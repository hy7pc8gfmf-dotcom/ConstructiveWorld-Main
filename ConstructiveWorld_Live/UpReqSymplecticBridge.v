(* ==========================================================================)
   UpReqSymplecticBridge.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：srs_rot_safe、srs_rot_characterization、srs_rot_pow、srs_qnpow、srs_rot_amp、srs_qnpow_one、srs_power_exact、srs_power_exact_gen、srs_power_rate。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import UpReqSpec2x2.
Require Import S02_CauchyComplete.

(* ================= §1 srs_rot_safe 族 ================= *)
Require Import S02_CauchyComplete.  (* 注：QleT'/QleT'_to_Qle/Qle_to_QleT' 家在 S02，S13 Require 不传递 Import —— 名对位补引 *)
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

Open Scope Q_scope.

Section SymplecticRotationSpec.

(* A. 主件 srs_rot_characterization：旋转的特征刻画                *)
(*   c²+s² == 1  ⟺  rot (c,s) 保范 ∧ 保辛（双向）                 *)

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

(* B. 幂与 n-速率（受体侧自证：rotⁿ 保范归纳是纯 nat 归纳）         *)

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

(* C. 支撑件：rotⁿ 闭式（cos/sin 倍角递推）+ 合成传递             *)

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

(* D. 供体接入：UpReqSpec2x2 sp2 速率引擎（/tmp 侧编通路）          *)
(*   把供体 Newton 开方率挂到旋转放大因子 D := c²+s² 上：            *)
(*   归一化旋转 (c/xₙ, s/xₙ)（xₙ := Newton 迭代）不放大范数          *)
(*   （D ≤ xₙ²），且残差 gapₙ·4ⁿ ≤ 3 指数收敛——旋转归一化速率。      *)

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

(* G4 审查留痕：出口件全表 Print Assumptions                       *)

Print Assumptions srs_rot_characterization.
Print Assumptions srs_power_exact.
Print Assumptions srs_power_exact_gen.
Print Assumptions srs_power_rate.
Print Assumptions srs_power_contract.
Print Assumptions srs_pow_closed.
Print Assumptions srs_pow_norm_transfer.
Print Assumptions srs_renorm_rate.
Print Assumptions srs_deficit_eq.
(* ================= §2 syb_qsq0_inv 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Open Scope Q_scope.

Section UpReqSymplecticBridge.

(* §0 内部支撑件                                                    *)

(* Q 层平方零消去（Qmult_integral 双支同形）。内部 Prop 位支撑件。 *)
Lemma syb_qsq0_inv : forall q : Q, (q * q == 0)%Q -> (q == 0)%Q.
Proof.
  intros q H. apply Qmult_integral in H. destruct H as [H | H]; exact H.
Qed.

(* 几何和：Σ_{k<n} q^k（步进式 = 前缀和 + q^k，配 1-qⁿ 因式分解）。 *)
Fixpoint syb_geomsum (n : nat) (q : Q) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S k => syb_geomsum k q + srs_qnpow k q
  end.

(* 几何和恒等式：1 − qⁿ == (1 − q)·Σ_{k<n} q^k。 *)
Theorem syb_geomsum_pow : forall (n : nat) (q : Q),
  QId (1 - srs_qnpow n q) ((1 - q) * syb_geomsum n q).
Proof.
  intros n. induction n as [| k IH]; intro q.
  - apply qid_intro. cbn [srs_qnpow syb_geomsum]. ring.
  - apply qid_intro.
    cbn [srs_qnpow syb_geomsum].
    assert (Hi : 1 - srs_qnpow k q
                 == (1 - q) * syb_geomsum k q)
      by exact (qid_elim _ _ (IH q)).
    assert (Hexp : (1 - q) * (syb_geomsum k q + srs_qnpow k q)
                   == (1 - q) * syb_geomsum k q + (1 - q) * srs_qnpow k q)
      by ring.
    rewrite Hexp, <- Hi. ring.
Qed.

(* q ≥ 0 ⟹ qⁿ ≥ 0（压缩档几何和正负性之支）。 *)
Lemma syb_qnpow_nn : forall (n : nat) (q : Q), Qle 0 q -> Qle 0 (srs_qnpow n q).
Proof.
  intros n. induction n as [| k IH]; intros q H0.
  - cbn [srs_qnpow]. exact sp2_qle_lit1.
  - cbn [srs_qnpow]. apply Qmult_le_0_compat; [exact H0 | exact (IH q H0)].
Qed.

(* q ≥ 0 ⟹ Σ_{k<n} q^k ≥ 0。 *)
Lemma syb_geomsum_nn : forall (n : nat) (q : Q), Qle 0 q -> Qle 0 (syb_geomsum n q).
Proof.
  intros n. induction n as [| k IH]; intros q H0.
  - cbn [syb_geomsum]. apply Qle_refl.
  - cbn [syb_geomsum].
    assert (Hs : Qle (0 + 0) (syb_geomsum k q + srs_qnpow k q)).
    { apply Qplus_le_compat; [exact (IH q H0) | exact (syb_qnpow_nn k q H0)]. }
    assert (Hz : (0 == 0 + 0)%Q) by ring.
    exact (sp2_qle_eq_l (0 + 0)%Q 0%Q
             (syb_geomsum k q + srs_qnpow k q)%Q Hz Hs).
Qed.

(* §1 G1 槽1：特征多项式恒等（Q 环层）+ Q 根强制退化                  *)

(* char-poly 恒等：rot(c,s)=[[c,-s],[s,c]] 的特征多项式在 t 处的值
   (t−c)²+s² 展开为 t²−2ct+(c²+s²)（迹 2c、行列式 c²+s²）。 *)
Theorem syb_charpoly : forall c s t : Q,
  QId ((t - c) * (t - c) + s * s) (t * t - 2 * (c * t) + (c * c + s * s)).
Proof.
  intros c s t. apply qid_intro. ring.
Qed.

(* 单位档（c²+s²==1）：char-poly == t²−2ct+1。 *)
Theorem syb_charpoly_unit : forall c s t : Q,
  QId (c * c + s * s) 1 ->
  QId ((t - c) * (t - c) + s * s) (t * t - 2 * (c * t) + 1).
Proof.
  intros c s t H.
  pose proof (qid_elim _ _ (syb_charpoly c s t)) as H1.
  apply qid_intro. rewrite H1, (qid_elim _ _ H). apply Qeq_refl.
Qed.

(* Q 根强制退化：char-poly 在 t 处取零 ⟹ t==c ∧ s==0。
   Δ<0 支的 Q 载体诚实形态：非退化旋转（s≠0）无 genuine Q 根——
   论证纯构造（两平方均非负 + 和为零 ⟹ 各自为零，Qle_antisym）。 *)
Theorem syb_root_forces_degenerate : forall c s t : Q,
  QId ((t - c) * (t - c) + s * s) 0 ->
  And (QId t c) (QId s 0).
Proof.
  intros c s t H.
  assert (Hq : (t - c) * (t - c) + s * s == 0) by exact (qid_elim _ _ H).
  assert (Ha : Qle 0 ((t - c) * (t - c))) by apply srs_qsq_nonneg.
  assert (Hb : Qle 0 (s * s)) by apply srs_qsq_nonneg.
  (* (t−c)² ≤ (t−c)²+s² == 0 ⟹ (t−c)² == 0 *)
  assert (Hale : Qle ((t - c) * (t - c)) ((t - c) * (t - c) + s * s))
    by exact (sp2_qle_plus_r _ _ Hb).
  assert (Ha0 : (t - c) * (t - c) == 0).
  { apply Qle_antisym.
    - exact (Qle_trans _ _ _ Hale (sp2_qeq_le _ _ Hq)).
    - exact Ha. }
  (* s² ≤ s²+(t−c)² == (t−c)²+s² == 0 ⟹ s² == 0 *)
  assert (Hble : Qle (s * s) (s * s + (t - c) * (t - c)))
    by exact (sp2_qle_plus_r _ _ Ha).
  assert (Hcomm : (s * s + (t - c) * (t - c))%Q
                  == ((t - c) * (t - c) + s * s)%Q) by ring.
  assert (Hb0 : s * s == 0).
  { apply Qle_antisym.
    - exact (Qle_trans _ _ _ Hble
               (sp2_qle_eq_l _ _ _ Hcomm (sp2_qeq_le _ _ Hq))).
    - exact Hb. }
  assert (Htc : t - c == 0).
  { apply Qmult_integral in Ha0. destruct Ha0 as [Hm1 | Hm2]; [exact Hm1 | exact Hm2]. }
  split; apply qid_intro.
  - assert (Ht : t == c + (t - c)) by ring.
    rewrite Htc, Qplus_0_r in Ht. exact Ht.
  - exact (syb_qsq0_inv s Hb0).
Qed.

(* §2 G1 槽2：保范/保辛在桥语句面的重述（对接 srs_rot_characterization）*)

Theorem syb_symplectic_isometry : forall c s : Q,
  QId (c * c + s * s) 1 ->
  And (forall p : (Q * Q)%type, QId (norms2 (rot c s p)) (norms2 p))
      (forall p q : (Q * Q)%type,
         QId (symp2 (rot c s p) (rot c s q)) (symp2 p q)).
Proof.
  intros c s H.
  destruct (srs_rot_characterization c s) as [Hfwd _].
  exact (Hfwd H).
Qed.

(*   （组合缝的精确刻画 + 障碍账定理化）                              *)

(* 一般 2×2 特征判别式恒等：(a+d)²−4(ad−bb′) == (a−d)²+4bb′。
   对称阵（b==b′）时退化为 sp2_qdisc 形 (a−d)²+4b²——sp2 槽的适用域
   恰为对称位。 *)
Theorem syb_chardisc_gen : forall a d b b' : Q,
  QId ((a + d) * (a + d) - 4 * (a * d - b * b'))
      ((a - d) * (a - d) + 4 * b * b').
Proof.
  intros a d b b'. apply qid_intro. ring.
Qed.

(* 旋转 rot(c,s) 的真特征判别式（(a−d)²+4bb′ 形在 a=d=c,b=−s,b′=s）：
   == −4s² ≤ 0——负判别式支的具体载体。 *)
Theorem syb_chardisc_rot : forall c s : Q,
  QId ((c - c) * (c - c) + 4 * (- s) * s) (-4 * (s * s)).
Proof.
  intros c s. apply qid_intro. ring.
Qed.

(* sp2 对称槽在旋转阵位（c,c,−s）的槽值：== 4s² ≥ 0。 *)
Theorem syb_qdisc_slot_rot : forall c s : Q,
  QId (sp2_qdisc c c (- s)) (4 * (s * s)).
Proof.
  intros c s. apply qid_intro. unfold sp2_qdisc. ring.
Qed.

(* 障碍账定理化：若对称参数位值 == 真特征判别式，则 s == 0。
   即 sp2_qdisc 槽恰在退化旋转处才看见旋转的特征判别式；
   Δ<0 支（s≠0）被对称槽结构性遮蔽——组合缝的精确定理化。 *)
Theorem syb_slot_agree : forall c s : Q,
  QId (sp2_qdisc c c (- s)) ((c - c) * (c - c) + 4 * (- s) * s) ->
  QId s 0.
Proof.
  intros c s H.
  assert (Hq : sp2_qdisc c c (- s) == (c - c) * (c - c) + 4 * (- s) * s)
    by exact (qid_elim _ _ H).
  assert (Hz : (sp2_qdisc c c (- s)
                - ((c - c) * (c - c) + 4 * (- s) * s))%Q == 0).
  { rewrite Hq. ring. }
  unfold sp2_qdisc in Hz.
  (* 槽差 == 8s²（恒等）；差为零 ⟹ 8s² == 0 ⟹ s² == 0 ⟹ s == 0 *)
  assert (H8 : (8 * (s * s))%Q == 0).
  { apply (Qeq_trans (8 * (s * s))%Q
             (((c - c) * (c - c) + 4 * - s * - s)
              - ((c - c) * (c - c) + 4 * - s * s))%Q 0%Q).
    - ring.
    - exact Hz. }
  assert (Hm : ((1#8) * (8 * (s * s)))%Q == 0).
  { rewrite H8. apply Qmult_0_r. }
  assert (Has : ((1#8) * (8 * (s * s)))%Q == (((1#8) * 8) * (s * s))%Q)
    by ring.
  rewrite Has in Hm.
  assert (Hunit : (((1#8) * 8)%Q) == 1) by reflexivity.
  rewrite Hunit, Qmult_1_l in Hm.
  apply qid_intro. exact (syb_qsq0_inv s Hm).
Qed.

(* 负判别式支非负性假言 ⟹ 退化：把「真特征判别式 ≥ 0」当假言，
   在 Q 有序域上构造性推出 s == 0（4s² ≥ 0 与 −4s² ≥ 0 夹逼）。
   这是 sp2_eig_gap 的 real_le 前提在旋转载体上取等的唯一路径。 *)
Theorem syb_negdisc_degenerate : forall c s : Q,
  QleT' 0 ((c - c) * (c - c) + 4 * (- s) * s) ->
  QId s 0.
Proof.
  intros c s H.
  assert (Hq : Qle 0 ((c - c) * (c - c) + 4 * (- s) * s))
    by (apply QleT'_to_Qle; exact H).
  assert (H0 : (4 * (- s) * s == (c - c) * (c - c) + 4 * (- s) * s)%Q)
    by ring.
  assert (Hg : Qle 0 (4 * (- s) * s)) by exact (sp2_qle_eq_r _ _ _ H0 Hq).
  assert (Hpos : Qle 0 (4 * (s * s))).
  { assert (Hid : (4 * (s * s) == (2 * s) * (2 * s))%Q) by ring.
    exact (sp2_qle_eq_r 0%Q ((2 * s) * (2 * s))%Q (4 * (s * s))%Q Hid
             (srs_qsq_nonneg (2 * s)%Q)). }
  assert (Hid2 : (4 * (- s) * s == - (4 * (s * s)))%Q) by ring.
  assert (Ho : Qle (- (4 * (s * s))) (- 0))
    by exact (Qopp_le_compat _ _ Hpos).
  assert (Hflip0 : Qle (4 * (- s) * s) (- 0))
    by exact (sp2_qle_eq_l (-(4 * (s * s)))%Q (4 * (- s) * s)%Q
               (- 0)%Q Hid2 Ho).
  assert (Hn0 : (- 0)%Q == 0) by ring.
  assert (Hflip : Qle (4 * (- s) * s) 0)
    by exact (sp2_qle_eq_r _ _ _ Hn0 Hflip0).
  assert (Hza : (4 * (- s) * s == 0)%Q)
    by (apply Qle_antisym; [exact Hflip | exact Hg]).
  (* 纯 Qeq 链回负化：4s² == 0（零 Prop 消除——Set 目标位红线） *)
  assert (Hneg : (- (4 * (s * s)))%Q == 0)
    by exact (Qeq_trans _ _ _ (Qeq_sym _ _ Hid2) Hza).
  assert (H4 : (4 * (s * s))%Q == 0).
  { pose proof (Qopp_involutive (4 * (s * s))%Q) as Hi.
    rewrite Hneg in Hi.
    assert (Hn0b : (- 0)%Q == 0) by ring.
    rewrite Hn0b in Hi. exact (Qeq_sym _ _ Hi). }
  (* (1#4) 乘法链：4s² == 0 ⟹ s² == 0 ⟹ s == 0 *)
  assert (Hm : ((1#4) * (4 * (s * s)))%Q == 0).
  { rewrite H4. apply Qmult_0_r. }
  assert (Has : ((1#4) * (4 * (s * s)))%Q == (((1#4) * 4) * (s * s))%Q)
    by ring.
  rewrite Has in Hm.
  assert (Hunit : (((1#4) * 4)%Q) == 1) by reflexivity.
  rewrite Hunit, Qmult_1_l in Hm.
  apply qid_intro. exact (syb_qsq0_inv s Hm).
Qed.

(* §4 G2 槽3：速率对接——单步亏损恒等式（qgap 槽）                     *)

(* 单步亏损恒等式：‖rot p‖² == ‖p‖² − qgap(c²+s², 1)·‖p‖²。
   srs_rot_amp（放大因子 D·‖p‖²）与 sp2_qgap（1−D）的真组合：
   亏损恰为单位点处的谱隙 × 范数。 *)
Theorem syb_rot_qgap_defect : forall (c s : Q) (p : (Q * Q)%type),
  QId (norms2 (rot c s p))
      (norms2 p - sp2_qgap (c * c + s * s) 1 * norms2 p).
Proof.
  intros c s p.
  assert (Hamp : norms2 (rot c s p) == (c * c + s * s) * norms2 p)
    by exact (srs_rot_amp c s p).
  apply qid_intro. unfold sp2_qgap. rewrite Hamp. ring.
Qed.

(* n 步亏损恒等式：‖rotⁿ p‖² == ‖p‖² − qgap·geomsum_n·‖p‖²。
   srs_power_exact（(c²+s²)ⁿ 速率律）× syb_geomsum_pow（几何和）
   的真组合——G3 幂速率对接主件。 *)
Theorem syb_power_qgap_defect : forall (n : nat) (c s : Q) (p : (Q * Q)%type),
  QId (norms2 (srs_rot_pow n c s p))
      (norms2 p - sp2_qgap (c * c + s * s) 1
                   * syb_geomsum n (c * c + s * s) * norms2 p).
Proof.
  intros n c s p.
  assert (Hex : norms2 (srs_rot_pow n c s p)
                == srs_qnpow n (c * c + s * s) * norms2 p)
    by exact (qid_elim _ _ (srs_power_exact n c s p)).
  assert (Hg : 1 - srs_qnpow n (c * c + s * s)
               == (1 - (c * c + s * s)) * syb_geomsum n (c * c + s * s))
    by exact (qid_elim _ _ (syb_geomsum_pow n (c * c + s * s))).
  apply qid_intro. unfold sp2_qgap.
  rewrite Hex, Qmult_1_l, <- Hg. ring.
Qed.

(* 等距的 qgap 参数位复原：c²+s²==1 ⟹ qgap 归零 ⟹ 亏损恒等式退化回
   srs_power_rate——桥的双向忠实性验证（经 sp2_qgap 槽，非直抄）。 *)
Theorem syb_power_isometry_via_qgap : forall (n : nat) (c s : Q)
    (p : (Q * Q)%type),
  QId (c * c + s * s) 1 ->
  QId (norms2 (srs_rot_pow n c s p)) (norms2 p).
Proof.
  intros n c s p H.
  assert (Hz : sp2_qgap (c * c + s * s) 1 == 0).
  { unfold sp2_qgap. rewrite (qid_elim _ _ H). ring. }
  pose proof (qid_elim _ _ (syb_power_qgap_defect n c s p)) as Hd.
  rewrite Hz in Hd.
  repeat rewrite Qmult_0_l in Hd.
  rewrite sp2_qminus_0_r in Hd.
  apply qid_intro. exact Hd.
Qed.

(* 压缩档对接：0 ≤ q ≤ 1（q := c²+s²）⟹ 亏损 ≥ 0——
   srs_power_contract 前提组的 sp2_qgap 槽重述（QleT' 入口、出口）。 *)
Theorem syb_contract_defect_nonneg : forall (n : nat) (c s : Q)
    (p : (Q * Q)%type),
  QleT' (c * c + s * s) 1 -> QleT' 0 (c * c + s * s) ->
  QleT' 0 (sp2_qgap (c * c + s * s) 1
           * syb_geomsum n (c * c + s * s) * norms2 p).
Proof.
  intros n c s p H1 H0.
  assert (Hq1 : Qle (c * c + s * s) 1) by (apply QleT'_to_Qle; exact H1).
  assert (Hq0 : Qle 0 (c * c + s * s)) by (apply QleT'_to_Qle; exact H0).
  assert (Hu : (1 * 1)%Q == 1) by reflexivity.
  assert (Hle : Qle (c * c + s * s) (1 * 1))
    by exact (sp2_qle_eq_r _ _ _ Hu Hq1).
  assert (Hgap : Qle 0 (sp2_qgap (c * c + s * s) 1))
    by exact (sp2_qgap_ge0 _ _ Hle).
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; [exact Hgap | exact (syb_geomsum_nn n (c * c + s * s) Hq0)].
  - exact (srs_norms2_nonneg p).
Qed.

(* §5 桥接闭合件：三槽逐一核验的 And 桥                              *)

Theorem syb_spec_bridge : forall c s t : Q,
  And (* 参数位1 特征方程：char-poly 恒等（Q 环层） *)
      (QId ((t - c) * (t - c) + s * s)
           (t * t - 2 * (c * t) + (c * c + s * s)))
      (And (* 参数位2 判别式：sp2 对称参数位值 / 旋转真判别式 / 障碍账重合定理 *)
        (And (QId (sp2_qdisc c c (- s)) (4 * (s * s)))
             (And (QId ((c - c) * (c - c) + 4 * (- s) * s) (-4 * (s * s)))
                  (QId (sp2_qdisc c c (- s))
                       ((c - c) * (c - c) + 4 * (- s) * s) -> QId s 0)))
        (* 槽3 速率：单步亏损恒等式（sp2_qgap 槽对接） *)
        (forall p : (Q * Q)%type,
           QId (norms2 (rot c s p))
               (norms2 p - sp2_qgap (c * c + s * s) 1 * norms2 p))).
Proof.
  intros c s t. split.
  - exact (syb_charpoly c s t).
  - split.
    + split.
      * exact (syb_qdisc_slot_rot c s).
      * split.
        -- exact (syb_chardisc_rot c s).
        -- exact (syb_slot_agree c s).
    + exact (syb_rot_qgap_defect c s).
Qed.

End UpReqSymplecticBridge.

(* 审查留痕：出口件全表 Print Assumptions                             *)

Print Assumptions syb_charpoly.
Print Assumptions syb_charpoly_unit.
Print Assumptions syb_root_forces_degenerate.
Print Assumptions syb_symplectic_isometry.
Print Assumptions syb_chardisc_gen.
Print Assumptions syb_chardisc_rot.
Print Assumptions syb_qdisc_slot_rot.
Print Assumptions syb_slot_agree.
Print Assumptions syb_negdisc_degenerate.
Print Assumptions syb_rot_qgap_defect.
Print Assumptions syb_geomsum_pow.
Print Assumptions syb_power_qgap_defect.
Print Assumptions syb_power_isometry_via_qgap.
Print Assumptions syb_contract_defect_nonneg.
Print Assumptions syb_spec_bridge.
