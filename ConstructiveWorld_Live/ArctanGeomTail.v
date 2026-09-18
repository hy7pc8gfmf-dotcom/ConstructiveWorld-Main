(* ================================================================== *)
(*  ArctanGeomTail.v —— 席位 C3（arctan 几何尾封口，20260916）          *)
(*                                                                    *)
(*  使命：现库 arctan 尾界只有调和级慢界 atan_tail_bound_le            *)
(*        （≤ 1/(2m+3)，S11）；本件把几何信息（单步比值恒等式          *)
(*        atan_mag_succ_geom）真正用起来，封口为几何尾界：             *)
(*                                                                    *)
(*    atg_tail_geom : |x| < 1（QltT 严格）⟹ m ≤ n ⟹                    *)
(*        |S_n − S_m| ≤ c_{m+1} · 1/(1−x²)                            *)
(*                                                                    *)
(*    其中 c_k := atan_mag k x = |x|^{2k+1}/(2k+1)，r := x·x。          *)
(*    （任务书的 (1 # (1−x*x)) 为 Z-字面写法、对 x:Q 不合型；           *)
(*      实测封口取其有理数形 1/(1−x*x)（Qdiv）。）                     *)
(*                                                                    *)
(*  模板对照坐标：                                                     *)
(*    atan_mag_succ_geom @S11_TP3B5  单步比值恒等式（本件引擎一）       *)
(*    atan_sq_le_one     @S11_TP3B5  |x|≤1 ⟹ x²≤1（主件入帮）          *)
(*    atan_pow_le_one    @S11_TP3B5  0≤y≤1 ⟹ y^p≤1（备用件，本件未引用） *)
(*    arctan_term_abs    @S11_TP3B5  |t_k| == c_k（主链入帮）           *)
(*    atan_mag_nonneg    @S11_TP3B5  c_k ≥ 0（收官入帮）               *)
(*    geo_sum_closed     @S03_QExp    几何和闭式模板（1/2 基泛化为      *)
(*                                    任意基 r：atg_geo_fin_closed）    *)
(*    q_le_div_le        @S03_QExp    分式保序                         *)
(*    sc_qmult_le_l      @S10_KVQuantTrig 左乘保序（项序手动归一）      *)
(*    qltT_*/qleT'_*     @S02_CauchyComplete QltT/QleT' 载体件          *)
(*                                                                    *)
(*  支撑件（本件新建，≥2）：                                            *)
(*    atg_mag_ratio       单步比值控制：c_{k+1} ≤ r·c_k（r ≥ 0 即可）   *)
(*    atg_mag_pow         比值迭代：c_{m+j} ≤ r^j·c_m                   *)
(*    atg_geo_fin_closed  任意基几何和闭式：g_d·(1−r) == 1−r^d          *)
(*    atg_geo_fin_le_div  几何和尾界：0≤r ∧ 0<1−r ⟹ g_d ≤ 1/(1−r)       *)
(*    atg_tail_aux        三角+几何和主链：|S_{m+d}−S_m| ≤ c_{m+1}·g_d  *)
(*                                                                    *)
(*  非平凡性声明：真几何比值链（ratio → 迭代 → 几何和闭式 → 分式尾界）， *)
(*  不借道 Leibniz 慢界 atan_tail_bound/atan_tail_bound_le。            *)
(*  全 Q 层，公理面零假设（零公理类禁词），出口 QleT'，零极限。          *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.

(* ============================================================ *)
(*  一、归一化辅助（Qdiv/Qopp 项序手动归一，防 ring 树序坑）      *)
(* ============================================================ *)

(* ---- |x|·|x| == x·x（Qabs 平方消去；本版 stdlib 无 Qabs_eq，    ---- *)
(* ---- 改走 Qabs_pos/Qabs_neg 按 x 符号分档）                      ---- *)
Lemma atg_sq_abs : forall x : Q, Qabs x * Qabs x == x * x.
Proof.
  intro x.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hnonpos].
  - rewrite Qabs_pos by (apply Qlt_le_weak; exact Hpos). reflexivity.
  - rewrite Qabs_neg by exact Hnonpos. ring.
Qed.

(* ---- 0 < 1（字面） ---- *)
Lemma atg_0_lt_1 : Qlt 0 1.
Proof. unfold Qlt; simpl; lia. Qed.

(* ---- y < 1 ⟹ 0 < 1 − y（Qopp 项序：经 −y+y / −y+1 归一） ---- *)
Lemma atg_one_minus_pos : forall y : Q, Qlt y 1 -> Qlt 0 (1 - y).
Proof.
  intros y Hy.
  apply QltT_to_Qlt.
  assert (Ht : QltT ((- y)%Q + y) ((- y)%Q + 1)).
  { apply (qleT'_plus_ltT_ltT ((- y)%Q) ((- y)%Q) y 1).
    - apply qleT'_refl.
    - apply Qlt_to_QltT. exact Hy. }
  assert (E1 : (- y)%Q + y == 0) by ring.
  assert (E2 : (1 - y)%Q == (- y)%Q + 1) by ring.
  exact (qltT_eq_compat_l ((- y)%Q + y) 0 (1 - y)%Q E1
           (qltT_eq_compat_r (1 - y)%Q ((- y)%Q + 1) ((- y)%Q + y) E2 Ht)).
Qed.

(* ---- |x| < 1 ⟹ x² < 1 ---- *)
Lemma atg_absx_sq_lt : forall x : Q, Qlt (Qabs x) 1 -> Qlt (x * x) 1.
Proof.
  intros x Hx.
  assert (Ha : Qle 0 (Qabs x)) by apply Qabs_nonneg.
  destruct (Qle_lt_or_eq 0 (Qabs x) Ha) as [Hpos | Hzero].
  - (* 0 < |x| < 1：|x|² < 1·|x| < 1·1 *)
    apply QltT_to_Qlt.
    assert (Ht1 : QltT (Qabs x * Qabs x) (1 * Qabs x)).
    { apply (qltT_mult_ltT_compat_r (Qabs x) 1 (Qabs x)).
      - apply Qlt_to_QltT. exact Hpos.
      - apply Qlt_to_QltT. exact Hx. }
    assert (Ht2 : QltT (Qabs x * 1) (1 * 1)).
    { apply (qltT_mult_ltT_compat_r (Qabs x) 1 1).
      - apply Qlt_to_QltT. exact atg_0_lt_1.
      - apply Qlt_to_QltT. exact Hx. }
    assert (E12 : Qabs x * 1 == 1 * Qabs x) by ring.
    assert (Ht3 : QltT (Qabs x * Qabs x) (1 * 1)).
    { apply (qleT'_ltT_ltT (Qabs x * Qabs x) (Qabs x * 1) (1 * 1)).
      - apply qltT_leT'.
        exact (qltT_eq_compat_r (Qabs x * 1) (1 * Qabs x)
                                (Qabs x * Qabs x) E12 Ht1).
      - exact Ht2. }
    apply (qltT_eq_compat_l (Qabs x * Qabs x) (x * x) 1).
    + exact (atg_sq_abs x).
    + apply (qltT_eq_compat_r (1 * 1) 1 (Qabs x * Qabs x)).
      * ring.
      * exact Ht3.
  - (* |x| = 0：x² == 0 < 1 *)
    apply QltT_to_Qlt.
    assert (E0 : 0 == x * x).
    { rewrite <- atg_sq_abs. rewrite <- Hzero. ring. }
    apply (qltT_eq_compat_l 0 (x * x) 1).
    + exact E0.
    + apply Qlt_to_QltT. exact atg_0_lt_1.
Qed.

(* ============================================================ *)
(*  二、单调比值控制（支撑件一；引擎：atan_mag_succ_geom）        *)
(* ============================================================ *)

(* ---- 单步比值：c_{k+1} ≤ r·c_k（r := x² ≥ 0 即可，无需 r ≤ 1） ---- *)
Lemma atg_mag_ratio : forall (x : Q) (k : nat), Qle 0 (x * x) ->
  Qle (atan_mag (Datatypes.S k) x) (x * x * atan_mag k x).
Proof.
  intros x k Hr0.
  rewrite (atan_mag_succ_geom x k).
  unfold atan_mag.
  assert (Ediv : x * x * (q_pow (Qabs x) (2 * k + 1) / (Z.of_nat (2 * k + 1) # 1)) ==
                 (x * x * q_pow (Qabs x) (2 * k + 1)) / (Z.of_nat (2 * k + 1) # 1))
    by (unfold Qdiv; ring).
  rewrite Ediv.
  apply (q_le_div_le ((Qabs x * Qabs x) * q_pow (Qabs x) (2 * k + 1))
                     (Z.of_nat (2 * k + 3) # 1)
                     (x * x * q_pow (Qabs x) (2 * k + 1))
                     (Z.of_nat (2 * k + 1) # 1)).
  - unfold Qlt; simpl; lia.
  - unfold Qlt; simpl; lia.
  - (* (a²·A)·d1 ≤ (x²·A)·d2，A := q_pow (Qabs x) (2k+1) ≥ 0 *)
    apply (Qle_trans _ ((x * x * q_pow (Qabs x) (2 * k + 1)) *
                        (Z.of_nat (2 * k + 1) # 1)) _).
    + rewrite atg_sq_abs. apply Qle_refl.
    + apply (sc_qmult_le_l (Z.of_nat (2 * k + 1) # 1)
                           (Z.of_nat (2 * k + 3) # 1)
                           (x * x * q_pow (Qabs x) (2 * k + 1))).
      * unfold Qle; simpl; lia.
      * apply Qmult_le_0_compat.
        -- exact Hr0.
        -- apply q_pow_nonneg. apply Qabs_nonneg.
Qed.

(* ---- 比值迭代：c_{m+j} ≤ r^j·c_m ---- *)
Lemma atg_mag_pow : forall (x : Q) (m j : nat), Qle 0 (x * x) ->
  Qle (atan_mag ((m + j)%nat) x) (q_pow (x * x) j * atan_mag m x).
Proof.
  intros x m j Hr0.
  induction j as [| j IH].
  - replace ((m + 0)%nat) with m by lia.
    replace (q_pow (x * x) 0%nat) with 1 by reflexivity.
    apply qeq_le. ring.
  - replace ((m + Datatypes.S j)%nat) with (Datatypes.S ((m + j)%nat)) by lia.
    rewrite q_pow_succ.
    apply (Qle_trans _ ((x * x) * atan_mag ((m + j)%nat) x) _).
    + apply atg_mag_ratio. exact Hr0.
    + apply (Qle_trans _ ((x * x) * (q_pow (x * x) j * atan_mag m x)) _).
      * apply (sc_qmult_le_l (atan_mag ((m + j)%nat) x)
                             (q_pow (x * x) j * atan_mag m x) (x * x)).
        -- exact IH.
        -- exact Hr0.
      * apply qeq_le. ring.
Qed.

(* ============================================================ *)
(*  三、任意基几何和：闭式 + 尾界（支撑件二；geo_sum_closed 泛化） *)
(* ============================================================ *)

Fixpoint atg_geo_fin (r : Q) (d : nat) : Q :=
  match d with
  | 0%nat => 0
  | Datatypes.S e => atg_geo_fin r e + q_pow r e
  end.

(* ---- 闭式：g_d·(1−r) == 1−r^d ---- *)
Lemma atg_geo_fin_closed : forall (r : Q) (d : nat),
  atg_geo_fin r d * (1 - r) == 1 - q_pow r d.
Proof.
  intros r d.
  induction d as [| d IH].
  - replace (q_pow r 0%nat) with 1 by reflexivity.
    replace (atg_geo_fin r 0%nat) with 0 by reflexivity.
    ring.
  - change (atg_geo_fin r (Datatypes.S d) * (1 - r))
      with ((atg_geo_fin r d + q_pow r d) * (1 - r)).
    assert (Hd : (atg_geo_fin r d + q_pow r d) * (1 - r) ==
                 atg_geo_fin r d * (1 - r) + q_pow r d * (1 - r)) by ring.
    rewrite Hd.
    rewrite IH.
    rewrite q_pow_succ.
    ring.
Qed.

(* ---- 几何和尾界：0 ≤ r ∧ 0 < 1−r ⟹ g_d ≤ 1/(1−r) ---- *)
Lemma atg_geo_fin_le_div : forall (r : Q) (d : nat), Qle 0 r -> Qlt 0 (1 - r) ->
  Qle (atg_geo_fin r d) (1 / (1 - r)).
Proof.
  intros r d Hr0 Hr1pos.
  assert (Hinv : Qinv 1 == 1) by reflexivity.
  assert (Hdiv1 : atg_geo_fin r d / 1 == atg_geo_fin r d).
  { unfold Qdiv. rewrite Hinv. apply Qmult_1_r. }
  apply (Qle_trans _ (atg_geo_fin r d / 1) _).
  - apply qeq_le.
    exact (Qeq_sym (atg_geo_fin r d / 1) (atg_geo_fin r d) Hdiv1).
  - apply (q_le_div_le (atg_geo_fin r d) 1 1 (1 - r)).
    + exact atg_0_lt_1.
    + exact Hr1pos.
    + apply (Qle_trans _ (1 - q_pow r d) _).
      * apply qeq_le. apply atg_geo_fin_closed.
      * apply (Qle_trans _ (1 - q_pow r d + q_pow r d) _).
        -- apply Qle_plus_nonneg_r. apply q_pow_nonneg. exact Hr0.
        -- apply qeq_le. ring.
Qed.

(* ============================================================ *)
(*  四、三角+几何和主链（支撑件三；引擎：arctan_term_abs）        *)
(* ============================================================ *)

Lemma atg_tail_aux : forall (x : Q) (m d : nat), Qle 0 (x * x) ->
  Qle (Qabs (arctan_partial ((m + d)%nat) x - arctan_partial m x))
      (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d).
Proof.
  intros x m d Hr0.
  induction d as [| d IH].
  - (* d = 0：|S_m − S_m| = 0 ≤ c_{m+1}·0 *)
    replace ((m + 0)%nat) with m by lia.
    replace (atg_geo_fin (x * x) 0%nat) with 0 by reflexivity.
    apply (Qle_trans _ 0 _).
    + apply qeq_le.
      assert (Hz : arctan_partial m x - arctan_partial m x == 0) by ring.
      rewrite Hz. reflexivity.
    + apply qeq_le. ring.
  - (* d → S d：三角不等式 + 比值迭代 + 几何和一步 *)
    replace ((m + Datatypes.S d)%nat) with (Datatypes.S ((m + d)%nat)) by lia.
    assert (Hstep : arctan_partial (Datatypes.S ((m + d)%nat)) x ==
                    arctan_partial ((m + d)%nat) x +
                    arctan_term (Datatypes.S ((m + d)%nat)) x) by reflexivity.
    rewrite Hstep.
    setoid_replace ((arctan_partial ((m + d)%nat) x +
                     arctan_term (Datatypes.S ((m + d)%nat)) x) - arctan_partial m x)
      with ((arctan_partial ((m + d)%nat) x - arctan_partial m x) +
            arctan_term (Datatypes.S ((m + d)%nat)) x) by ring.
    apply (Qle_trans _ (Qabs (arctan_partial ((m + d)%nat) x - arctan_partial m x) +
                        Qabs (arctan_term (Datatypes.S ((m + d)%nat)) x)) _).
    + apply Qabs_triangle.
    + assert (Hp : Qle (atan_mag (Datatypes.S ((m + d)%nat)) x)
                       (q_pow (x * x) d * atan_mag (Datatypes.S m) x)).
      { replace (Datatypes.S ((m + d)%nat)) with (Datatypes.S m + d)%nat by lia.
        apply atg_mag_pow. exact Hr0. }
      apply (Qle_trans _ (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d +
                          atan_mag (Datatypes.S ((m + d)%nat)) x) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- apply qeq_le. apply arctan_term_abs.
      * apply (Qle_trans _ (atan_mag (Datatypes.S m) x * atg_geo_fin (x * x) d +
                            q_pow (x * x) d * atan_mag (Datatypes.S m) x) _).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ exact Hp.
        -- replace (atg_geo_fin (x * x) (Datatypes.S d))
             with (atg_geo_fin (x * x) d + q_pow (x * x) d) by reflexivity.
           apply qeq_le. ring.
Qed.

(* ============================================================ *)
(*  五、主件：几何尾界（A5 席数值果 2 封口；QltT 进 / QleT' 出）   *)
(* ============================================================ *)

Lemma atg_tail_geom : forall (x : Q) (m n : nat), QltT (Qabs x) 1 -> (m <= n)%nat ->
  QleT' (Qabs (arctan_partial n x - arctan_partial m x))
        (atan_mag (Datatypes.S m) x * (1 / (1 - x * x))).
Proof.
  intros x m n Hx Hmn.
  apply Qle_to_QleT'.
  assert (Hsq : Qle (x * x) 1) by (apply atan_sq_le_one; apply qltT_leT'; exact Hx).
  assert (Hr0 : Qle 0 (x * x)) by apply Qsquare_nonneg.
  assert (Hlt : Qlt (x * x) 1) by (apply atg_absx_sq_lt; apply QltT_to_Qlt; exact Hx).
  assert (Hr1 : Qlt 0 (1 - x * x)) by (apply atg_one_minus_pos; exact Hlt).
  apply (Qle_trans _ (atan_mag (Datatypes.S m) x *
                      atg_geo_fin (x * x) (n - m)%nat) _).
  - (* 主链：|S_n − S_m| ≤ c_{m+1}·g_{n−m} *)
    remember (n - m)%nat as d eqn:Ed.
    assert (E : (m + d)%nat = n) by lia.
    rewrite <- E.
    apply atg_tail_aux. exact Hr0.
  - (* 几何和尾界收官：g_{n−m} ≤ 1/(1−r) ⟹ c_{m+1}·g ≤ c_{m+1}/(1−r) *)
    apply (sc_qmult_le_l (atg_geo_fin (x * x) (n - m)%nat) (1 / (1 - x * x))
                         (atan_mag (Datatypes.S m) x)).
    + apply (atg_geo_fin_le_div (x * x) (n - m)%nat Hr0 Hr1).
    + apply atan_mag_nonneg.
Qed.

(* ============================================================ *)
(*  六、审计口（G4）：Print Assumptions                           *)
(* ============================================================ *)

Print Assumptions atg_tail_geom.
Print Assumptions atg_tail_aux.
Print Assumptions atg_mag_ratio.
Print Assumptions atg_mag_pow.
Print Assumptions atg_geo_fin_closed.
Print Assumptions atg_geo_fin_le_div.
