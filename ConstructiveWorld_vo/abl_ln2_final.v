(* ===================================================================== *)
(*  abl_ln2_final.v —— ln2 有理逼近分离定理·全链装配件                        *)
(*  模块名：abl_ln2_final。                                                *)
(*  数学使命：把 θⁿ 预算、卷积带窗、规范分子对、供给接口与无理性判据组成的     *)
(*        完整分离链装配为最终语句，三件主定理：                            *)
(*        ① lnt5_uniform_separation：在五肢供给接口成立时，对每个分母 v      *)
(*        显式构造仅依赖 v 的正分离函数 f：中支常数 (clo_{n₀}/2)·|A_{n₀}|⁻¹  *)
(*        与否支常数 ((1/v − (4/5)^{n₀})/2)·|A_{n₀}|⁻¹ 的 Qcompare 极小值，  *)
(*        其中 n₀ := 8·⌊v⌋ 为闭式窗指标，使 |u/v − x_k| ≥ f(v) 对一切整数    *)
(*        u 与一切 k ≥ K 成立（常数对分子一致化是本件新增组合步）；           *)
(*        ② lnt5_bound_final：分离引擎结论面沿供给投影件的转写；             *)
(*        ③ lnt5_irrational_final 与 lnt5_irrational_ireal_face：经供给      *)
(*        重排件接入无理性判据，得到 ln2 与每个有理数 q 的显式正距离          *)
(*        （real_lt 面，即 ln2 ≠ q 的 Set 层语句形）；并证明两处 ln2 的      *)
(*        柯西极限名（ln2b_X 与 ri_real）实现同一实数，其上的线对象亦同。     *)
(*  依赖清单：Stdlib QArith/Qabs/Arith/ZArith/Lia；S01_BaseRing             *)
(*        S02_CauchyComplete S03_QExp；UpReqLn2Irrational                   *)
(*        UpReqIrrationalCriterion RealIdentity Ln2Bridge；同链前序模块      *)
(*        abl_ln2_theta_total / abl_ln2_assembly / abl_ln2_ireal /          *)
(*        abl_ln2_conv_core / abl_ln2_conv_mesh。                           *)
(*  对标行：Ln2Bridge ln2b_delta_of_supply 的逐点分离常数提取形；本件增量：    *)
(*        分离常数对分子一致化（Qcompare 极小值构造）、窗指标闭式化           *)
(*        n₀ := 8·⌊v⌋（取自 conv_core 的带窗件 cc_band_v）、供给面单前提化    *)
(*        （cm_pade_supply 经重排件直连无理性判据）、柯西极限名实现            *)
(*        同一实数的同一性证明。                                          *)
(*  构造性注记：纯构造性、零承认件；交付语句面全 Set（sigT/S01.And/QeqT/      *)
(*        QleT'/QltT/real_lt/real_eq），分离常数与窗指标全显式封闭项；        *)
(*        Qeq/Qle/Qlt 仅 Prop 推理面作脚手架；整数分叉走 Z.eq_dec，           *)
(*        常数比较走 Qcompare（零 LPO）。                                   *)
(*  诚实面：代数恒等式 Σ_k bterm = q̃_n·ln2 − p_n 为链上在办事项：三件主      *)
(*        定理均以 cm_pade_supply 为唯一开放前提（其见证函数携带下上界对     *)
(*        与下界列 clo），该恒等式到货后各语句无需修改即得无条件形；          *)
(*        本件零新增开放前提。中支常数含 clo 在 n₀ 的取值，故 f 的全显式      *)
(*        数值形随到货见证而定；否支常数已全闭式。                           *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no            *)
(*        -Q vo_local_world_unified_0930 "" 本件（同链前序五模块先行，       *)
(*        单道串行）。                                                     *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqLn2Irrational UpReqIrrationalCriterion RealIdentity Ln2Bridge.
Require Import abl_ln2_theta_total abl_ln2_assembly abl_ln2_ireal
  abl_ln2_conv_core abl_ln2_conv_mesh.

Open Scope nat_scope.

(* ============================================================ *)
(* §A 有理数二元极小（Qcompare 三分承载，Set 层可提取）                      *)
(* ============================================================ *)

(* 按 Qcompare 选取较小者：Gt 取 b，其余取 a *)
Definition lnt5_qmin (a b : Q) : Q :=
  match Qcompare a b with
  | Gt => b
  | _ => a
  end.

(* 极小值不超过左元 *)
Lemma lnt5_qmin_le_l : forall a b : Q, Qle (lnt5_qmin a b) a.
Proof.
  intros a b. unfold lnt5_qmin.
  destruct (Qcompare a b) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply QleT'_to_Qle. unfold QleT', Qle_bool.
    rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity.
Qed.

(* 极小值不超过右元 *)
Lemma lnt5_qmin_le_r : forall a b : Q, Qle (lnt5_qmin a b) b.
Proof.
  intros a b. unfold lnt5_qmin.
  destruct (Qcompare a b) eqn:E.
  - apply QleT'_to_Qle. unfold QleT', Qle_bool. rewrite E. reflexivity.
  - apply QleT'_to_Qle. unfold QleT', Qle_bool. rewrite E. reflexivity.
  - apply Qle_refl.
Qed.

(* 两元皆正则极小值正 *)
Lemma lnt5_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (lnt5_qmin a b).
Proof.
  intros a b Ha Hb. unfold lnt5_qmin. destruct (Qcompare a b).
  - exact Ha.
  - exact Ha.
  - exact Hb.
Qed.

(* ============================================================ *)
(* §B 显式分离常数（闭式数据；n₀ := 8·⌊v⌋ 为带窗指标）                      *)
(* ============================================================ *)

(* 带窗指标：n₀ v := 8·⌊v⌋（正整数 v 的地板由 Z.to_nat 承载） *)
Definition lnt5_n0 (v : positive) : nat := 8 * Z.to_nat (Z.pos v).

(* 中支常数：(clo_{n₀}/2)·|A_{n₀}|⁻¹（clo 由供给接口见证函数给出） *)
Definition lnt5_c1 (clo : nat -> Q) (v : positive) : Q :=
  ((clo (lnt5_n0 v)) * (1 # 2)%Q) * Qinv (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q).

(* 否支常数：((1/v − (4/5)^{n₀})/2)·|A_{n₀}|⁻¹（全闭式，仅依赖 v） *)
Definition lnt5_c2 (v : positive) : Q :=
  (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)
    * Qinv (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q).

(* 逐分母分离函数：两支常数的极小值 *)
Definition lnt5_f (clo : nat -> Q) (v : positive) : Q :=
  lnt5_qmin (lnt5_c1 clo v) (lnt5_c2 v).

(* 中支常数正性：clo 正性（供给肢）与 |A| 正性（规范分子面） *)
Lemma lnt5_c1_pos : forall (clo : nat -> Q) (v : positive),
  (forall n : nat, QltT 0 (clo n)) -> QltT 0 (lnt5_c1 clo v).
Proof.
  intros clo v Hclo. unfold lnt5_c1.
  apply qmult_ltT_0_compat.
  - apply qmult_ltT_0_compat.
    + apply (Hclo (lnt5_n0 v)).
    + apply Qlt_to_QltT. unfold Qlt. cbn. lia.
  - apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    exact (QltT_to_Qlt _ _ (cm_A_pos (lnt5_n0 v))).
Qed.

(* 否支常数正性：带窗 (4/5)^{n₀} < 1/v（conv_core）与 |A| 正性 *)
Lemma lnt5_c2_pos : forall v : positive, QltT 0 (lnt5_c2 v).
Proof.
  intro v. unfold lnt5_c2.
  apply qmult_ltT_0_compat.
  - apply qmult_ltT_0_compat.
    + apply Qlt_to_QltT. apply lic_qlt_0_minus.
      apply QltT_to_Qlt. exact (cc_band_v v).
    + apply Qlt_to_QltT. unfold Qlt. cbn. lia.
  - apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    exact (QltT_to_Qlt _ _ (cm_A_pos (lnt5_n0 v))).
Qed.

(* ============================================================ *)
(* §C 档位与供给重排                                                        *)
(* ============================================================ *)

(* 档位小于一：θ 预算件在 n = 1 的实例（q_pow θ 1 按定义化简为 θ） *)
Theorem lnt5_theta_lt1 : QltT (4 # 5)%Q (1 # 1)%Q.
Proof.
  pose proof (lnt4_theta_budget_lt 1%nat (le_n 1)) as Hb.
  apply Qlt_to_QltT.
  assert (Heq : q_pow (4 # 5)%Q 1 == (4 # 5)%Q) by (vm_compute; reflexivity).
  rewrite <- Heq. exact (QltT_to_Qlt _ _ Hb).
Qed.

(* 供给重排：池面供给型（A/B/θ 已固定为规范数据）折入通用五肢供给接口
   （A := lna_Amod、B := lna_Bmod、θ := 4/5，五肢逐一对位） *)
Theorem lnt5_pade_repack : cm_pade_supply -> ln2i_pade_supply.
Proof.
  intros [clo [Hth1 [HA [Hclo [Hlo Hup]]]]].
  exists lna_Amod. exists lna_Bmod. exists clo. exists (4 # 5)%Q.
  split.
  - exact Hth1.
  - split.
    + exact HA.
    + split.
      * exact Hclo.
      * split.
        -- exact Hlo.
        -- exact Hup.
Qed.

(* ============================================================ *)
(* §D 逐分母均匀分离主定理                                                  *)
(* ============================================================ *)

(* 主定理：供给接口成立时，存在仅依赖分母的正分离函数 f，使
   |u/v − x_k| ≥ f(v) 对一切整数 u、一切 k ≥ K 成立。
   证法：在 n₀ := 8·⌊v⌋ 处按整数行列式是否为零分叉（Z.eq_dec，零 LPO）：
   中支以下界肢的终归 slack 形与命中恒等式得中支常数逐点下界；
   否支以三角不等式链与带窗件得否支常数逐点下界；再经 Qcompare
   极小值把两支常数折算为统一函数 f(v)。 *)
Theorem lnt5_uniform_separation : forall (Hs : cm_pade_supply),
  sigT (fun f : positive -> Q =>
    And (forall v : positive, QltT 0 (f v))
      (forall (u : Z) (v : positive),
        sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
          QleT' (f v) (Qabs (((u # v)%Q - ln2i_x k)%Q))))).
Proof.
  intros [clo [Hth1 [HA [Hclo [Hlo Hup]]]]].
  exists (lnt5_f clo). split.
  - intro v. apply lnt5_qmin_pos.
    + apply (lnt5_c1_pos clo v Hclo).
    + apply lnt5_c2_pos.
  - intros u v.
    destruct (Z.eq_dec (u * lna_Amod (lnt5_n0 v))
                        (Z.pos v * lna_Bmod (lnt5_n0 v))) as [Hhit | Hmiss].
    + (* —— 中支：u/v 为 A_{n₀}·X − B_{n₀} 的零点 —— *)
      assert (HhitQ : (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                        - ((lna_Bmod (lnt5_n0 v)) # 1)%Q)%Q == 0%Q).
      { rewrite ln2b_line_q. rewrite Hhit.
        unfold Qeq. cbn [Qnum Qden Pos.mul]. lia. }
      assert (HepsN : QltT 0 ((clo (lnt5_n0 v)) * (1 # 2)%Q)%Q).
      { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
        - apply QltT_to_Qlt. apply (Hclo (lnt5_n0 v)).
        - unfold Qlt. cbn. lia. }
      destruct (ln2b_le_pt_slack (real_const (clo (lnt5_n0 v)))
                  (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) (Hlo (lnt5_n0 v))
                  ((clo (lnt5_n0 v)) * (1 # 2)%Q)%Q HepsN) as [Kl HKl].
      exists Kl. intros k Hk.
      pose proof (HKl k Hk) as HKlq0.
      pose proof (QltT_to_Qlt _ _ HKlq0) as HKlq.
      rewrite (real_const_proj (clo (lnt5_n0 v)) k) in HKlq.
      pose proof (ln2b_half_lt (clo (lnt5_n0 v))
                    (projT1 (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) k) HKlq)
        as Hlowk.
      rewrite ln2b_line_pt in Hlowk.
      rewrite (ln2b_hit_line (lna_Amod (lnt5_n0 v)) (lna_Bmod (lnt5_n0 v))
                 ((u # v)%Q) k HhitQ) in Hlowk.
      apply Qle_to_QleT'.
      apply Qlt_le_weak.
      apply (Qle_lt_trans (lnt5_f clo v) (lnt5_c1 clo v)
               (Qabs (((u # v)%Q - ln2i_x k)%Q))).
      * apply lnt5_qmin_le_l.
      * rewrite (Qabs_Qminus (u # v)%Q (ln2i_x k)).
        apply (ln2b_div_lt_of ((clo (lnt5_n0 v)) * (1 # 2)%Q)
                 (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q)
                 (Qabs ((ln2i_x k - (u # v))%Q))).
        -- exact (cm_A_pos (lnt5_n0 v)).
        -- exact Hlowk.
    + (* —— 否支：整系数行列式非零，三角不等式链 —— *)
      assert (Hw0 : (u * lna_Amod (lnt5_n0 v)
                     - Z.pos v * lna_Bmod (lnt5_n0 v))%Z <> 0%Z)
        by (intro E; apply Hmiss; lia).
      pose proof (proj2 (Z.abs_pos (u * lna_Amod (lnt5_n0 v)
                          - Z.pos v * lna_Bmod (lnt5_n0 v))%Z) Hw0) as Hwpos.
      assert (Hbook : (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                        - ((lna_Bmod (lnt5_n0 v)) # 1)%Q)%Q
                      == ((u * lna_Amod (lnt5_n0 v)
                           - Z.pos v * lna_Bmod (lnt5_n0 v)) # v)%Q)
        by (apply ln2b_line_q).
      assert (Hdelta0 : QltT 0 (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v))
                                 * (1 # 2)%Q)%Q).
      { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
        - apply lic_qlt_0_minus. apply QltT_to_Qlt. exact (cc_band_v v).
        - unfold Qlt. cbn. lia. }
      destruct (ln2b_le_pt_slack (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v))
                  (real_const (q_pow (4 # 5)%Q (lnt5_n0 v))) (Hup (lnt5_n0 v))
                  (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)%Q
                  Hdelta0) as [Ku HKu].
      exists Ku. intros k Hk.
      pose proof (HKu k Hk) as HKuq0.
      pose proof (QltT_to_Qlt _ _ HKuq0) as HKuq.
      rewrite (real_const_proj (q_pow (4 # 5)%Q (lnt5_n0 v)) k) in HKuq.
      assert (Hmid : (q_pow (4 # 5)%Q (lnt5_n0 v)
                       + ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)%Q
                     == ((1 # v)%Q
                         - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)%Q)
        by ring.
      rewrite Hmid in HKuq.
      assert (Hsplit : (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                         - ((lna_Bmod (lnt5_n0 v)) # 1)%Q)%Q
                       == (((lna_Amod (lnt5_n0 v)) # 1)%Q
                           * ((u # v)%Q - ln2i_x k)%Q
                           + (((lna_Amod (lnt5_n0 v)) # 1)%Q * ln2i_x k
                              - ((lna_Bmod (lnt5_n0 v)) # 1)%Q))%Q)
        by ring.
      assert (Hleg1 : Qle (Qabs ((u * lna_Amod (lnt5_n0 v)
                                  - Z.pos v * lna_Bmod (lnt5_n0 v)) # v)%Q)
                        (Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                               - ((lna_Bmod (lnt5_n0 v)) # 1)%Q))).
      { apply qeq_le. apply Qeq_sym. apply Qabs_wd. exact Hbook. }
      assert (Hleg2 : Qle (Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                                  - ((lna_Bmod (lnt5_n0 v)) # 1)%Q))
                        (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                         * Qabs (((u # v)%Q - ln2i_x k)%Q)
                         + projT1 (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) k)%Q).
      { assert (Hleg2a : Qle (Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q * ((u # v)%Q)
                                      - ((lna_Bmod (lnt5_n0 v)) # 1)%Q))
                              (Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q
                                     * ((u # v)%Q - ln2i_x k)%Q
                                     + (((lna_Amod (lnt5_n0 v)) # 1)%Q * ln2i_x k
                                        - ((lna_Bmod (lnt5_n0 v)) # 1)%Q)))).
        { apply qeq_le. apply Qabs_wd. exact Hsplit. }
        pose proof (Qabs_triangle (((lna_Amod (lnt5_n0 v)) # 1)%Q
                                     * ((u # v)%Q - ln2i_x k)%Q)
                      (((lna_Amod (lnt5_n0 v)) # 1)%Q * ln2i_x k
                       - ((lna_Bmod (lnt5_n0 v)) # 1)%Q)) as HT.
        assert (HE : (Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q
                              * ((u # v)%Q - ln2i_x k)%Q)
                      + Qabs (((lna_Amod (lnt5_n0 v)) # 1)%Q * ln2i_x k
                              - ((lna_Bmod (lnt5_n0 v)) # 1)%Q))%Q
                     == (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                         * Qabs (((u # v)%Q - ln2i_x k)%Q)
                         + projT1 (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) k)%Q).
        { rewrite Qabs_Qmult.
          rewrite <- (ln2b_line_pt lna_Amod lna_Bmod (lnt5_n0 v) k).
          reflexivity. }
        exact (Qle_trans _ _ _ Hleg2a (Qle_trans _ _ _ HT (qeq_le _ _ HE))).
      }
      pose proof (Qle_trans _ _ _ Hleg1 Hleg2) as Htri.
      assert (Hge : Qle (1 # v)%Q
                      (Qabs ((u * lna_Amod (lnt5_n0 v)
                              - Z.pos v * lna_Bmod (lnt5_n0 v)) # v)%Q)).
      { unfold Qle, Qabs. cbn [Qnum Qden]. nia. }
      pose proof (Qle_trans _ _ _ Hge Htri) as Hchain2.
      assert (Hchain3 : Qlt (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                              * Qabs (((u # v)%Q - ln2i_x k)%Q)
                              + projT1 (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) k)%Q
                              (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                               * Qabs (((u # v)%Q - ln2i_x k)%Q)
                               + ((1 # v)%Q - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v))
                                   * (1 # 2)%Q))%Q).
      { apply (lic_qlt_add_l (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                                 * Qabs (((u # v)%Q - ln2i_x k)%Q))).
        exact HKuq. }
      assert (Hpre : Qlt (1 # v)%Q
                       (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                        * Qabs (((u # v)%Q - ln2i_x k)%Q)
                        + ((1 # v)%Q - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v))
                            * (1 # 2)%Q))%Q).
      { apply (Qle_lt_trans (1 # v)%Q
                 (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                  * Qabs (((u # v)%Q - ln2i_x k)%Q)
                  + projT1 (ln2b_line lna_Amod lna_Bmod (lnt5_n0 v)) k)%Q).
        - exact Hchain2.
        - exact Hchain3. }
      assert (Hchain : Qlt (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)
                         (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                          * Qabs (((u # v)%Q - ln2i_x k)%Q))).
      { pose proof (proj1 (Qlt_minus_iff (1 # v)%Q
                             (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                              * Qabs (((u # v)%Q - ln2i_x k)%Q)
                              + ((1 # v)%Q - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v))
                                  * (1 # 2)%Q))%Q) Hpre) as Hm.
        assert (Hring : ((Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                           * Qabs (((u # v)%Q - ln2i_x k)%Q)
                           + ((1 # v)%Q - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v))
                               * (1 # 2)%Q))%Q
                          - (1 # v)%Q)%Q
                        == (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                            * Qabs (((u # v)%Q - ln2i_x k)%Q)
                            - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)%Q)
          by ring.
        rewrite Hring in Hm.
        assert (Hring2 : ((((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)
                            + (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                               * Qabs (((u # v)%Q - ln2i_x k)%Q)
                               - ((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q))%Q
                         == (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                             * Qabs (((u # v)%Q - ln2i_x k)%Q)))
          by ring.
        apply (lic_qlt_comp_r
                 _ (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q
                    * Qabs (((u # v)%Q - ln2i_x k)%Q))
                 (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)
                 Hring2 (lic_qlt_lt_add_r _ _ Hm)).
      }
      apply Qle_to_QleT'.
      apply Qlt_le_weak.
      apply (Qle_lt_trans (lnt5_f clo v) (lnt5_c2 v)
               (Qabs (((u # v)%Q - ln2i_x k)%Q))).
      * apply lnt5_qmin_le_r.
      * apply (ln2b_div_lt_of (((1 # v)%Q - q_pow (4 # 5)%Q (lnt5_n0 v)) * (1 # 2)%Q)
                 (Qabs ((lna_Amod (lnt5_n0 v)) # 1)%Q)
                 (Qabs (((u # v)%Q - ln2i_x k)%Q))).
        -- exact (cm_A_pos (lnt5_n0 v)).
        -- exact Hchain.
Qed.

(* ============================================================ *)
(* §E 分离引擎结论面转写                                                    *)
(* ============================================================ *)

(* 引擎面：经供给投影件（五肢折三肢）直取分离引擎结论——
   对一切有理数 u/v 给出正分离常数与终归指标 *)
Theorem lnt5_bound_final : forall (Hs : cm_pade_supply) (u : Z) (v : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      QleT' c (Qabs (((u # v)%Q - ln2i_x k)%Q))))).
Proof.
  intros Hs u v. exact (cm_bound (cm_pade_of_supply Hs) u v).
Qed.

(* ============================================================ *)
(* §F 无理性终形与柯西极限名同一性                                          *)
(* ============================================================ *)

(* 无理性终形（供给条件形）：对每个有理数 q 给出显式正距离——
   即 ln2 ≠ q 的 Set 层语句形（real_lt 面承载） *)
Theorem lnt5_irrational_final : forall (Hs : cm_pade_supply) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric ln2b_X (real_const q)))).
Proof.
  intros Hs q. exact (ln2b_irrational_from_supply (lnt5_pade_repack Hs) q).
Qed.

(* ln2 的两处柯西极限名逐点同读数，故实现同一实数 *)
Lemma lnt5_carrier_dock : real_eq ln2b_X ri_real.
Proof.
  apply real_eq_of_zero_diff. intro k.
  rewrite ln2b_X_proj. rewrite ri_real_proj.
  apply Qplus_opp_r.
Qed.

(* 线对象双面同一：供给肢所在的线对象与 ri_real 面规范线逐点同读数 *)
Lemma lnt5_line_carrier_dock : forall n : nat,
  real_eq (ln2b_line lna_Amod lna_Bmod n)
          (real_abs (real_plus (real_mult (real_const (lnr_lA n)) ri_real)
                               (real_opp (real_const (lnr_lB n))))).
Proof.
  intro n. apply real_eq_of_zero_diff. intro k.
  rewrite ln2b_line_pt.
  rewrite real_abs_proj, real_plus_proj, real_mult_proj, real_opp_proj,
          real_const_proj, ri_real_proj.
  assert (HE : Qabs ((lnr_lA n * ln2i_x k - lnr_lB n)%Q)
             == Qabs (((lna_Amod n) # 1)%Q * ln2i_x k
                      - ((lna_Bmod n) # 1)%Q)).
  { apply Qabs_wd.
    rewrite (qeqT_imp_qeq _ _ (lna_lA_z n)).
    rewrite (qeqT_imp_qeq _ _ (lna_lB_z n)).
    ring. }
  rewrite HE. ring.
Qed.

(* 无理性终形的 ri_real 面转写：同一分离常数在另一柯西极限名上成立 *)
Theorem lnt5_irrational_ireal_face : forall (Hs : cm_pade_supply) (q : Q),
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric ri_real (real_const q)))).
Proof.
  intros Hs q. destruct (lnt5_irrational_final Hs q) as [c [Hc0 Hlt]].
  exists c. split.
  - exact Hc0.
  - destruct Hlt as [eps [Heps0 [N HN]]].
    exists eps. split.
    + exact Heps0.
    + exists N. intros n Hn. exact (HN n Hn).
Qed.

(* ============================================================ *)
(* §G 数值锚组                                                              *)
(* ============================================================ *)

(* 带窗锚：v = 2 处 (4/5)^{16} < 1/2（conv_core 带窗件实例） *)
Theorem lnt5_anchor_band2 : QltT (q_pow (4 # 5)%Q (lnt5_n0 2%positive))
                                 ((1 # 2)%Q).
Proof. exact (cc_band_v 2%positive). Qed.

(* 否支常数正性锚（v = 1 实例） *)
Theorem lnt5_anchor_c2_1 : QltT 0 (lnt5_c2 1%positive).
Proof. exact (lnt5_c2_pos 1%positive). Qed.

(* 极小值件锚：f(v) 为两支常数的极小值，v = 1 处不超过否支常数 *)
Theorem lnt5_anchor_f1 : forall clo : nat -> Q,
  Qle (lnt5_f clo 1%positive) (lnt5_c2 1%positive).
Proof. intro clo. apply lnt5_qmin_le_r. Qed.

(* ============================================================ *)
(* 提取与假设审计（零承认复核）                                            *)
(* ============================================================ *)

Separate Extraction lnt5_qmin lnt5_f lnt5_uniform_separation
  lnt5_irrational_final.

Print Assumptions lnt5_qmin_le_l.
Print Assumptions lnt5_qmin_le_r.
Print Assumptions lnt5_qmin_pos.
Print Assumptions lnt5_theta_lt1.
Print Assumptions lnt5_c1_pos.
Print Assumptions lnt5_c2_pos.
Print Assumptions lnt5_pade_repack.
Print Assumptions lnt5_uniform_separation.
Print Assumptions lnt5_bound_final.
Print Assumptions lnt5_irrational_final.
Print Assumptions lnt5_carrier_dock.
Print Assumptions lnt5_line_carrier_dock.
Print Assumptions lnt5_irrational_ireal_face.
Print Assumptions lnt5_anchor_band2.
Print Assumptions lnt5_anchor_c2_1.
Print Assumptions lnt5_anchor_f1.
