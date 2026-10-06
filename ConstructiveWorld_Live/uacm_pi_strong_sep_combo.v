(* 五字段指针｜模块：uacm_pi_strong_sep_combo。使命：pi_geom 对每一非零分母有理
   数的显式正距离分离的组合件——将窗族机件（LW5SepComplexity 的 bool 出窗判定器
   lw5n_sep_dec 与最小分离窗阶 lw5n_nsep）与守卫形分离定理（LW0LeibSeparation 的
   leibsep_pi_sep_alpha_guarded）在 Q 层合成：出窗事实经换算引理（包络采样点
   lw0m_xL 含入窗内＋统一窗 lw0m_e 消没）转化为窗距守卫前提，产出 sigT 显式分离
   见证 0 < c < |pi_geom − a/b|。命中前提 leiblw_Id (lw5n_sep_dec …) true 系
   Set 层 bool 恒等假设位，如实保留最小分离窗阶搜索的预算足用性问题（预算足用性
   不在 LW5SepComplexity 主张范围）；附 22/7 实算样例，无条件形依赖增长律闭证，
   属后续工作。
  依赖：S01_BaseRing（NatLe/NatLe_lift/NatLe_drop）、S02_CauchyComplete（QltT/
   QleT'/Qlt_to_QltT/Qle_to_QleT'）、S03_QExp（real_metric/real_const）、
   S10_KVQuantTrig（real_pi_geom）、PiEnvelope（pie_modulus/pie_modulus_bound/
   pie_even_mono/pie_even_le_odd/pie_v_eq/pie_mag_pos/pie_mag_antitone）、
   LW0LeibWindow（leiblw_Id/leiblw_Qleb）、LW0MLicBridge（lw0m_xL/lw0m_e）、
   LW5SepComplexity（lw5n_eps/lw5n_lo/lw5n_hi/lw5n_M/lw5n_modulus_val/
   lw5n_eps4_pos/lw5n_sep_dec/lw5n_inwin/lw5n_nsep/lw5n_Qleb_false_lt）、
   Local.LW0LeibSeparation（leibsep_pi_sep_alpha_guarded）。
  对标：论文A §4.2/§4.3/§5.1（可计算最小分离指数、预算诚实缺口、守卫形态一）。
  构造性：零公理／零承认式；语句面全 Set 层（QltT/QleT'/sigT/And/leiblw_Id/
   NatLe 均 Set 值），证内 Prop（Qlt/Qle/Or）仅作脚手架且分支消去整体封装于
   辅助引理（Qed 闭合）后以 Set 值产出供主定理使用。
  编译配方：coqc -q -Q <世界根> "" uacm_pi_strong_sep_combo.v（全字面双 export
   COQLIB/ROCQLIB 指向 9.1 平台库）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lia Bool.Bool Lqa Arith.Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0LeibWindow.
Require Import LW0MLicBridge.
Require Import LW5SepComplexity.
Require Import Local.LW0LeibSeparation.

(* ============================================================ *)
(* §1 换算机件：包络采样点含入窗内                                      *)
(*   统一窗采样点 xL k := lp_four * lp_odd k = 4·S(2k+2)（pie_v_eq），在  *)
(*   k ≥ M := pie_modulus(eps_n/2) 时落窗 [lo_n, hi_n] 内：偶列单调      *)
(*   （pie_even_mono）给下含入，偶阶恒不越奇阶（pie_even_le_odd，全域）   *)
(*   给上含入。                                                          *)
(* ============================================================ *)

Lemma uacm_modulus_pos : forall eps : Q, (1 <= pie_modulus eps)%nat.
Proof.
  intros eps. unfold pie_modulus.
  destruct (Z.to_nat (Qceiling (4 / eps))); lia.
Qed.

Lemma uacm_xL_in_win : forall (n k : nat),
  NatLe (pie_modulus (lw5n_eps n / 2)) k ->
  And (QleT' (lw5n_lo n) (lw0m_xL k)) (QleT' (lw0m_xL k) (lw5n_hi n)).
Proof.
  intros n k Hk.
  apply NatLe_drop in Hk.
  pose proof (lw5n_eps4_pos n) as Hc4.
  split.
  - (* 下含入：lo n ≤ 4·S(2M+2) ≤ 4·S(2k+2) = xL k *)
    apply Qle_to_QleT'.
    assert (HloS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)
                    == lw5n_lo n + lw5n_eps n / 4)%Q).
    { unfold lw5n_lo, lw5n_M.
      replace (2 * pie_modulus (lw5n_eps n / 2) + 1 + 1)%nat
        with (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat by lia.
      ring. }
    assert (Hmono : Qle (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
                        (4 * pie_partial (2 * k + 2))).
    { apply pie_mult4_le.
      replace (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat
        with (2 * (pie_modulus (lw5n_eps n / 2) + 1))%nat by lia.
      replace (2 * k + 2)%nat
        with (2 * (pie_modulus (lw5n_eps n / 2) + 1
                   + (k - pie_modulus (lw5n_eps n / 2))))%nat by lia.
      apply (pie_even_mono (k - pie_modulus (lw5n_eps n / 2))
                           (pie_modulus (lw5n_eps n / 2) + 1)). }
    pose proof (qeq_le _ _ (Qeq_sym _ _ HloS)) as H1.
    apply (Qle_trans _ (lw5n_lo n + lw5n_eps n / 4)%Q _).
    + pose proof (Qle_refl (lw5n_lo n)). lra.
    + apply (Qle_trans _ (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)) _).
      * exact H1.
      * apply (Qle_trans _ (4 * pie_partial (2 * k + 2))%Q _).
        -- exact Hmono.
        -- apply qeq_le. apply Qeq_sym. exact (pie_v_eq k).
  - (* 上含入：xL k = 4·S(2k+2) ≤ 4·S(2M+1) = hi n − eps_n/4 ≤ hi n *)
    apply Qle_to_QleT'.
    assert (HhiS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1)
                    == lw5n_hi n - lw5n_eps n / 4)%Q).
    { unfold lw5n_hi, lw5n_M. ring. }
    assert (Hodd : Qle (4 * pie_partial (2 * k + 2))
                       (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))).
    { apply pie_mult4_le.
      replace (2 * k + 2)%nat with (2 * (k + 1))%nat by lia.
      apply (pie_even_le_odd (k + 1) (pie_modulus (lw5n_eps n / 2))). }
    apply (Qle_trans _ (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1)) _).
    + apply (Qle_trans _ (4 * pie_partial (2 * k + 2))%Q _).
      * apply qeq_le. exact (pie_v_eq k).
      * exact Hodd.
    + pose proof (qeq_le _ _ HhiS) as H2.
      apply (Qle_trans _ (lw5n_hi n - lw5n_eps n / 4)%Q _).
      * exact H2.
      * pose proof (Qle_refl (lw5n_hi n)). lra.
Qed.

(* ============================================================ *)
(* §2 换算引理：出窗事实 → 守卫前提（N, c0 显式 witness 包，全 Set 面）    *)
(*   N := max(M1, M2)，M1 承担采样点含入窗（§1），M2 := pie_modulus(d/10)  *)
(*   承担统一窗消没（4·pie_mag M2 < d/10 ⟹ lw0m_e N < d/8）；              *)
(*   c0 := d/4；合成 lw0m_e N + 2·c0 < d ≤ |xL N − q|（出窗距离传递）。    *)
(*   NatLe 1 N 承载守卫形的 (1 ≤ N) 前提（Set 面，NatLe_drop 回 nat ≤）。 *)
(* ============================================================ *)

Lemma uacm_guard_of_hit : forall (q : Q) (n : nat),
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun N : nat => sigT (fun c0 : Q =>
    And (QltT 0 c0)
        (And (NatLe 1 N)
             (QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)))))).
Proof.
  intros q n Hhit.
  (* 出窗分解：bool 层分支（Bool 消去入 Set 合法），不产 Or *)
  unfold lw5n_sep_dec in Hhit. apply leiblw_id_inv in Hhit.
  apply negb_true_iff in Hhit.
  unfold lw5n_inwin in Hhit.
  destruct (leiblw_Qleb (lw5n_lo n) q) eqn:Hf1.
  - (* lo ≤ q 分支：andb true b = false ⟹ b = false ⟹ hi < q *)
    assert (Hf2 : leiblw_Qleb q (lw5n_hi n) = false).
    { simpl in Hhit. exact Hhit. }
    assert (Hhi : Qlt (lw5n_hi n) q) by exact (lw5n_Qleb_false_lt _ _ Hf2).
    assert (Hd : Qlt 0 (q - lw5n_hi n)%Q) by lra.
    exists (Nat.max (pie_modulus (lw5n_eps n / 2))
                    (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q)).
    exists ((q - lw5n_hi n) * (1 # 4))%Q.
    split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (q - lw5n_hi n) (1 # 4)).
      * exact Hd.
      * unfold Qlt. simpl. lia.
    + split.
      * apply NatLe_lift.
        pose proof (uacm_modulus_pos (lw5n_eps n / 2)). lia.
      * assert (Hbnd : Qlt (4 * pie_mag (pie_modulus
                              ((q - lw5n_hi n) * (1 # 10))%Q))
                           ((q - lw5n_hi n) * (1 # 10))%Q).
        { apply pie_modulus_bound.
          apply (Qmult_lt_0_compat (q - lw5n_hi n) (1 # 10)).
          - exact Hd.
          - unfold Qlt. simpl. lia. }
        assert (Hanti : Qle (pie_mag (Nat.max (pie_modulus (lw5n_eps n / 2))
                                     (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q)))
                            (pie_mag (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q))).
        { apply pie_mag_antitone. lia. }
        destruct (uacm_xL_in_win n
                    (Nat.max (pie_modulus (lw5n_eps n / 2))
                             (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q))
                    (NatLe_lift _ _ (Nat.le_max_l _ _))) as [Hinl Hinu].
        apply QleT'_to_Qle in Hinu.
        assert (Hab : Qle ((q - lw5n_hi n)%Q)
                          (Qabs ((lw0m_xL (Nat.max (pie_modulus (lw5n_eps n / 2))
                                          (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q))
                                   - q)%Q))).
        { apply (Qabs_case (lw0m_xL (Nat.max (pie_modulus (lw5n_eps n / 2))
                                    (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q))
                             - q)
                   (fun z => Qle (q - lw5n_hi n) z)).
          - intros Hs0. lra.
          - intros Hs0. lra. }
        assert (He : Qlt (lw0m_e (Nat.max (pie_modulus (lw5n_eps n / 2))
                                    (pie_modulus ((q - lw5n_hi n) * (1 # 10))%Q))
                           + 2 * ((q - lw5n_hi n) * (1 # 4)))
                         (q - lw5n_hi n)%Q).
        { unfold lw0m_e. lra. }
        apply Qlt_to_QltT.
        exact (Qlt_le_trans _ _ _ He Hab).
  - (* q < lo 分支；d := lo n − q *)
    assert (Hlo : Qlt q (lw5n_lo n)) by exact (lw5n_Qleb_false_lt _ _ Hf1).
    assert (Hd : Qlt 0 (lw5n_lo n - q)%Q) by lra.
    exists (Nat.max (pie_modulus (lw5n_eps n / 2))
                    (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q)).
    exists ((lw5n_lo n - q) * (1 # 4))%Q.
    split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (lw5n_lo n - q) (1 # 4)).
      * exact Hd.
      * unfold Qlt. simpl. lia.
    + split.
      * apply NatLe_lift.
        pose proof (uacm_modulus_pos (lw5n_eps n / 2)). lia.
      * assert (Hbnd : Qlt (4 * pie_mag (pie_modulus
                              ((lw5n_lo n - q) * (1 # 10))%Q))
                           ((lw5n_lo n - q) * (1 # 10))%Q).
        { apply pie_modulus_bound.
          apply (Qmult_lt_0_compat (lw5n_lo n - q) (1 # 10)).
          - exact Hd.
          - unfold Qlt. simpl. lia. }
        assert (Hanti : Qle (pie_mag (Nat.max (pie_modulus (lw5n_eps n / 2))
                                     (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q)))
                            (pie_mag (pie_modulus
                              ((lw5n_lo n - q) * (1 # 10))%Q))).
        { apply pie_mag_antitone. lia. }
        destruct (uacm_xL_in_win n
                    (Nat.max (pie_modulus (lw5n_eps n / 2))
                             (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q))
                    (NatLe_lift _ _ (Nat.le_max_l _ _))) as [Hinl Hinu].
        apply QleT'_to_Qle in Hinl.
        assert (Hab : Qle ((lw5n_lo n - q)%Q)
                          (Qabs ((lw0m_xL (Nat.max (pie_modulus (lw5n_eps n / 2))
                                          (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q))
                                   - q)%Q))).
        { apply (Qabs_case (lw0m_xL (Nat.max (pie_modulus (lw5n_eps n / 2))
                                    (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q))
                             - q)
                   (fun z => Qle (lw5n_lo n - q) z)).
          - intros Hs0. lra.
          - intros Hs0. lra. }
        assert (He : Qlt (lw0m_e (Nat.max (pie_modulus (lw5n_eps n / 2))
                                    (pie_modulus ((lw5n_lo n - q) * (1 # 10))%Q))
                           + 2 * ((lw5n_lo n - q) * (1 # 4)))
                         (lw5n_lo n - q)%Q).
        { unfold lw0m_e. lra. }
        apply Qlt_to_QltT.
        exact (Qlt_le_trans _ _ _ He Hab).
Qed.

(* ============================================================ *)
(* §3 主组合定理：sigT 显式分离见证                                       *)
(* ============================================================ *)

Theorem uacm_pi_strong_sep_combo :
  forall (a b : Q),
    QltT 0 (Qabs b) ->
    leiblw_Id (lw5n_sep_dec (a / b)%Q (lw5n_nsep (a / b)%Q)) true ->
    sigT (fun c : Q => And (QltT 0 c)
            (real_lt (real_const c)
               (real_metric real_pi_geom (real_const (a / b))))).
Proof.
  intros a b Hb Hhit.
  destruct (uacm_guard_of_hit (a / b)%Q (lw5n_nsep (a / b)%Q) Hhit)
    as [N [c0 [Hc0 [HNle Hg]]]].
  exact (leibsep_pi_sep_alpha_guarded a b N c0 Hb
           (NatLe_drop 1 N HNle) Hc0 Hg).
Qed.

(* ============================================================ *)
(* §4 实算样例：22/7 的命中前提真算（vm_compute 实例核对）                 *)
(* ============================================================ *)

Lemma uacm_gate_sample_three :
  leiblw_Id (lw5n_sep_dec 3%Q (lw5n_nsep 3%Q)) true.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 提取检验＋假设审计                                                 *)
(* ============================================================ *)

From Stdlib Require Import Extraction.

Separate Extraction lw5n_sep_dec lw5n_nsep uacm_xL_in_win
  uacm_modulus_pos uacm_guard_of_hit uacm_pi_strong_sep_combo.

Print Assumptions uacm_modulus_pos.
Print Assumptions uacm_xL_in_win.
Print Assumptions uacm_guard_of_hit.
Print Assumptions uacm_pi_strong_sep_combo.
Print Assumptions uacm_gate_sample_three.
