(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpRealLeB2.v *)
(* *)
(* 目的： 多 eps 组合链与广义完成器（Bishop 显式假设攻坚第二段）。 *)
(* 主件： real_le_b_plus_compat / real_abs_le_quad_B 组合链与 real_db_breaking_bound_B 完成器。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB。 *)
(* 备注： 正性证书缺位场景（如仅非负）以免倒逆形态处理；keep 可判定与迁移对称为 Variable 前提。 *)
(* ============================================================ *)
(* ============================================================ *)
(* UpRealLeB2.v —— Bishop：多 eps 组合链四件＋广义完成器                 *)
(*   （上游 UpRealLeB 引擎的续建层；Require 使用，上游零变动）        *)
(* *)
(* 主结果（全部 Set 层、零 Prop 泄露、纯 term-mode 组装）：          *)
(*   F.1 real_le_closure_b_nonneg：非负系数完成器（广义完成器之一）——C ≥ 0 证书＋(∀eps>0, x ≤ y + C·eps) ⟹ x ≤_B y；与 real_le_closure_b（C>0 证书版）的关键差异：系数只须非负——见证 e₀ := δ·inv(2)·inv(C+1)（C+1 > 0 可从 C≥0 构造），C·e₀ ≤ δ·inv(2) < δ（C·inv(C+1) ≤ 1 单调一步），免去 C 本身的倒逆——正性证书缺位（如 T 仅 ≥0）场景的复合系数链完成规格件。 *)
(*   F.2 real_le_b_trans：≤_B 传递组合器（x ≤_B y ∧ y ≤_B z ⟹ x ≤_B z，eps/2 拆分：δ·inv(2) 双份，(z+dh)+dh == z+δ 换形完成）。 *)
(*   F.3 real_le_b_plus_compat：≤_B 加法兼容组合器（x ≤_B y ∧ u ≤_B v ⟹ x+u ≤_B y+v，同 eps/2 拆分手法）。 *)
(*   F.4 real_abs_le_quad_B：|X| ≤_B 2t²+(eps1+eps2)——源件尾带全称 eps 余量，one 特化完成单步＋源件直连。 *)
(*   F.5 real_quad_t_le_h_B：2(h/x)² ≤_B (1/2)·eps·|h|——源件 eps' 为全称求和余量，完成后 eps' 从界内消去。 *)
(*   F.6 real_abs_h_sq_le_B：A|h|² ≤_B (A·eps3)·|h|——同链，eps' 消去。 *)
(*   F.7 real_db_breaking_bound_B：db ≤_B invZ·T·(e^{E/D}·M)——源件 eps/eps' 内嵌于 invZ·T·(exp·(eps+eps')) 复合系数，F.1 非负系数完成器实例（C := invZ·T·(exp+1)，非负性由 invZ>0、T≥0、exp+1>0 逐级组装——T 的正性不可证故 C>0 证书路线不可行，正是 F.1 的规格动机）。 *)
(* *)
(* 红线：零未闭合证明（G1 禁词全零）；Set 层语句；纯 term-mode 显式组装（real_eq 非 Id，禁 rewrite，全链 real_eq_trans/compat）；全 Qed 闭合；新件 Print Assumptions Closed（文末）。 *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.

(* ============================================================ *)
(* F.0 辅助：δ·inv(2) + δ·inv(2) == δ（eps/2 拆分换形基础模块）          *)
(* ============================================================ *)

Lemma leb2_half_add : forall d : Real,
  real_eq
    (real_plus
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    d.
Proof.
  intro d.
  (* dh + dh == d·(h+h) == d·(h+h) 换形链 *)
  apply (real_eq_trans _
           (real_mult d
              (real_plus
                 (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                 (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
           _).
  - apply real_eq_sym. apply real_distrib.
  - apply (real_eq_trans _ (real_mult d real_one) _).
    + apply (RealSetoid.real_eq_mult_compat d
               (real_plus
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
               d
               real_one).
      * apply real_eq_refl.
      * (* h + h == 1：h+h == h·1+h·1 == h·(1+1) == (1+1)·h == 1 *)
        apply (real_eq_trans _
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one))
                 _).
        -- apply (RealSetoid.real_eq_plus_compat
                    (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                    (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) real_one)).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_eq_sym. apply real_mult_one.
        -- apply (real_eq_trans _
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                               (real_plus real_one real_one))
                    _).
           ++ apply real_eq_sym. apply real_distrib.
           ++ apply (real_eq_trans _
                       (real_mult (real_plus real_one real_one)
                                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       _).
              ** apply real_mult_comm.
              ** apply real_inv_pos_correct.
    + apply real_mult_one.
Qed.

(* ============================================================ *)
(* F.1 非负系数完成器（广义完成器规格件）                             *)
(*   C ≥ 0 时 C 的正性不可证场景（复合系数含 ≥0 因子）仍可完成：        *)
(*   见证 e₀ := δ·inv(2)·inv(C+1)，C·e₀ == δ·inv(2)·(C·inv(C+1))       *)
(*        ≤ δ·inv(2)·((C+1)·inv(C+1)) == δ·inv(2) < δ。                *)
(* ============================================================ *)

Lemma real_le_closure_b_nonneg : forall x y C : Real,
  real_le real_zero C ->
  (forall eps : Real, real_lt real_zero eps ->
    real_le x (real_plus y (real_mult C eps))) ->
  real_le_b x y.
Proof.
  intros x y C HC H. unfold real_le_b. intros d Hd.
  (* 半见证 dh := δ·inv(2) 及其正性 *)
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  (* C + 1 > 0 与 C ≤ C + 1（非负系数的唯一证书加工面） *)
  assert (HCltp : real_lt C (real_plus C real_one)).
  { apply (RealSetoid.real_lt_id_l C (real_plus C real_zero) (real_plus C real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate C real_zero real_one). exact real_lt_zero_one. }
  assert (HCle : real_le C (real_plus C real_one))
    by exact (RealSetoid.real_lt_le_iff_req C (real_plus C real_one) (inl HCltp)).
  assert (HCp : real_lt real_zero (real_plus C real_one)).
  { apply (real_lt_le_trans real_zero real_one (real_plus C real_one) real_lt_zero_one).
    apply (RealSetoid.real_le_id_l real_one (real_plus real_zero real_one) (real_plus C real_one)).
    - apply real_eq_sym.
      apply (real_eq_trans (real_plus real_zero real_one) (real_plus real_one real_zero) _).
      + apply real_plus_comm.
      + apply real_plus_zero.
    - apply (real_le_plus_compat real_zero C real_one real_one).
      + exact HC.
      + apply real_le_refl. }
  assert (HinvCp : real_lt real_zero (real_inv_pos (real_plus C real_one) HCp))
    by exact (real_inv_pos_pos (real_plus C real_one) HCp).
  (* 见证 e₀ := δ·inv(2)·inv(C+1) > 0 *)
  assert (He0pos : real_lt real_zero
    (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
               (real_inv_pos (real_plus C real_one) HCp)))
    by exact (real_mult_positive
                (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                (real_inv_pos (real_plus C real_one) HCp) Hdh HinvCp).
  (* 关键界：C·e₀ ≤ δ·inv(2) < δ *)
  assert (Hkey : real_le
    (real_mult C
       (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_inv_pos (real_plus C real_one) HCp)))
    (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))).
  { assert (Heq1 : real_eq
      (real_mult C
         (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                    (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult C (real_inv_pos (real_plus C real_one) HCp)))).
    { apply (real_eq_trans _
               (real_mult
                  (real_mult C
                     (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                  (real_inv_pos (real_plus C real_one) HCp))
               _).
      - apply real_mult_assoc.
      - apply (real_eq_trans _
                 (real_mult
                    (real_mult
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       C)
                    (real_inv_pos (real_plus C real_one) HCp))
                 _).
        + apply (RealSetoid.real_eq_mult_compat
                    (real_mult C
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                    (real_inv_pos (real_plus C real_one) HCp)
                    (real_mult
                       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                       C)
                    (real_inv_pos (real_plus C real_one) HCp)).
          * apply real_mult_comm.
          * apply real_eq_refl.
        + apply real_eq_sym. apply real_mult_assoc. }
    assert (Hle2 : real_le
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult C (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))))
      by exact (real_le_mult_compat_r
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_mult C (real_inv_pos (real_plus C real_one) HCp))
                  (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))
                  (RealSetoid.real_lt_le_iff_req real_zero _
                    (inl Hdh))
                  (real_le_mult_compat C (real_plus C real_one)
                     (real_inv_pos (real_plus C real_one) HCp) HinvCp HCle)).
    assert (Heq3 : real_eq
      (real_mult
         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
         (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp)))
      (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))).
    { apply (real_eq_trans _
               (real_mult
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  real_one)
               _).
      - apply (RealSetoid.real_eq_mult_compat
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  (real_mult (real_plus C real_one) (real_inv_pos (real_plus C real_one) HCp))
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  real_one).
        + apply real_eq_refl.
        + apply real_inv_pos_correct.
      - apply real_mult_one. }
    exact (real_le_trans _ _
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (RealSetoid.real_le_id_l _ _ _ Heq1 (real_le_refl _))
             (RealSetoid.real_le_id_r _ _ _ Heq3 Hle2)). }
  (* 使用假设（Or 编码两支分别闭合） *)
  destruct (H _
    (real_mult_positive
       (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_inv_pos (real_plus C real_one) HCp) Hdh HinvCp)) as [Hlt | Heq].
  - apply (real_lt_trans x (real_plus y (real_mult C
      (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_inv_pos (real_plus C real_one) HCp)))) (real_plus y d)).
    + exact Hlt.
    + apply (real_le_lt_trans _ (real_plus y
        (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))) (real_plus y d)).
      * apply (real_le_plus_compat y y _ _).
        -- apply real_le_refl.
        -- exact Hkey.
      * apply (real_lt_plus_translate y
          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) d).
        -- (* dh < d：dh < d·1 == d *)
           apply (real_lt_eq_lt
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (real_mult d real_one) d).
           ++ apply (real_mult_lt_compat_l
                       (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                       real_one d real_inv_two_lt_one Hd).
           ++ apply real_mult_one.
  - apply (RealSetoid.real_lt_id_l x (real_plus y (real_mult C
      (real_mult (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_inv_pos (real_plus C real_one) HCp)))) (real_plus y d)).
    + exact Heq.
    + apply (real_le_lt_trans _ (real_plus y
        (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))) (real_plus y d)).
      * apply (real_le_plus_compat y y _ _).
        -- apply real_le_refl.
        -- exact Hkey.
      * apply (real_lt_plus_translate y
          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) d).
        -- (* dh < d：dh < d·1 == d *)
           apply (real_lt_eq_lt
             (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
             (real_mult d real_one) d).
           ++ apply (real_mult_lt_compat_l
                       (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                       real_one d real_inv_two_lt_one Hd).
           ++ apply real_mult_one.
Qed.

(* ============================================================ *)
(* F.2 ≤_B 传递组合器：x ≤_B y ∧ y ≤_B z ⟹ x ≤_B z                    *)
(*   （eps/2 拆分：双份 δ·inv(2)，中项 (z+dh)+dh == z+δ 换形）          *)
(* ============================================================ *)

Lemma real_le_b_trans : forall x y z : Real,
  real_le_b x y -> real_le_b y z -> real_le_b x z.
Proof.
  intros x y z Hxy Hyz. unfold real_le_b in Hxy, Hyz. unfold real_le_b. intros d Hd.
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  pose proof (Hxy (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) Hdh) as H1.
  pose proof (Hyz (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) Hdh) as H2.
  (* 中项：y + dh < (z + dh) + dh（dh+y 平移路线 + comm 换形） *)
  assert (Hmid : real_lt
    (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))).
  { pose proof (real_lt_plus_translate
                  (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                  y (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                  H2) as H3.
    apply (real_lt_eq_lt
      (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
      (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                 (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))
      (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                 (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))).
    - (* y+dh < dh+(z+dh)：左项 comm 换形（real_lt_id_l）+ 平移 *)
      apply (RealSetoid.real_lt_id_l
               (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)) y)
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                          (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))).
      + apply real_plus_comm.
      + exact H3.
    - (* dh+(z+dh) == (z+dh)+dh：plus_comm *)
      apply real_plus_comm. }
  (* 尾项：(z+dh)+dh == z+δ *)
  assert (Heqz : real_eq
    (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
    (real_plus z d)).
  { apply (real_eq_trans _
             (real_plus z
                (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                           (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))))
             _).
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat z
               (real_plus (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
                          (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
               z d).
      + apply real_eq_refl.
      + exact (leb2_half_add d). }
  exact (real_lt_trans x
           (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
           (real_plus z d) H1
           (real_lt_eq_lt
              (real_plus y (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
              (real_plus (real_plus z (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
                         (real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)))
              (real_plus z d) Hmid Heqz)).
Qed.

(* ============================================================ *)
(* F.3 ≤_B 加法兼容组合器：x ≤_B y ∧ u ≤_B v ⟹ x+u ≤_B y+v            *)
(*   （eps/2 拆分：两份 δ·inv(2)，(y+dh)+(v+dh) == (y+v)+δ 换形）       *)
(* ============================================================ *)

Lemma real_le_b_plus_compat : forall x y u v : Real,
  real_le_b x y -> real_le_b u v ->
  real_le_b (real_plus x u) (real_plus y v).
Proof.
  intros x y u v Hx Hu. unfold real_le_b in Hx, Hu. unfold real_le_b. intros d Hd.
  set (dh := real_mult d (real_inv_pos (real_plus real_one real_one) real_two_pos_local)).
  assert (Hhalfpos : real_lt real_zero (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdh : real_lt real_zero dh)
    by exact (real_mult_positive d
                (real_inv_pos (real_plus real_one real_one) real_two_pos_local) Hd Hhalfpos).
  pose proof (Hx dh Hdh) as H1.
  pose proof (Hu dh Hdh) as H2.
  pose proof (real_lt_plus_compat x (real_plus y dh) u (real_plus v dh) H1 H2) as H3.
  (* (y+dh)+(v+dh) == (y+v)+δ：assoc/comm 六步换形，逐 assert 定位 *)
  assert (HstepA : real_eq (real_plus (real_plus y dh) (real_plus v dh))
                           (real_plus y (real_plus dh (real_plus v dh)))).
  { apply real_eq_sym. apply real_plus_assoc. }
  assert (HstepB : real_eq (real_plus y (real_plus dh (real_plus v dh)))
                           (real_plus y (real_plus dh (real_plus dh v)))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus dh (real_plus v dh)) y (real_plus dh (real_plus dh v))).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat dh (real_plus v dh) dh (real_plus dh v)).
      + apply real_eq_refl.
      + apply real_plus_comm. }
  assert (HstepC : real_eq (real_plus y (real_plus dh (real_plus dh v)))
                           (real_plus y (real_plus (real_plus dh dh) v))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus dh (real_plus dh v)) y (real_plus (real_plus dh dh) v)).
    - apply real_eq_refl.
    - apply real_plus_assoc. }
  assert (HstepD : real_eq (real_plus y (real_plus (real_plus dh dh) v))
                           (real_plus y (real_plus d v))).
  { apply (RealSetoid.real_eq_plus_compat y (real_plus (real_plus dh dh) v) y (real_plus d v)).
    - apply real_eq_refl.
    - apply (RealSetoid.real_eq_plus_compat (real_plus dh dh) v d v).
      + exact (leb2_half_add d).
      + apply real_eq_refl. }
  assert (HstepE : real_eq (real_plus y (real_plus d v))
                           (real_plus (real_plus y v) d)).
  { apply (real_eq_trans _ (real_plus y (real_plus v d)) _).
    - apply (RealSetoid.real_eq_plus_compat y (real_plus d v) y (real_plus v d)).
      + apply real_eq_refl.
      + apply real_plus_comm.
    - apply real_plus_assoc. }
  apply (real_lt_eq_lt (real_plus x u)
                       (real_plus (real_plus y dh) (real_plus v dh))
                       (real_plus (real_plus y v) d)).
  - exact H3.
  - exact (real_eq_trans _ _ _ HstepA (real_eq_trans _ _ _ HstepB
             (real_eq_trans _ _ _ HstepC (real_eq_trans _ _ _ HstepD HstepE)))).
Qed.

(* ============================================================ *)
(* F.4 盘点 #24 real_abs_le_quad_eps 升格：|X| ≤_B 2t²+(eps1+eps2)     *)
(*   源件结论尾带全称 eps 余量（eps1/eps2 为前提位固定正量并入右端），   *)
(*   证书链 = one 特化完成单步 + 源件直连，零新增前提。                 *)
(* ============================================================ *)

Lemma real_abs_le_quad_B : forall (X t eps1 eps2 : Real),
  real_le X eps1 ->
  real_le (real_opp X)
          (real_plus (real_mult (real_mult t t) (real_plus real_one real_one)) eps2) ->
  real_lt real_zero eps1 -> real_lt real_zero eps2 ->
  real_le_b (real_abs X)
            (real_plus (real_mult (real_mult t t) (real_plus real_one real_one))
                       (real_plus eps1 eps2)).
Proof.
  intros X t eps1 eps2 HXA HXB HA Heps2.
  apply real_le_closure_b_one. intros eps Heps.
  exact (real_abs_le_quad_eps X t eps1 eps2 eps HXA HXB HA Heps2 Heps).
Qed.

(* ============================================================ *)
(* F.5 盘点 #25 real_quad_t_le_h_eps 升格：2(h/x)² ≤_B (1/2)·eps·|h|   *)
(*   源件 eps' 为全称求和余量（0<eps' 前提位），完成后 eps' 从界内      *)
(*   消去；余量内嵌 |h| 因子随固定端并入右端。零新增前提。              *)
(* ============================================================ *)

Lemma real_quad_t_le_h_B : forall (x h eps : Real) (Hx : real_lt real_zero x),
  real_lt (real_abs h)
    (real_mult
       (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local)
                  (real_inv_pos (real_plus real_one real_one) real_two_pos_local))
       (real_mult eps (real_mult x x))) ->
  real_lt real_zero eps ->
  real_le_b
    (real_mult (real_mult (real_mult h (real_inv_pos x Hx)) (real_mult h (real_inv_pos x Hx)))
               (real_plus real_one real_one))
    (real_mult (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos_local) eps)
               (real_abs h)).
Proof.
  intros x h eps Hx Hh Heps.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_quad_t_le_h_eps x h eps eps' Hx Hh Heps Heps').
Qed.

(* ============================================================ *)
(* F.6 盘点 #28 real_abs_h_sq_le_eps 升格：A|h|² ≤_B (A·eps3)·|h|      *)
(*   同 F.5 链型（双余量 A·eps3·|h| + eps'，eps' 全称消去）。           *)
(* ============================================================ *)

Lemma real_abs_h_sq_le_B : forall A h eps3 : Real,
  real_lt real_zero A -> real_lt (real_abs h) eps3 ->
  real_le_b (real_mult A (real_mult (real_abs h) (real_abs h)))
            (real_mult (real_mult A eps3) (real_abs h)).
Proof.
  intros A h eps3 HA Hh3.
  apply real_le_closure_b_one. intros eps' Heps'.
  exact (real_abs_h_sq_le_eps A h eps3 eps' HA Hh3 Heps').
Qed.

(* ============================================================ *)
(* F.7 盘点 #32 real_db_breaking_bound_eps 升格（复合系数非负完成）   *)
(*   源件 eps 与 eps' 内嵌于 invZ·T·(exp·eps + eps') 复合系数；系数     *)
(*   C := invZ·T·(exp+1) 仅非负（T ≥ 0 无正性证书），正走 F.1 器。      *)
(*   完成后 eps 与 eps' 同时从界内消去：db ≤_B invZ·T·(exp·M)。        *)
(*   节变量逐字对偶源件 discharged 前缀（15 参，检验实测）。           *)
(* ============================================================ *)

Section RealKVQuantLeB.

Variable S : Type.
Variable keep : S -> Set.
Variable keep_dec : forall s : S, Or (keep s) (Not (keep s)).
Variable real_transition : S -> S -> Real.
Variable real_transition_nonneg : forall s s' : S, real_le real_zero (real_transition s s').
Variable real_transition_sym : forall s s' : S, real_eq (real_transition s s') (real_transition s' s).
Variable real_energy : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable L : Real.
Variable E_max : Real.
Variable real_metric : S -> S -> Real.
Variable real_energy_lipschitz : forall s s' : S,
  real_le (real_abs (real_plus (real_energy s) (real_opp (real_energy s'))))
          (real_mult L (real_metric s s')).
Variable real_energy_lower : forall s : S, real_le (real_opp E_max) (real_energy s).
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_evicted_partition_pos : real_lt real_zero
  (real_evicted_partition S keep keep_dec real_energy D D_pos real_sum_over_S).

Theorem real_db_breaking_bound_B : forall s s' : S,
  keep s -> keep s' ->
  real_le_b
    (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                      real_sum_over_S real_evicted_partition_pos s s')
    (real_mult
       (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                        real_sum_over_S) real_evicted_partition_pos)
       (real_mult (real_transition s s')
                  (real_mult
                     (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                     (real_mult
                        (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                        (cauchy_real_exp
                           (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))))))).
Proof.
  intros s s' Hs Hs'.
  apply (real_le_closure_b_nonneg
           (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                             real_sum_over_S real_evicted_partition_pos s s')
           (real_mult
              (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                               real_sum_over_S) real_evicted_partition_pos)
              (real_mult (real_transition s s')
                         (real_mult
                            (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                            (real_mult
                               (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                               (cauchy_real_exp
                                  (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))))))
           (real_mult
              (real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                               real_sum_over_S) real_evicted_partition_pos)
              (real_mult (real_transition s s')
                         (real_plus (cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max))
                                    real_one)))).
  (* 前提 1：0 ≤ C := invZ·(T·(exp+1))——invZ>0、T≥0、exp+1>0 逐级组装 *)
  {
  set (W := real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                             real_sum_over_S) real_evicted_partition_pos).
  set (T := real_transition s s').
  set (E1 := cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)).
  assert (HWpos : real_lt real_zero W)
    by exact (real_inv_pos_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                                  real_sum_over_S) real_evicted_partition_pos).
  assert (HWle : real_le real_zero W)
    by exact (RealSetoid.real_lt_le_iff_req real_zero W (inl HWpos)).
  assert (HTle : real_le real_zero T) by exact (real_transition_nonneg s s').
  assert (HGpos : real_lt real_zero (real_plus E1 real_one))
    by exact (real_plus_positive E1 real_one
                (cauchy_real_exp_pos (real_mult (real_inv_pos D D_pos) E_max)) real_lt_zero_one).
  assert (HTG : real_le real_zero (real_mult T (real_plus E1 real_one))).
  { apply (RealSetoid.real_le_id_l real_zero (real_mult T real_zero)
                                   (real_mult T (real_plus E1 real_one))).
    - apply real_eq_sym. apply real_mult_zero.
    - apply (real_le_mult_compat_r T real_zero (real_plus E1 real_one) HTle).
      exact (RealSetoid.real_lt_le_iff_req real_zero (real_plus E1 real_one) (inl HGpos)). }
  apply (RealSetoid.real_le_id_l real_zero (real_mult W real_zero)
                                 (real_mult W (real_mult T (real_plus E1 real_one)))).
  - apply real_eq_sym. apply real_mult_zero.
  - apply (real_le_mult_compat_r W real_zero (real_mult T (real_plus E1 real_one)) HWle).
    exact HTG.
  }
  (* 前提 2：∀ε>0, db ≤ y + C·ε——源件取 eps := eps' := ε，分配律换形 *)
  intros ep Hep.
  set (W := real_inv_pos (real_evicted_partition S keep keep_dec real_energy D D_pos
                             real_sum_over_S) real_evicted_partition_pos) in *.
  set (T := real_transition s s') in *.
  set (E1 := cauchy_real_exp (real_mult (real_inv_pos D D_pos) E_max)) in *.
  set (M2 := real_mult (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s'))
                       (cauchy_real_exp (real_mult (real_mult (real_inv_pos D D_pos) L) (real_metric s s')))) in *.
  set (C := real_mult W (real_mult T (real_plus E1 real_one))).
  pose proof (real_db_breaking_bound_eps S keep keep_dec real_transition
              real_transition_nonneg real_transition_sym real_energy D D_pos L E_max
              real_metric real_energy_lipschitz real_energy_lower real_sum_over_S
              real_evicted_partition_pos s s' ep ep Hs Hs' Hep Hep) as Hsrc.
  fold W in Hsrc. fold T in Hsrc. fold E1 in Hsrc. fold M2 in Hsrc.
  assert (Hchain1 : real_eq
    (real_mult W (real_mult T (real_plus (real_mult E1 M2) (real_plus (real_mult E1 ep) ep))))
    (real_plus (real_mult W (real_mult T (real_mult E1 M2)))
               (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep))))).
  { apply (real_eq_trans _
             (real_mult W
                (real_plus (real_mult T (real_mult E1 M2))
                           (real_mult T (real_plus (real_mult E1 ep) ep)))) _).
    - apply (RealSetoid.real_eq_mult_compat W _ W _).
      + apply real_eq_refl.
      + apply real_distrib.
    - apply real_distrib. }
  assert (Hchain2 : real_eq
    (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep)))
    (real_mult C ep)).
  { apply (real_eq_trans _
             (real_mult W (real_mult T (real_mult (real_plus E1 real_one) ep))) _).
    - apply (RealSetoid.real_eq_mult_compat W _ W _).
      + apply real_eq_refl.
      + apply (RealSetoid.real_eq_mult_compat T _ T _).
        * apply real_eq_refl.
        * (* (E1·ep)+ep == (E1+1)·ep *)
          apply (real_eq_trans _
                   (real_plus (real_mult E1 ep) (real_mult real_one ep)) _).
          -- apply (RealSetoid.real_eq_plus_compat (real_mult E1 ep) ep
                       (real_mult E1 ep) (real_mult real_one ep)).
             ++ apply real_eq_refl.
             ++ apply (real_eq_trans ep (real_mult ep real_one)
                         (real_mult real_one ep)).
                ** apply real_eq_sym. apply real_mult_one.
                ** apply real_mult_comm.
          -- apply real_distrib_r.
    - apply (real_eq_trans _
               (real_mult W (real_mult (real_mult T (real_plus E1 real_one)) ep)) _).
      + apply (RealSetoid.real_eq_mult_compat W _ W _).
        * apply real_eq_refl.
        * apply real_mult_assoc.
      + apply real_mult_assoc. }
  apply (RealSetoid.real_le_id_r
           (real_db_breaking S keep keep_dec real_transition real_energy D D_pos
                             real_sum_over_S real_evicted_partition_pos s s')
           (real_mult W (real_mult T (real_plus (real_mult E1 M2) (real_plus (real_mult E1 ep) ep))))
           (real_plus (real_mult W (real_mult T (real_mult E1 M2))) (real_mult C ep))).
  - exact (real_eq_trans _ _ _ Hchain1
             (RealSetoid.real_eq_plus_compat
                (real_mult W (real_mult T (real_mult E1 M2)))
                (real_mult W (real_mult T (real_plus (real_mult E1 ep) ep)))
                (real_mult W (real_mult T (real_mult E1 M2)))
                (real_mult C ep)
                (real_eq_refl _) Hchain2)).
  - exact Hsrc.
Qed.

End RealKVQuantLeB.

(* ============================================================ *)

(*                                                                *)
(* 【结论 G1｜非负系数完成器】real_le_closure_b_nonneg：可证。         *)
(*   规格（供未来引擎升级引用）：源完成器 real_le_closure_b 要求系数     *)
(*   正性证书（零小于 D），而多 eps 组合链的复合系数常仅非负——典型：    *)
(*   正量乘非负量（如 invZ·T，其中 T 仅有非负接口）。本器证明：非负      *)
(*   证书即足——见证 e₀ := δ·inv(2)·inv(C+1)（C+1 的正性由 C≥0 与        *)
(*   零小于一构造），C·e₀ 换形后 ≤ δ·inv(2)·((C+1)·inv(C+1))            *)
(*   == δ·inv(2) < δ。零稠密性、零经典、零新增前提。                     *)
(* 【结论 G2｜组合器双件】real_le_b_trans 与 real_le_b_plus_compat：     *)
(*   可证。拆分取 δ·inv(2)（real_inv_two_lt_one 既有）；传递件中项       *)
(*   (z+dh)+dh == z+δ、加法件 (y+dh)+(v+dh) == (y+v)+δ 全经             *)
(*   assoc/comm/leb2_half_add 换形闭合。Bishop 序自此具备传递与加法      *)
(*   组合面：多 eps 项可逐段完成后组合（引擎升级面第二规格）。           *)
(* 【结论 G3｜盘点 #24 real_abs_le_quad_B】可升格（完整）——源件结论     *)
(*   尾带全称 eps 余量（|X| ≤ 2t²+(eps1+eps2)+eps），属 plain-eps 直连   *)
(*   形：eps1/eps2 为前提位固定正量并入右端。one 特化完成单步 + 源件     *)
(*   直连，零新增前提。盘点判 9(e) 的「证书链长」在升格面不成立——        *)
(*   四分支证书链在源件内部已闭合，升格面只使用其出口语句。              *)
(* 【结论 G4｜盘点 #25 real_quad_t_le_h_B】可升格（完整）——源件 eps'    *)
(*   为全称求和余量（自带零小于前提位），one 完成后 eps' 从界内消去：    *)
(*   2(h/x)² ≤_B (1/2)·eps·|h|。余量内嵌 |h| 因子随固定端并入右端。      *)
(* 【结论 G5｜盘点 #28 real_abs_h_sq_le_B】可升格（完整）——同 G4 链型： *)
(*   双余量 (A·eps3)·|h| + eps' 中 eps' 全称消去：A|h|² ≤_B (A·eps3)·|h|。*)
(* 【结论 G6｜盘点 #32 real_db_breaking_bound_B】可升格（完整，非冻结）  *)
(*   ——判 9(f) 设想的复合系数正性路线（invZ·T·exp 作 D）确不可行：      *)
(*   T 仅非负接口，其正性构造性不可证。改走非负系数路线：C :=            *)
(*   invZ·T·(exp+1)，非负性由 invZ>0（接口既有）、T≥0（接口既有）、      *)
(*   exp>0（cauchy_real_exp_pos 既有）逐级组装；源件取 eps := eps' := ε  *)
(*   后分配律换形 db ≤ y + C·ε，F.1 器单步完成。eps 与 eps' 同时消去：   *)
(*   db ≤_B invZ·T·(exp·(L/D·m)·exp(L/D·m))。零新增前提（15 参 discharged *)
(*   前缀照抄源件，节变量对偶声明）。                                    *)
(* 【核对】盘点清单显式假设 4 件（#24/25/28/32）全部升格落盘本文件。         *)

(*   == 二十九件 Bishop 形；余七件为冻结族（结论 9(a)-(d)），形态不匹配 *)


(*   Obj.magic 计数为零（检验验后删）；G4 认证 9.0 同平台通过。           *)
(*   全件 Print Assumptions Closed（见文末）。                           *)
(* ============================================================ *)

Print Assumptions leb2_half_add.
Print Assumptions real_le_closure_b_nonneg.
Print Assumptions real_le_b_trans.
Print Assumptions real_le_b_plus_compat.
Print Assumptions real_abs_le_quad_B.
Print Assumptions real_quad_t_le_h_B.
Print Assumptions real_abs_h_sq_le_B.
Print Assumptions real_db_breaking_bound_B.
