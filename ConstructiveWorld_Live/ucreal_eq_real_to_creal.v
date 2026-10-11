(* ================================================================== *)
(* ucreal_eq_real_to_creal.v —— 库实数相等到标准库 CReal 相等的传输   *)
(*                                                                    *)
(* 数学使命：库构造实数的相等 real_eq（同深度指标交叉逼近）传输为     *)
(*       标准库 CReal 相等 CRealEq（双向无正间隙形）。                *)
(* 证明结构：固定取样深度 j = |n|，两转换序列值各自落在单调模量       *)
(*       包络 ucreal_mod 选出的稳定尾段内；real_eq 提供任意精度的     *)
(*       交叉项界，三角不等式合成逐点一致界                           *)
(*       |seq x n - seq y n| <= 2*2^n（n >= 0 侧阈值宽松，n < 0 侧   *)
(*       由 2^(-|n|) 指数恒等式 ucreal_pow2_neg_eq 与单调性           *)
(*       ucreal_pow2_le_mono 对齐阈值）；再经标准库 CRealEq_diff      *)
(*       的逐点绝对值特征一步组合出 CRealEq。                         *)
(* 依赖：标准库 QArith、Qabs、ZArith、Lia、Lqa、                      *)
(*       ConstructiveCauchyReals（CRealEq_diff 定义面）；库内         *)
(*       ucreal_bridge（ucreal_of_real/ucreal_mod_spec/幂函数族）、    *)
(*       S02_CauchyComplete（real_eq/real_eq_sym）。                  *)
(* 对标：Stdlib.Reals.Cauchy.ConstructiveCauchyReals (CRealEq_diff)   *)
(* 构造性注记：零公理、零承认件、零经典逻辑。逐点界由 Qlt_le_dec      *)
(*       可判定二分与构造性 epsilon 论证得出：超阈值分支以            *)
(*       delta/4 精度见证与三角不等式导出矛盾，全程不引入排中律。     *)
(*       主语句使用标准库 CRealEq（其 Prop 承载系标准库自身定义面）。 *)
(* 编译配方：coqc -native-compiler no -q -Q world "" world\ucreal_eq_real_to_creal.v *)
(* ================================================================== *)

From Stdlib Require Import QArith.
From Stdlib Require Import Qpower.
From Stdlib Require Import Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import ucreal_bridge.

(* ================================================================== *)
(* Section 1. One-sided pointwise bound from real_eq.                 *)
(* ================================================================== *)

Lemma ucreal_eq_one_sided_le :
  forall X Y : Real, real_eq X Y ->
    forall n : Z,
      (seq (ucreal_of_real X) n - seq (ucreal_of_real Y) n
       <= 2 * 2 ^ n)%Q.
Proof.
  intros X Y Heq n.
  destruct X as [ux cx]. destruct Y as [uy cy].
  assert (Hsx : forall n0 : Z,
            seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) ux cx)) n0
            = ux (ucreal_mod ux cx (Z.to_nat (Z.abs n0))))
    by (intros; reflexivity).
  assert (Hsy : forall n0 : Z,
            seq (ucreal_of_real (existT (fun u : Qseq => cauchy u) uy cy)) n0
            = uy (ucreal_mod uy cy (Z.to_nat (Z.abs n0))))
    by (intros; reflexivity).
  rewrite (Hsx n), (Hsy n).
  remember (Z.to_nat (Z.abs n)) as j eqn:Hjdef.
  set (mx := ucreal_mod ux cx j) in *.
  set (my := ucreal_mod uy cy j) in *.
  destruct (Qlt_le_dec (2 * 2 ^ n) (ux mx - uy my)%Q) as [Hgt | Hdone].
  - (* strictly above the threshold: contradiction by epsilon squeeze *)
    exfalso.
    assert (Hdelta : (0 < (ux mx - uy my) - 2 * 2 ^ n)%Q) by lra.
    assert (Hposq : QltT 0 (((ux mx - uy my) - 2 * 2 ^ n) * (1 # 4))%Q).
    { apply Qlt_to_QltT. lra. }
    destruct (Heq _ Hposq) as [N3 HN3].
    cbn [projT1] in HN3.
    set (m := Nat.max (Nat.max mx my) N3).
    assert (Hmxm : (mx <= m)%nat) by lia.
    assert (Hmym : (my <= m)%nat) by lia.
    assert (HNm : (N3 <= m)%nat) by lia.
    pose proof (ucreal_mod_spec ux cx j mx m (Nat.le_refl _) Hmxm) as Htx.
    pose proof (ucreal_mod_spec uy cy j my m (Nat.le_refl _) Hmym) as Hty.
    pose proof (HN3 m (NatLe_lift _ _ HNm)) as Hxy.
    apply QltT_to_Qlt in Htx. apply Qabs_Qlt_condition in Htx.
    destruct Htx as [Htx1 Htx2].
    apply QltT_to_Qlt in Hty. apply Qabs_Qlt_condition in Hty.
    destruct Hty as [Hty1 Hty2].
    apply QltT_to_Qlt in Hxy. apply Qabs_Qlt_condition in Hxy.
    destruct Hxy as [Hxy1 Hxy2].
    assert (Hepsj : (ucreal_eps j <= 2 ^ n)%Q).
    { assert (HjZ : Z.of_nat j = Z.abs n).
      { rewrite Hjdef. apply Z2Nat.id. apply Z.abs_nonneg. }
      assert (Hpowpos : (0 < 2 ^ n)%Q)
        by (apply Qpower_0_lt; unfold Qlt, Qnum, Qden; lia).
      pose proof (Qeq_sym _ _ (ucreal_pow2_neg_eq j)) as Hleft.
      rewrite HjZ in Hleft.
      destruct (Z_le_gt_dec 0 n) as [Hn | Hn].
      - assert (Habsn : Z.abs n = n) by (apply Z.abs_eq; lia).
        rewrite Habsn in Hleft.
        assert (Hmid : (2 ^ Z.opp n <= 2 ^ n)%Q)
          by (apply ucreal_pow2_le_mono; lia).
        lra.
      - assert (Habsn : Z.abs n = Z.opp n) by (apply Z.abs_neq; lia).
        rewrite Habsn in Hleft.
        rewrite Z.opp_involutive in Hleft.
        lra. }
    lra.
  - exact Hdone.
Qed.

(* ================================================================== *)
(* Section 2. Absolute-value pointwise bound (both signs).            *)
(* ================================================================== *)

Lemma ucreal_eq_pointwise_abs_le :
  forall X Y : Real, real_eq X Y ->
    forall n : Z,
      (Qabs (seq (ucreal_of_real X) n - seq (ucreal_of_real Y) n)
       <= 2 * 2 ^ n)%Q.
Proof.
  intros X Y Heq n. apply Qabs_Qle_condition. split.
  - pose proof (ucreal_eq_one_sided_le Y X (real_eq_sym X Y Heq) n) as H.
    lra.
  - exact (ucreal_eq_one_sided_le X Y Heq n).
Qed.

(* ================================================================== *)
(* Section 3. The equality transport theorem.                         *)
(* ================================================================== *)

Theorem ucreal_eq_real_to_creal :
  forall X Y : Real, real_eq X Y ->
    CRealEq (ucreal_of_real X) (ucreal_of_real Y).
Proof.
  intros X Y Heq.
  apply (proj2 (CRealEq_diff (ucreal_of_real X) (ucreal_of_real Y))).
  intro n. exact (ucreal_eq_pointwise_abs_le X Y Heq n).
Qed.

(* ================================================================== *)
(* Section 4. Verification probes.                                    *)
(* ================================================================== *)

Print Assumptions ucreal_eq_one_sided_le.
Print Assumptions ucreal_eq_pointwise_abs_le.
Print Assumptions ucreal_eq_real_to_creal.

From Stdlib Require Import Extraction.
Extraction "ucreal_eq_real_to_creal_extract.ml" ucreal_of_real.
