(* ============================================================ *)
(* UpAblLogWall.v —— 最小站选择器到 LPO 族实例的正向归约（Real 层对数差距的定理化） *)
(*                                                              *)
(* 使命：本件形式化「不带可判定测试前提的 Real 层精确最小站选择器」与          *)
(*   LPO 族实例之间的正向归约——「Real 层对数差距」限制的定理化。              *)
(*   限制的根源（参 S02_CauchyComplete 的 real_square_not_negative 注记）：    *)
(*   信息性序的全称形式不可证——序判定需先判定元素的符号；本件把该缺位         *)
(*   转化为显式正向归约。                                                     *)
(*                                                              *)
(* 规格：lgw_MinSel : Set := forall kappa TV0 budget : Real，供给             *)
(*   k:nat 携带精确最小站规格 lgw_min_sel_spec：                              *)
(*     test k 成立（供隙支）∧ ∀j<k，test j 被驳（否证支），                   *)
(*   其中 test := λk, real_lt (κ^k·TV₀) budget——语句形复现自                  *)
(*   UpReqMixLogA.v 的 mixa_sel_accounts / mixa_pow_budget_log_min（Q 层      *)
(*   为布尔测试形，本件为其信息性序测试强化）。                               *)
(*                                                              *)
(* 主定理 lgw_lpo_of_min_sel : lgw_MinSel -> lgw_lpo_family（正向归约）：      *)
(*   归约构造：∀x:Real, 0≤x≤1，取 κ:=half、TV₀:=x、budget:=half：            *)
(*   最小站 k=0 ⟹ x<half ⟹ x<1；k=1 ⟹ half·x<half ⟹ x<1；                    *)
(*   k≥2 ⟹ 站 1 被驳 ⟹ ¬(x<1)，与前提 x≤1 合取得 x=1——                      *)
(*   选择器输出即序判定见证：Or (real_lt x one) (real_eq x one)               *)
(*   = real_le x one 的 Or 分解 = LPO 实例。                                  *)
(*   数学核心 = 从最小站规格提取序信息；全部换形走投影级 Q 算术               *)
(*   （real_mult_proj / real_const_proj，配合两个桥接引理                     *)
(*   lgw_qlt_half_gap 与 lgw_qlt_half_gap_inv），不依赖 Real 层乘法           *)
(*   单调性引理——库内缺席本身即此构造性边界的内容。                          *)
(*                                                              *)
(* 对照件 lgw_oracle_pin：lgw_ord_oracle -> lgw_lpo_family——序判定神谕       *)
(*   在场时 LPO 族实例直接可得，对照表明障碍在序判定数据的可得性。           *)
(*                                                              *)
(* 谱系：UpReqLpoEquiv 的 rLPO（零问题形）：本件序形实例与 rLPO 同为          *)
(*   「Or(供隙支, 归零支)」数据形——real_lt 供一致正隙（sigT eps/N 形），       *)
(*   real_eq 供逐点归零（全称 eps 形）；差别仅参照常量（1 vs 0）与            *)
(*   门槛前提（0≤x≤1）。rLPO 定义经 Require 逐字复用为谱系对照。              *)
(*                                                              *)
(* 未竟项如实说明（经 UpAblLogWallEq 的 lgwe_minsel_refutable 精化）：       *)
(*   全称无前提接口 lgw_MinSel 为空集——取 kappa=TV0=budget=real_one 时       *)
(*   最小站不存在（test 逐站可驳），lgw_MinSel -> Empty_set 为闭项定理，     *)
(*   故无条件下双向等价不可达；条件化等价见 UpAblLogWallEq 的 lgwe_equivalence。 *)
(*                                                              *)
(* 构造性注记：纯构造性 Set 层承载，语句面全 sigT/自定义 And/Or，零承认，      *)
(*   零 Prop 泄露；归约前提（选择器）以定理显式参承接（随语句面入出口         *)
(*   签名，非全局无据项）。                                                   *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、UpReqLpoEquiv（rLPO 谱系对照）。    *)
(* 对标：stdlib QArith（Q 上序与线性算术）；mathlib 无构造性对应物。          *)
(* 编译配方：Rocq 9.1 直调 coqc + cpu_guard（-LoadLimit 85 -CoreN 2），       *)
(*   输出至临时目录，树内零写入。                                             *)
(* 结构：§0 几何常量与站点幂族；§1 选择器规格；§2 投影级 Q 算术桥接引理；     *)
(*   §3 站点规格→序信息桥；§4 主定理正向归约；§5 序判定神谕对照件；           *)
(*   §6 假设审计与提取出口。三站转换引理：lgw_test0_lt_one、                   *)
(*   lgw_test1_lt_one、lgw_test1_of_lt_one。                                  *)
(* ------------------------------------------------------------ *)
(*                                                              *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 几何常量与站点幂族（复现 UpTVDoeblin 的 tv_rpow 形）                    *)
(* ============================================================ *)

Definition lgw_half : Real := real_const (1#2).

Fixpoint lgw_rpow (a : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult a (lgw_rpow a m)
  end.

(* 信息性测试：test k := real_lt (κ^k·TV₀) budget（Q 层 mixa_test 的同形复现） *)
Definition lgw_test (kappa TV0 budget : Real) (k : nat) : Set :=
  real_lt (real_mult (lgw_rpow kappa k) TV0) budget.

(* ============================================================ *)
(* §1 选择器规格（Q 层 mixa_sel_accounts 语句形的 Real 层对应件）             *)
(* ============================================================ *)

(* 精确最小站规格：test k 成立（供隙支）∧ ∀j<k，test j 被驳（否证支）         *)
Definition lgw_min_sel_spec (kappa TV0 budget : Real) (k : nat) : Set :=
  And (lgw_test kappa TV0 budget k)
      (forall j : nat, NatLe (Datatypes.S j) k ->
        lgw_test kappa TV0 budget j -> Empty_set).

(* Real 层最小站选择器接口（不带可判定测试前提——构造性边界所在）             *)
Definition lgw_MinSel : Set :=
  forall kappa TV0 budget : Real,
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

(* LPO 实例面：[0,1] 上信息性 real_le 的 Or 分解决策 *)
Definition lgw_lpo_family : Set :=
  forall x : Real, real_le real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).

(* ============================================================ *)
(* §2 投影级 Q 算术桥接引理（全部换形的公共内核）                             *)
(* ============================================================ *)

(* 二分正桥：eps < 1/2 − z/2 ⟹ 2eps < 1 − z（Qmult_lt_compat_r ×2 + ring） *)
Lemma lgw_qlt_half_gap : forall eps z : Q,
  Qlt eps ((1#2) - (1#2) * z) -> Qlt (eps + eps) (1 - z).
Proof.
  intros eps z H.
  assert (Hq2 : Qlt 0 (2#1)) by (apply (proj2 (Qlt_alt 0 (2#1))); reflexivity).
  assert (Hm : eps * (2#1) < ((1#2) - (1#2) * z) * (2#1))
    by (apply Qmult_lt_compat_r; assumption).
  assert (Hr1 : ((1#2) - (1#2) * z) * (2#1) == 1 - z) by ring.
  assert (Hr2 : eps * (2#1) == eps + eps) by ring.
  rewrite Hr2 in Hm. rewrite Hr1 in Hm. exact Hm.
Qed.

(* 二分逆桥：eps < 1 − z ⟹ eps/2 < 1/2 − z/2（Qmult_lt_compat_r + ring） *)
Lemma lgw_qlt_half_gap_inv : forall eps z : Q,
  Qlt eps (1 - z) -> Qlt (eps * (1#2)) ((1#2) - (1#2) * z).
Proof.
  intros eps z H.
  assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
  assert (Hm : eps * (1#2) < (1 - z) * (1#2))
    by (apply Qmult_lt_compat_r; assumption).
  assert (Hr1 : (1 - z) * (1#2) == (1#2) - (1#2) * z) by ring.
  rewrite Hr1 in Hm. exact Hm.
Qed.

(* 投影引理：lgw_half / real_one / 幂族前两站的逐点投影 Q 值                  *)
Lemma lgw_half_proj : forall n : nat, projT1 lgw_half n == (1#2).
Proof.
  intros n. unfold lgw_half. apply real_const_proj.
Qed.

Lemma lgw_one_proj : forall n : nat, projT1 real_one n == 1.
Proof.
  intros n. exact (Qeq_refl (projT1 real_one n)).
Qed.

Lemma lgw_rpow0_proj : forall n : nat,
  projT1 (lgw_rpow lgw_half 0%nat) n == 1.
Proof.
  intros n. exact (Qeq_refl (projT1 (lgw_rpow lgw_half 0%nat) n)).
Qed.

Lemma lgw_rpow1_proj : forall n : nat,
  projT1 (lgw_rpow lgw_half 1%nat) n == (1#2).
Proof.
  intros n.
  cbn [lgw_rpow].
  rewrite (real_mult_proj lgw_half real_one n).
  rewrite (lgw_half_proj n).
  rewrite (lgw_one_proj n).
  reflexivity.
Qed.

(* ============================================================ *)
(* §3 站点规格→序信息桥（主定理的数学核心，三站三分支）                       *)
(* ============================================================ *)

(* 站 0 成立 ⟹ x < one：eps < 1/2 − x_n 且 eps>0 ⟹ x_n < 1/2 ⟹ 1/4 < 1−x_n  *)
Lemma lgw_test0_lt_one : forall x : Real,
  lgw_test lgw_half x lgw_half 0%nat -> real_lt x real_one.
Proof.
  intros x Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  unfold real_lt.
  exists (1#4). split.
  - apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (real_mult_proj (lgw_rpow lgw_half 0%nat) x n) in HN.
    rewrite (lgw_rpow0_proj n) in HN.
    rewrite (lgw_half_proj n) in HN.
    rewrite (lgw_one_proj n).
    assert (Hn1 : 1 * projT1 x n == projT1 x n) by ring.
    rewrite Hn1 in HN.
    assert (Hnn : Qlt 0 ((1#2) - projT1 x n)).
    { apply Qlt_trans with eps; assumption. }
    assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
    assert (Hadr : (1#2) + 0 < (1#2) + ((1#2) - projT1 x n)).
    { exact (proj2 (Qplus_lt_r 0%Q ((1#2) - projT1 x n) (1#2)) Hnn). }
    rewrite (Qplus_0_r (1#2)) in Hadr.
    assert (Hr : 1 - projT1 x n == (1#2) + ((1#2) - projT1 x n)) by ring.
    rewrite Hr.
    apply Qlt_trans with (1#2).
    + apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
    + exact Hadr.
Qed.

(* 站 1 成立 ⟹ x < one：eps < 1/2 − x_n/2 ⟹ 2eps < 1 − x_n（二分正桥）       *)
Lemma lgw_test1_lt_one : forall x : Real,
  lgw_test lgw_half x lgw_half 1%nat -> real_lt x real_one.
Proof.
  intros x Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  unfold real_lt.
  exists (eps + eps). split.
  - apply Qlt_to_QltT.
    assert (Hq2 : Qlt 0 (2#1)) by (apply (proj2 (Qlt_alt 0 (2#1))); reflexivity).
    assert (Hm0 : 0 * (2#1) < eps * (2#1))
      by (apply Qmult_lt_compat_r; assumption).
    rewrite Qmult_0_l in Hm0.
    assert (Hr2 : eps * (2#1) == eps + eps) by ring.
    rewrite <- Hr2. exact Hm0.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (real_mult_proj (lgw_rpow lgw_half 1%nat) x n) in HN.
    rewrite (lgw_rpow1_proj n) in HN.
    rewrite (lgw_half_proj n) in HN.
    rewrite (lgw_one_proj n).
    exact (lgw_qlt_half_gap eps (projT1 x n) HN).
Qed.

(* x < one ⟹ 站 1 成立（反向方向：供隙取 eps·half，由 lgw_qlt_half_gap_inv）  *)
Lemma lgw_test1_of_lt_one : forall x : Real,
  real_lt x real_one -> lgw_test lgw_half x lgw_half 1%nat.
Proof.
  intros x Hlt.
  unfold lgw_test, real_lt.
  destruct Hlt as [eps [Heps [N HN]]].
  apply QltT_to_Qlt in Heps.
  exists (eps * (1#2)). split.
  - apply Qlt_to_QltT.
    assert (Hqh : Qlt 0 (1#2)) by (apply (proj2 (Qlt_alt 0 (1#2))); reflexivity).
    assert (Hm0 : 0 * (1#2) < eps * (1#2))
      by (apply Qmult_lt_compat_r; assumption).
    rewrite Qmult_0_l in Hm0.
    exact Hm0.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (lgw_one_proj n) in HN.
    rewrite (real_mult_proj (lgw_rpow lgw_half 1%nat) x n).
    rewrite (lgw_rpow1_proj n).
    rewrite (lgw_half_proj n).
    exact (lgw_qlt_half_gap_inv eps (projT1 x n) HN).
Qed.

(* ============================================================ *)
(* §4 主定理——正向归约（选择器 ⟹ LPO 实例）                                  *)
(* ============================================================ *)

(* 归约构造：κ:=half、TV₀:=x、budget:=half 三站分支——                       *)
(*   情形 k=0/1 由供隙支直接得 x<1；情形 k≥2 由否证支（站 1 被驳）            *)
(*   与前提 x≤1 的左支矛盾得空型、右支（x=1）直接取——                        *)
(*   选择器输出即序判定见证，序判定缺位由此归约为选择器缺位。                 *)
Theorem lgw_lpo_of_min_sel : lgw_MinSel -> lgw_lpo_family.
Proof.
  intros Hsel x Hz Hx1.
  destruct (Hsel lgw_half x lgw_half) as [k Hacc].
  destruct Hacc as [Htk Hbel].
  destruct k as [| [| m]].
  - apply inl. exact (lgw_test0_lt_one x Htk).
  - apply inl. exact (lgw_test1_lt_one x Htk).
  - assert (Href1 : lgw_test lgw_half x lgw_half 1%nat -> Empty_set).
    { intros Ht1. apply (Hbel 1%nat).
      - apply NatLe_lift. apply le_n_S. apply le_n_S. apply le_0_n.
      - exact Ht1. }
    destruct Hx1 as [Hlt1 | Heq1].
    + destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
    + apply inr. exact Heq1.
Qed.

(* ============================================================ *)
(* §5 序判定神谕对照件                                                       *)
(* ============================================================ *)

(* 序判定神谕：任意实对的 Or 分解决策——Real 层不可供给（参                   *)
(*   S02_CauchyComplete 的 real_square_not_negative 注记；神谕在场时结论直接可得，不可构造性核心 = 序判定缺位） *)
Definition lgw_ord_oracle : Set :=
  forall x y : Real, Or (real_lt x y) (real_eq x y).

Theorem lgw_oracle_pin : lgw_ord_oracle -> lgw_lpo_family.
Proof.
  intros Hord x _ Hx1.
  exact (Hord x real_one).
Qed.

(* ============================================================ *)
(* §6 假设审计与提取出口                                                     *)
(* ============================================================ *)

Print Assumptions lgw_min_sel_spec.
Print Assumptions lgw_MinSel.
Print Assumptions lgw_lpo_family.
Print Assumptions lgw_lpo_of_min_sel.
Print Assumptions lgw_oracle_pin.

Separate Extraction lgw_rpow lgw_test lgw_min_sel_spec lgw_MinSel lgw_lpo_family lgw_ord_oracle.
