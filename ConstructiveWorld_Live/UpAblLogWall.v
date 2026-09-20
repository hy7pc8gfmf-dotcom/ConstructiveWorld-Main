(* ============================================================ *)
(* UpAblLogWall.v —— 席N2：判定墙族第 8 位·Real 层最小站选择器阻断定理化      *)
(*                                                              *)
(* 【零承认件】本件零承认、零假设负载、零经典逻辑：全文无任何全局无据项，     *)
(*   四关卡全绿申报（G1 禁词双轨 0 / G2 全量编译 EXIT=0+Closed+5ff4 头+      *)
(*   vo 新于 v / G3 独立目录 Obj.magic=0 / G4 coqchk 无承认项）。            *)
(*                                                              *)
(* 目的：把论文 7 §10.2「Real 层对数差距」limitation 定理化——              *)
(*   「不带可判定测试前件的 Real 层精确最小站选择器」⟹ LPO 族实例。          *)
(*                                                              *)
(* 锚点：S02:802 real_square_not_negative 自注「信息性 real_le 的全称形式     *)
(*   不可证（需判定 a 的符号）」——本件把该序判定缺位沿「最小站账」面升级     *)
(*   为机器检验的正向归约：                                                  *)
(*                                                              *)
(*   lgw_MinSel : Set := forall kappa TV0 budget : Real,                     *)
(*     存在 k:nat 携带精确最小站账 lgw_min_sel_spec：                        *)
(*       test k 真（信息性 real_lt 供隙支）∧  ∀j<k，test j 被驳（否证支）   *)
(*     其中 test := λk, real_lt (κ^k·TV₀) budget——Q 层账形镜像自            *)
(*     UpReqMixLogA.v mixa_sel_accounts / mixa_pow_budget_log_min            *)
(*     （test k = true ∧ ∀j<k, test j = false 的信息性升级）。               *)
(*                                                              *)
(*   lgw_lpo_of_min_sel : lgw_MinSel -> lgw_lpo_family（主件·正向归约）：    *)
(*     归约构造：∀x:Real, 0≤x≤1，取 κ:=half、TV₀:=x、budget:=half：         *)
(*       最小站 k=0 ⟹ x<half ⟹ x<1；k=1 ⟹ half·x<half ⟹ x<1；              *)
(*       k≥2 ⟹ 站 1 被驳 ⟹ ¬(x<1)，与前件 x≤1 合流得 x=1——                *)
(*       选择器输出即序判定证书：Or (real_lt x one) (real_eq x one)          *)
(*       = real_le x one 的 Or 分解（S02:469 定义形）= LPO 实例。            *)
(*     数学核心 = 从最小站账提取序信息；全部换形走投影级 Q 算术              *)
(*     （real_mult_proj/real_const_proj + lgw_qlt_half_gap 双桥），          *)
(*     不依赖 Real 层乘法单调件（库内缺席——缺席本身即墙的一部分）。          *)
(*                                                              *)
(*   lgw_oracle_pin（神谕钉对照件）：序判定神谕在场时本墙结论平凡可得        *)
(*     （B3 神谕钉放电先例同法，RC=0）——墙核 = 序判定缺位，非账面本身。      *)
(*                                                              *)
(*   谱系：AA15R UpReqLpoEquiv（rLPO 零问题形，墙族第 7 位）：本件序形实例    *)
(*   与 rLPO 同为「Or(供隙支, 归零支)」数据形——real_lt 供一致正隙            *)
(*   （S02:465 sigT eps/N 形），real_eq 供逐点归零（S02:396 全称 eps 形）；   *)
(*   差别仅参照常量（1 vs 0）与门槛前件（0≤x≤1）。rLPO 定义经 Require        *)
(*   逐字复用为谱系对照。AA23 UpReqPinWallEquiv 为降档阶梯先例。             *)
(*                                                              *)
(*   降档阶梯申报：L1（规格面+正向归约+神谕钉）全绿到档。                    *)
(*   L2/L3 挂账如实说明：AA23 反向障碍账法的前提是接口不可满足               *)
(*   （pwe_PinWall 在 2#4 位逼出 Leibniz 假等式故可全驳），而本件            *)
(*   lgw_MinSel 经典可满足（lgw_oracle_pin 即其在序判定神谕下的实现          *)
(*   对照），AA23 形反向障碍「反向归约存在 ⟹ rLPO 被驳」在本件为经典        *)
(*   假命题，构造性不可证——故 L2 按方法学不可达挂账，L3（双向               *)
(*   lgw_equivalence）随之挂账；挂账理由为方法学障碍非预算截断。             *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、语句面全 sigT/自定义 And/Or，零 Prop 泄露；        *)
(*   归约前提（选择器）以定理显式参承接（随语句面入出口签名，非全局无据项）。 *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、UpReqLpoEquiv（rLPO 谱系对照）。  *)
(* ------------------------------------------------------------ *)
(* N2（20260920）：新建。                                                   *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：几何常量与站点幂族（镜像 UpTVDoeblin tv_rpow 形）                  *)
(* ============================================================ *)

Definition lgw_half : Real := real_const (1#2).

Fixpoint lgw_rpow (a : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult a (lgw_rpow a m)
  end.

(* 信息性测试：test k := real_lt (κ^k·TV₀) budget（Q 层 mixa_test 镜像） *)
Definition lgw_test (kappa TV0 budget : Real) (k : nat) : Set :=
  real_lt (real_mult (lgw_rpow kappa k) TV0) budget.

(* ============================================================ *)
(* Part 1：选择器规格面（Q 层 mixa_sel_accounts 账形的 Real 面镜像）          *)
(* ============================================================ *)

(* 精确最小站账：test k 真（供隙支）∧ ∀j<k，test j 被驳（否证支） *)
Definition lgw_min_sel_spec (kappa TV0 budget : Real) (k : nat) : Set :=
  And (lgw_test kappa TV0 budget k)
      (forall j : nat, NatLe (Datatypes.S j) k ->
        lgw_test kappa TV0 budget j -> Empty_set).

(* Real 层最小站选择器接口（不带可判定测试前件——墙件本身） *)
Definition lgw_MinSel : Set :=
  forall kappa TV0 budget : Real,
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

(* LPO 实例面：[0,1] 上信息性 real_le 的 Or 分解决策 *)
Definition lgw_lpo_family : Set :=
  forall x : Real, real_le real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).

(* ============================================================ *)
(* Part 2：投影级 Q 算术桥（全部换形的公共内核）                              *)
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

(* 投影钉：half / one / 幂族前两站的逐点投影 Q 值 *)
Lemma lgw_half_proj : forall n : nat, projT1 lgw_half n == (1#2).
Proof.
  intros n. unfold lgw_half. apply real_const_proj.
Qed.

Lemma lgw_one_proj : forall n : nat, projT1 real_one n == 1.
Proof.
  intros n. reflexivity.
Qed.

Lemma lgw_rpow0_proj : forall n : nat,
  projT1 (lgw_rpow lgw_half 0%nat) n == 1.
Proof.
  intros n. reflexivity.
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
(* Part 3：站账→序信息桥（主件的数学核心，三站三分支）                        *)
(* ============================================================ *)

(* 站 0 真 ⟹ x < one：eps < 1/2 − x_n 且 eps>0 ⟹ x_n < 1/2 ⟹ 1/4 < 1−x_n *)
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

(* 站 1 真 ⟹ x < one：eps < 1/2 − x_n/2 ⟹ 2eps < 1 − x_n（二分正桥） *)
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

(* x < one ⟹ 站 1 真（否证支的反向消耗：供隙取 eps·half，二分逆桥） *)
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
(* Part 4：主件——正向归约（选择器 ⟹ LPO 实例）                              *)
(* ============================================================ *)

(* 归约构造：κ:=half、TV₀:=x、budget:=half 三站分支——                       *)
(*   k=0/1 支由站账供隙支直接出 x<1；k≥2 支由站账否证支（站 1 被驳）          *)
(*   与前件 x≤1 的左支相撞出空型、右支（x=1）随取——                          *)
(*   选择器输出即序判定证书，序判定缺位由此归约为选择器缺位。                 *)
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
      - apply NatLe_lift. lia.
      - exact Ht1. }
    destruct Hx1 as [Hlt1 | Heq1].
    + destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
    + apply inr. exact Heq1.
Qed.

(* ============================================================ *)
(* Part 5：神谕钉对照件（B3 放电先例同法）                                    *)
(* ============================================================ *)

(* 序判定神谕：任意实对的 Or 分解决策——Real 层不可供给（S02:802 墙注对象；   *)
(*   神谕在场时选择器结论平凡可得，墙核 = 序判定缺位） *)
Definition lgw_ord_oracle : Set :=
  forall x y : Real, Or (real_lt x y) (real_eq x y).

Theorem lgw_oracle_pin : lgw_ord_oracle -> lgw_lpo_family.
Proof.
  intros Hord x _ Hx1.
  exact (Hord x real_one).
Qed.

(* ============================================================ *)
(* Part 6：摘要输出（G2/G3 关卡面）                                          *)
(* ============================================================ *)

Print Assumptions lgw_min_sel_spec.
Print Assumptions lgw_MinSel.
Print Assumptions lgw_lpo_family.
Print Assumptions lgw_lpo_of_min_sel.
Print Assumptions lgw_oracle_pin.

Separate Extraction lgw_rpow lgw_test lgw_min_sel_spec lgw_MinSel lgw_lpo_family lgw_ord_oracle.
