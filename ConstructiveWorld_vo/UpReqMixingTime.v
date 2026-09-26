(* UpReqMixingTime.v —— 显式 k 选取的混合时间定理                    *) (* 使命：转移核混合时间的显式构造：给定谱隙参数 κ（0<κ<1）、初值      *)
(*   偏差 TV₀ 与精度预算 budget，构造显式自然数步数 k 使              *) (*   TV(K^k μ, K^k ν) < budget（sigT 见证，Defined 可计算）。          *)
(*   本件亦为 GibbsAttractor 诚实边界「率件齐备只缺 ln/ceil」缺口的   *) (*   构造性闭合：ln/ceil 的 Nat-枚举+Archimedean 显式替身。            *)
(* 依赖（只 Require 三件授权绿盘件 + 基座伞壳）：                      *) (*   基座 CW_ConstructiveWorld_219（S01-S15 Export 伞壳）：            *)
(*     real_arch（S07:2772 Real 层 Archimedean，显式 nat 见证）、        *) (*     real_mult_div（S08:79）、real_distrib（S02:2384）、               *)
(*     real_distrib_r（S09:120）、real_mult_lt_compat（S07:5979）、       *) (*     real_le_mult_compat（S07:6800）、real_inv_pos 族（S02）、          *)
(*     Nat2Z.inj_succ（ZArith，const-succ 桥的 Z 支路）。                   *) (*   A 件 UpTVDoeblin：tv_rpow/tv_titer/tv_doeblin/tv_step、             *)
(*     tv_doeblin_iter（:1573 TV(Kⁿμ,Kⁿν) ≤ (1−δ)ⁿ·TV₀ 主迭代引理）、      *) (*     tv_omd/_pos_of_lt/_nonneg/_eq_zero（率 κ := 1−δ 证书族）。         *)
(*   R2 件 UpReqIterGeomRate：igr_lt_plus_r / igr_le_plus_r             *) (*     （严格正 d 的 x ▹ x+d 序平移，:185/:197）。                        *)
(* 本件承载（前缀 mix_，全树 grep 零撞名）：                             *) (*   ① mix_scale / mix_const_succ / mix_const_zero /                    *)
(*      mix_scale_eq_const / mix_scale_mult_distrib ——                   *) (*      nat-尺度（迭代和 k·w）与 const-尺度（(k#1)·w）双向桥，            *)
(*      消解 real_arch 输出 real_const (Z.of_nat k #1) 与 Nat 层          *) (*      枚举尺度的会合（Nat2Z.inj_succ + Q 环运算）。                     *)
(*   ② mix_bernoulli_upper —— Bernoulli 上形式                           *) (*      (1−w)^k·(1+k·w) ≤ 1（0<w<1；归纳；纯 Real 环运算，零 exp/log）。  *)
(*   ③ mix_le_inv —— A·B ≤ 1 ∧ 0<B ⟹ A ≤ 1/B（逆元支路）。                *) (*   ④ mix_pow_budget —— k 选取主定理：0<κ<1 ∧ 0<TV₀ ∧ 0<budget          *)
(*      ⟹ sigT (fun k:nat => κ^k·TV₀ < budget)；k := real_arch 在预算    *) (*      实数 TV₀·(1/(w·budget))（w:=1−κ）上解出的显式 nat，Defined        *)
(*      可提取。此即「显式 ln/ceil 的构造性替身」。注：CW220_Extensions   *) (*      .v:1025 r_arch_pow_real 为 abstract r_pow 层同形先例（本件未      *)
(*      Require CW220，自建于 tv_rpow 层，含 ⑤⑥ 的 TV/混合组装）。        *) (*   ⑤ mix_k_select / mix_k_select_le —— TV₀ 非负（Or 逐支）放宽形：      *)
(*      TV₀==0 支 k:=0 一步闭合；lt 支归 ④；le 形经 Or 左支。              *) (*   ⑥ mix_time_explicit —— 混合时间主定理：Section MixingTV              *)
(*      （TVRealWorld 环境共 9+1 变量）内：tv_doeblin_iter × ④ 组装，     *) (*      sigT k ∧ TV(K^k μ, K^k ν) < budget（严格 real_lt 形）；           *)
(*      δ=1 支与 TV₀==0 支 k:=1 一步闭合；+ le 形推论。                    *)
(*   ⑦ mix_k_calc —— Defined k-计算器（见证提取口）。                     *)
(* 公理面：本件零新增公理；全部前提为 Set 层显式证书（real_lt /           *)
(*   real_le Or 编码 / sigT），Print Assumptions 预期全 Closed。          *)
(* 构造性注记：语句面全 Set 层（量词 nat/list Real/函数空间；比较全       *)
(*   real_lt/real_le/real_eq；sigT 第二分量 real_lt : Set）；零 Prop      *)
(*   泄露于签名；零经典逻辑（real_arch/real_lt 均携带构造性见证；         *)
(*   证明内部 Prop 分支仅证明性分情形消去，产物全 Set）；k 选取全程       *)
(*   Defined 可计算（Nat-枚举 = real_arch 显式 nat，非存在性省略）。      *)
(* 编译配方（Rocq 9.1 直调，COQLIB/ROCQLIB 环境变量全字面设置）：         *)
(*   cpu_guard -Command "cmd /c 编译批"（-Q . "" -native-compiler no）     *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
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
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：环运算 tactic（沿用 UpTVDoeblin tvd_rring 口径）与 nat-尺度    *)
(* ============================================================ *)


(* k·w 的 nat-尺度迭代和：mix_scale 0 w = 0，mix_scale (Datatypes.S k) w = w + … *)
Fixpoint mix_scale (k : nat) (w : Real) : Real :=
  match k with
  | Datatypes.O => real_zero
  | Datatypes.S m => real_plus w (mix_scale m w)
  end.

Ltac mix_rring :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with
         | [ x : Real |- _ ] => destruct x
         end;
  cbn [projT1 real_plus real_mult real_opp real_minus_r real_one real_zero
       real_const real_of_nat mix_scale tv_omd] in *;
  ring.

(* 1·x == x（real_mult_one 的左因子换形） *)
Lemma mix_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_one x) (real_mult x real_one) x).
  - exact (real_mult_comm real_one x).
  - exact (real_mult_one x).
Qed.

(* nat-尺度非负性：0 ≤ w ⟹ 0 ≤ k·w *)
Lemma mix_scale_nonneg : forall (w : Real) (k : nat),
  real_le real_zero w -> real_le real_zero (mix_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - apply (RealSetoid.real_eq_le). exact (real_eq_refl real_zero).
  - apply (real_le_trans real_zero (real_plus real_zero real_zero)
             (real_plus w (mix_scale k w))).
    + apply (RealSetoid.real_eq_le).
      exact (real_eq_sym _ _ (real_plus_zero real_zero)).
    + exact (real_le_plus_compat real_zero w real_zero
               (mix_scale k w) Hw IH).
Qed.

(* nat-尺度严格正：0 < w ⟹ 0 < (Datatypes.S k)·w（= w + k·w ≥ w > 0） *)
Lemma mix_scale_S_pos : forall (w : Real) (k : nat),
  real_lt real_zero w -> real_lt real_zero (mix_scale (Datatypes.S k) w).
Proof.
  intros w k Hwp.
  assert (Hnn : real_le real_zero w).
  { apply (RealSetoid.real_lt_le_iff_req real_zero w). left. exact Hwp. }
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus w (mix_scale k w))).
  - apply (real_eq_sym _ _ (real_plus_zero real_zero)).
  - exact (real_lt_plus_compat_lt_le real_zero w real_zero
             (mix_scale k w) Hwp (mix_scale_nonneg w k Hnn)).
Qed.

(* ============================================================ *)
(* Part 1：const-尺度桥（real_arch 输出面 (k#1) ↔ nat-尺度）              *)
(* ============================================================ *)

(* const-零：(0#1) == 0 *)
Lemma mix_const_zero : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof. mix_rring. Qed.

(* const-succ：(Datatypes.S k)#1 == (k#1) + 1（Nat2Z.inj_succ + Q 环运算） *)
Lemma mix_const_succ : forall k : nat,
  real_eq (real_const (Z.of_nat (Datatypes.S k) # 1))
          (real_plus (real_const (Z.of_nat k # 1)) real_one).
Proof.
  intro k. apply real_eq_of_zero_diff. intro n0.
  cbn [projT1 real_const real_plus real_one real_zero] in *.
  replace (Z.of_nat (Datatypes.S k)) with ((Z.of_nat k) + 1)%Z by lia.
  unfold Qminus, Qeq, Qplus, Qmult, Qopp. simpl. ring.
Qed.

(* 主桥：k·w == (k#1)·w（nat-尺度与 const-尺度作为 Real 全等） *)
Lemma mix_scale_eq_const : forall (k : nat) (w : Real),
  real_eq (mix_scale k w) (real_mult (real_const (Z.of_nat k # 1)) w).
Proof.
  intros k. induction k as [| k IH].
  - intro w.
    apply (real_eq_trans real_zero (real_mult real_zero w)
             (real_mult (real_const (Z.of_nat 0 # 1)) w)).
    + apply (real_eq_trans real_zero (real_mult w real_zero)
               (real_mult real_zero w)).
      * exact (real_eq_sym _ _ (real_mult_zero w)).
      * exact (real_eq_sym _ _ (real_mult_comm real_zero w)).
    + apply (RealSetoid.real_eq_mult_compat real_zero w
               (real_const (Z.of_nat 0 # 1)) w
               mix_const_zero (real_eq_refl w)).
  - intro w.
    apply (real_eq_trans (real_plus w (mix_scale k w))
             (real_plus w (real_mult (real_const (Z.of_nat k # 1)) w))).
    + apply (RealSetoid.real_eq_plus_compat w (mix_scale k w) w
               (real_mult (real_const (Z.of_nat k # 1)) w)
               (real_eq_refl w) (IH w)).
    + apply (real_eq_trans
               (real_plus w (real_mult (real_const (Z.of_nat k # 1)) w))
               (real_plus (real_mult real_one w)
                          (real_mult (real_const (Z.of_nat k # 1)) w))).
      * apply (RealSetoid.real_eq_plus_compat w
                 (real_mult (real_const (Z.of_nat k # 1)) w)
                 (real_mult real_one w)
                 (real_mult (real_const (Z.of_nat k # 1)) w)
                 (real_eq_sym _ _ (mix_mult_one_l w))
                 (real_eq_refl (real_mult (real_const (Z.of_nat k # 1)) w))).
      * apply (real_eq_trans
                 (real_plus (real_mult real_one w)
                    (real_mult (real_const (Z.of_nat k # 1)) w))
                 (real_mult (real_plus real_one
                               (real_const (Z.of_nat k # 1))) w)).
        -- exact (real_distrib_r real_one
                     (real_const (Z.of_nat k # 1)) w).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_plus real_one (real_const (Z.of_nat k # 1))) w
                     (real_const (Z.of_nat (Datatypes.S k) # 1)) w
                     (real_eq_trans
                        (real_plus real_one (real_const (Z.of_nat k # 1)))
                        (real_plus (real_const (Z.of_nat k # 1)) real_one)
                        (real_const (Z.of_nat (Datatypes.S k) # 1))
                        (real_plus_comm real_one
                           (real_const (Z.of_nat k # 1)))
                        (real_eq_sym _ _ (mix_const_succ k)))
                     (real_eq_refl w)).
Qed.

(* nat-尺度对右因子的分配：(k·x)·z == k·(x·z) *)
Lemma mix_scale_mult_distrib : forall (k : nat) (x z : Real),
  real_eq (real_mult (mix_scale k x) z) (mix_scale k (real_mult x z)).
Proof.
  intro k. induction k as [| k IH]; intros x z.
  - apply (real_eq_trans (real_mult real_zero z)
             (real_mult z real_zero) real_zero).
    + exact (real_mult_comm real_zero z).
    + exact (real_mult_zero z).
  - apply (real_eq_trans (real_mult (real_plus x (mix_scale k x)) z)
             (real_plus (real_mult x z) (real_mult (mix_scale k x) z))).
    + apply (real_eq_sym _ _ (real_distrib_r x (mix_scale k x) z)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult x z)
               (real_mult (mix_scale k x) z) (real_mult x z)
               (mix_scale k (real_mult x z))
               (real_eq_refl (real_mult x z)) (IH x z)).
Qed.

(* ============================================================ *)
(* Part 2：率证书小件与幂面                                              *)
(* ============================================================ *)

(* δ > 0 ⟹ 1−δ < 1（omd 上界；与 tv_omd_pos_of_lt 对偶） *)
Lemma mix_omd_lt_one : forall delta : Real,
  real_lt real_zero delta -> real_lt (tv_omd delta) real_one.
Proof.
  intros delta Hdelta.
  apply (real_lt_eq_lt (tv_omd delta)
           (real_plus (tv_omd delta) delta) real_one).
  - exact (igr_lt_plus_r (tv_omd delta) delta Hdelta).
  - mix_rring.
Qed.

(* 幂外延：底相等 ⟹ 幂相等 *)
Lemma mix_rpow_eq_compat : forall (x y : Real) (k : nat),
  real_eq x y -> real_eq (tv_rpow x k) (tv_rpow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (real_eq_refl real_one).
  - apply (RealSetoid.real_eq_mult_compat x (tv_rpow x k) y (tv_rpow y k)
             Hxy IH).
Qed.

(* 幂一：a¹ == a *)
Lemma mix_rpow_one : forall a : Real, real_eq (tv_rpow a 1) a.
Proof.
  intro a.
  exact (real_eq_trans (tv_rpow a 1) (real_mult a real_one) a           (real_eq_refl (real_mult a real_one)) (real_mult_one a)).
Qed.

(* 幂正：0 < a ⟹ 0 < a^k *)
Lemma mix_rpow_pos : forall (a : Real) (k : nat),
  real_lt real_zero a -> real_lt real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact real_lt_zero_one.
  - exact (real_mult_pos_compat a (tv_rpow a k) Ha IH).
Qed.

(* 幂非负：0 ≤ a ⟹ 0 ≤ a^k（Or 逐支） *)
Lemma mix_rpow_nonneg : forall (a : Real) (k : nat),
  real_le real_zero a -> real_le real_zero (tv_rpow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - apply (RealSetoid.real_lt_le_iff_req real_zero real_one). left.
    exact real_lt_zero_one.
  - destruct Ha as [Halt | Haq].
    + destruct IH as [IPlt | IPeq].
      * apply (RealSetoid.real_lt_le_iff_req real_zero
                 (real_mult a (tv_rpow a k))). left.
        exact (real_mult_pos_compat a (tv_rpow a k) Halt IPlt).
      * apply (RealSetoid.real_eq_le).
        apply (real_eq_sym _ _).
        apply (real_eq_trans (real_mult a (tv_rpow a k))
                 (real_mult a real_zero) real_zero).
        -- exact (RealSetoid.real_eq_mult_compat a (tv_rpow a k) a
                    real_zero (real_eq_refl a) (real_eq_sym _ _ IPeq)).
        -- exact (real_mult_zero a).
    + apply (RealSetoid.real_eq_le).
      apply (real_eq_sym _ _).
      apply (real_eq_trans (real_mult a (tv_rpow a k))
               (real_mult real_zero (tv_rpow a k)) real_zero).
      * exact (RealSetoid.real_eq_mult_compat a (tv_rpow a k)
                 real_zero (tv_rpow a k) (real_eq_sym _ _ Haq)
                 (real_eq_refl (tv_rpow a k))).
      * apply (real_eq_trans (real_mult real_zero (tv_rpow a k))
                 (real_mult (tv_rpow a k) real_zero) real_zero).
        -- exact (real_mult_comm real_zero (tv_rpow a k)).
        -- exact (real_mult_zero (tv_rpow a k)).
Qed.

(* boost 正性：1 + k·w > 0（0 ≤ w 足矣；k 分支） *)
Lemma mix_boost_pos : forall (w : Real) (k : nat),
  real_le real_zero w ->
  real_lt real_zero (real_plus real_one (mix_scale k w)).
Proof.
  intros w k Hw. destruct k as [| k'].
  - (* k = 0：1+0 == 1 > 0 *)
    apply (real_lt_eq_lt real_zero (real_plus real_one
              (mix_scale 0 w)) real_one).
    + exact real_lt_zero_one.
    + mix_rring.
  - (* k ≥ 1：0+0 < 1+(w+k'·w)（0 < 1 ∧ 0 ≤ w） *)
    apply (RealSetoid.real_lt_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (mix_scale (Datatypes.S k') w))).
    + apply (real_eq_sym _ _ (real_plus_zero real_zero)).
    + exact (real_lt_plus_compat_lt_le real_zero real_one real_zero
               (mix_scale (Datatypes.S k') w) real_lt_zero_one
               (mix_scale_nonneg w (Datatypes.S k') Hw)).
Qed.

(* 泛型原子环件（igr 风格：全析后 simpl+ring；绕开变元停滞不动点的       *)
(*   点级不可归约墙——mix_scale k w 作整体原子入账）                      *)
(* 乘法换位：(a·b)·c == b·(a·c)（eq 组合件链，零 ring） *)
Lemma mix_mult_swap : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult b (real_mult a c)).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_mult (real_mult b a) c)).
  - apply (RealSetoid.real_eq_mult_compat (real_mult a b) c
             (real_mult b a) c (real_mult_comm a b) (real_eq_refl c)).
  - apply (real_eq_sym _ _ (real_mult_assoc b a c)).
Qed.

Lemma mix_ring_cancel : forall A C : Real,
  real_eq (real_plus (real_minus_r A C) C) A.
Proof.
  intros A C. destruct A as [a Ha]. destruct C as [c Hc].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma mix_ring_sc : forall u a : Real,
  real_eq
    (real_mult (real_minus_r real_one u)
       (real_plus real_one (real_plus u a)))
    (real_minus_r (real_plus real_one a)
       (real_mult (real_plus u a) u)).
Proof.
  intros u a. destruct u as [p Hp]. destruct a as [q Hq].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* omd 双重补：x == 1−(1−x) *)
Lemma mix_omd_id : forall x : Real,
  real_eq x (real_minus_r real_one (real_minus_r real_one x)).
Proof.
  intro x. destruct x as [r Hr].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* ============================================================ *)
(* Part 3：Bernoulli 上形式（零 exp/log 的幂收缩核）                      *)
(*   (1−w)^k · (1 + k·w) ≤ 1（0 < w < 1）                                *)
(* ============================================================ *)

Lemma mix_bernoulli_upper : forall (w : Real) (k : nat),
  real_le real_zero w -> real_lt real_zero w -> real_le w real_one ->
  real_lt w real_one ->
  real_le (real_mult (tv_rpow (real_minus_r real_one w) k)
                     (real_plus real_one (mix_scale k w)))
          real_one.
Proof.
  intros w k Hw0 Hwp Hw1 Hwlt. induction k as [| k IH].
  - (* k = 0：1·(1+0) == 1 *)
    apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_mult real_one (real_plus real_one (mix_scale 0 w)))
             (real_mult real_one real_one)).
    + apply (RealSetoid.real_eq_mult_compat real_one
               (real_plus real_one (mix_scale 0 w)) real_one real_one
               (real_eq_refl real_one) (real_plus_zero real_one)).
    + exact (real_mult_one real_one).
  - (* 归纳步：环运算化简 (1−w)(1+(k+1)w) == (1+kw) − ((k+1)w)·w；
       子 claim (1−w)(1+(k+1)w) ≤ 1+kw；再乘 Pk 接 IH *)
    assert (Hbpos : real_lt real_zero (real_minus_r real_one w))
      by exact (tv_omd_pos_of_lt w Hwlt).
    assert (HPk : real_lt real_zero (tv_rpow (real_minus_r real_one w) k))
      by exact (mix_rpow_pos (real_minus_r real_one w) k Hbpos).
    assert (HC : real_lt real_zero (real_mult (mix_scale (Datatypes.S k) w) w))
      by exact (real_mult_pos_compat (mix_scale (Datatypes.S k) w) w
                 (mix_scale_S_pos w k Hwp) Hwp).
    assert (HeqSC : real_eq
              (real_mult (real_minus_r real_one w)
                 (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_minus_r (real_plus real_one (mix_scale k w))
                 (real_mult (mix_scale (Datatypes.S k) w) w)))
      by exact (mix_ring_sc w (mix_scale k w)).
    assert (HSC : real_le
              (real_mult (real_minus_r real_one w)
                 (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_plus real_one (mix_scale k w))).
    { apply (real_le_trans _
               (real_minus_r (real_plus real_one (mix_scale k w))
                  (real_mult (mix_scale (Datatypes.S k) w) w))).
      - apply (RealSetoid.real_eq_le). exact HeqSC.
      - apply (real_le_trans _
                 (real_plus (real_minus_r (real_plus real_one (mix_scale k w))
                               (real_mult (mix_scale (Datatypes.S k) w) w))
                            (real_mult (mix_scale (Datatypes.S k) w) w))).
        + exact (igr_le_plus_r _ _ HC).
        + apply (RealSetoid.real_eq_le).
          exact (mix_ring_cancel _ _). }
    assert (HeqR : real_eq
              (real_mult (real_mult (real_minus_r real_one w)
                           (tv_rpow (real_minus_r real_one w) k))
                        (real_plus real_one (mix_scale (Datatypes.S k) w)))
              (real_mult (real_mult (real_minus_r real_one w)
                              (real_plus real_one (mix_scale (Datatypes.S k) w)))
                         (tv_rpow (real_minus_r real_one w) k)))
      by exact (real_eq_trans
                  (real_mult (real_mult (real_minus_r real_one w)
                               (tv_rpow (real_minus_r real_one w) k))
                        (real_plus real_one (mix_scale (Datatypes.S k) w)))
                  (real_mult (tv_rpow (real_minus_r real_one w) k)
                     (real_mult (real_minus_r real_one w)
                        (real_plus real_one (mix_scale (Datatypes.S k) w))))
                  (real_mult (real_mult (real_minus_r real_one w)
                               (real_plus real_one
                                  (mix_scale (Datatypes.S k) w)))
                        (tv_rpow (real_minus_r real_one w) k))
                  (mix_mult_swap (real_minus_r real_one w)
                     (tv_rpow (real_minus_r real_one w) k)
                     (real_plus real_one (mix_scale (Datatypes.S k) w)))
                  (real_mult_comm (tv_rpow (real_minus_r real_one w) k)
                     (real_mult (real_minus_r real_one w)
                        (real_plus real_one (mix_scale (Datatypes.S k) w))))).
    assert (IH' : real_le
              (real_mult (real_plus real_one (mix_scale k w))
                         (tv_rpow (real_minus_r real_one w) k))
              real_one).
    { apply (real_le_trans _
               (real_mult (tv_rpow (real_minus_r real_one w) k)
                          (real_plus real_one (mix_scale k w)))).
      - apply (RealSetoid.real_eq_le). exact (real_mult_comm _ _).
      - exact IH. }
    apply (real_le_trans
             (real_mult (real_mult (real_minus_r real_one w)
                          (tv_rpow (real_minus_r real_one w) k))
                   (real_plus real_one (mix_scale (Datatypes.S k) w)))
             (real_mult (real_plus real_one (mix_scale k w))
                (tv_rpow (real_minus_r real_one w) k))
             real_one).
    + apply (real_le_trans _
               (real_mult (real_mult (real_minus_r real_one w)
                              (real_plus real_one (mix_scale (Datatypes.S k) w)))
                          (tv_rpow (real_minus_r real_one w) k))).
      * apply (RealSetoid.real_eq_le). exact HeqR.
      * exact (real_le_mult_compat
                 (real_mult (real_minus_r real_one w)
                    (real_plus real_one (mix_scale (Datatypes.S k) w)))
                 (real_plus real_one (mix_scale k w))
                 (tv_rpow (real_minus_r real_one w) k) HPk HSC).
    + exact IH'.
Qed.

(* ============================================================ *)
(* Part 4：逆元支路（A·B ≤ 1 ∧ 0<B ⟹ A ≤ 1/B）                             *)
(* ============================================================ *)

Lemma mix_le_inv : forall (A B : Real) (HB : real_lt real_zero B),
  real_le (real_mult A B) real_one -> real_le A (real_inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : real_lt real_zero (real_inv_pos B HB))
    by exact (real_inv_pos_pos B HB).
  assert (HeqA : real_eq A
              (real_mult (real_mult A B) (real_inv_pos B HB))).
  { apply (real_eq_trans A (real_mult A real_one)).
    - apply (real_eq_sym _ _ (real_mult_one A)).
    - apply (real_eq_trans (real_mult A real_one)
               (real_mult A (real_mult B (real_inv_pos B HB)))).
      + apply (RealSetoid.real_eq_mult_compat A real_one A
                 (real_mult B (real_inv_pos B HB)) (real_eq_refl A)
                 (real_eq_sym _ _ (real_inv_pos_correct B HB))).
      + exact (real_mult_assoc A B (real_inv_pos B HB)). }
  apply (real_le_trans A
           (real_mult (real_mult A B) (real_inv_pos B HB))
           (real_inv_pos B HB)).
  - apply (RealSetoid.real_eq_le). exact HeqA.
  - apply (real_le_trans _ (real_mult real_one (real_inv_pos B HB))).
    + exact (real_le_mult_compat (real_mult A B) real_one
               (real_inv_pos B HB) HBp HAB).
    + apply (RealSetoid.real_eq_le).
      apply (real_eq_trans (real_mult real_one (real_inv_pos B HB))
               (real_mult (real_inv_pos B HB) real_one)).
      * exact (real_mult_comm real_one (real_inv_pos B HB)).
      * exact (real_mult_one (real_inv_pos B HB)).
Qed.

(* ============================================================ *)
(* Part 5：k 选取主定理 —— mix_pow_budget                                 *)
(* ============================================================ *)

Theorem mix_pow_budget : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  assert (hwp : real_lt real_zero (real_minus_r real_one kappa))
    by exact (tv_omd_pos_of_lt kappa Hk2).
  assert (hw1 : real_le kappa real_one).
  { apply (RealSetoid.real_lt_le_iff_req kappa real_one). left.
    exact Hk2. }
  assert (hw0 : real_le real_zero (real_minus_r real_one kappa))
    by exact (tv_omd_nonneg kappa hw1).
  assert (hwlt : real_lt (real_minus_r real_one kappa) real_one)
    by exact (mix_omd_lt_one kappa Hk1).
  assert (Heqk : real_eq kappa
              (real_minus_r real_one (real_minus_r real_one kappa)))
    by exact (mix_omd_id kappa).
  assert (Hwb : real_lt real_zero
              (real_mult (real_minus_r real_one kappa) budget))
    by exact (real_mult_pos_compat (real_minus_r real_one kappa) budget
                hwp Hbudget).
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                Hwb))) as [N [Hge2 HN]].
  destruct N as [| N'].
  - exfalso. lia.
  - set (w := real_minus_r real_one kappa) in *.
    set (wb := real_mult w budget) in *.
    set (Ms := mix_scale (Datatypes.S N') w) in *.
    set (boost := real_plus real_one Ms) in *.
    set (invwb := real_inv_pos wb Hwb).
    set (mR := real_const (Z.of_nat (Datatypes.S N') # 1)).
    assert (HMs : real_lt real_zero Ms)
      by exact (mix_scale_S_pos w N' hwp).
    assert (HMsnn : real_le real_zero Ms).
    { apply (RealSetoid.real_lt_le_iff_req real_zero Ms). left.
      exact HMs. }
    assert (Hboost0 : real_lt real_zero boost)
      by exact (mix_boost_pos w (Datatypes.S N') hw0).
    assert (HinvB : real_lt real_zero (real_inv_pos boost Hboost0))
      by exact (real_inv_pos_pos boost Hboost0).
    (* ---- 预算支路：TV0 < budget·boost ---- *)
    assert (Hstep : real_lt (real_mult (real_mult TV0 invwb) wb)
                         (real_mult mR wb))
      by exact (real_mult_lt_compat _ _ _ HN Hwb).
    assert (HeqL : real_eq (real_mult (real_mult TV0 invwb) wb) TV0).
    { apply (real_eq_trans _ (real_mult wb (real_mult TV0 invwb))).
      - exact (real_mult_comm _ _).
      - exact (real_mult_div wb TV0 Hwb). }
    assert (HeqR : real_eq (real_mult mR wb) (real_mult Ms budget)).
    { apply (real_eq_trans _ (mix_scale (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_eq_const (Datatypes.S N') wb)).
      - apply (real_eq_sym _ _ (mix_scale_mult_distrib (Datatypes.S N') w budget)). }
    assert (Hb0 : real_lt TV0 (real_mult Ms budget)).
    { exact (real_lt_eq_lt TV0 (real_mult mR wb) (real_mult Ms budget)
               (real_eq_lt_lt TV0 (real_mult (real_mult TV0 invwb) wb)
                  (real_mult mR wb) (real_eq_sym _ _ HeqL) Hstep)
               HeqR). }
    assert (HeqBud : real_eq (real_mult budget boost)
                         (real_plus budget (real_mult Ms budget))).
    { apply (real_eq_trans _
               (real_plus (real_mult budget real_one)
                  (real_mult budget Ms))).
      - exact (real_distrib budget real_one Ms).
      - apply (RealSetoid.real_eq_plus_compat (real_mult budget real_one)
                 (real_mult budget Ms) budget (real_mult Ms budget)
                 (real_mult_one budget) (real_mult_comm budget Ms)). }
    assert (Hbud : real_lt TV0 (real_mult budget boost)).
    { apply (real_lt_eq_lt TV0 (real_plus (real_mult Ms budget) budget)
               (real_mult budget boost)).
      - exact (real_lt_le_trans TV0 (real_mult Ms budget)
                 (real_plus (real_mult Ms budget) budget) Hb0
                 (igr_le_plus_r (real_mult Ms budget) budget Hbudget)).
      - exact (real_eq_trans (real_plus (real_mult Ms budget) budget)
                 (real_plus budget (real_mult Ms budget))
                 (real_mult budget boost)
                 (real_plus_comm (real_mult Ms budget) budget)
                 (real_eq_sym _ _ HeqBud)).
    }
    exists (Datatypes.S N').
    (* ---- 主链：κ^(Datatypes.S N')·TV0 < budget ---- *)
    assert (Heqp : real_eq (tv_rpow kappa (Datatypes.S N'))
              (tv_rpow (real_minus_r real_one w) (Datatypes.S N')))
      by exact (mix_rpow_eq_compat kappa (real_minus_r real_one w)
                  (Datatypes.S N') Heqk).
    assert (hw1w : real_le w real_one).
    { apply (RealSetoid.real_lt_le_iff_req w real_one). left.
      exact hwlt. }
    assert (Hbern : real_le
              (real_mult (tv_rpow (real_minus_r real_one w) (Datatypes.S N')) boost)
              real_one)
      by exact (mix_bernoulli_upper w (Datatypes.S N') hw0 hwp hw1w hwlt).
    assert (Hinvleg : real_le
              (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
              (real_inv_pos boost Hboost0))
      by exact (mix_le_inv _ _ Hboost0 Hbern).
    apply (real_le_lt_trans _ (real_mult (real_inv_pos boost Hboost0) TV0)
             budget).
    + apply (real_le_trans _
               (real_mult (tv_rpow (real_minus_r real_one w) (Datatypes.S N')) TV0)).
        * apply (RealSetoid.real_eq_le).
          exact (RealSetoid.real_eq_mult_compat
                   (tv_rpow kappa (Datatypes.S N')) TV0
                   (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
                   TV0 Heqp (real_eq_refl TV0)).
        * exact (real_le_mult_compat
                   (tv_rpow (real_minus_r real_one w) (Datatypes.S N'))
                   (real_inv_pos boost Hboost0) TV0 Ha Hinvleg).
    + apply (real_eq_lt_lt _ _ _ (real_mult_comm _ _)).
      apply (real_lt_eq_lt _
               (real_mult (real_mult budget boost)
                  (real_inv_pos boost Hboost0))).
        * exact (real_mult_lt_compat TV0 (real_mult budget boost)
                  (real_inv_pos boost Hboost0) Hbud HinvB).
        * apply (real_eq_trans _
                 (real_mult (real_mult boost budget)
                            (real_inv_pos boost Hboost0))).
          -- apply (RealSetoid.real_eq_mult_compat
                   (real_mult budget boost) (real_inv_pos boost Hboost0)
                   (real_mult boost budget) (real_inv_pos boost Hboost0)
                   (real_mult_comm budget boost) (real_eq_refl _)).
          -- apply (real_eq_trans (real_mult (real_mult boost budget)
                              (real_inv_pos boost Hboost0))
                   (real_mult boost (real_mult budget
                        (real_inv_pos boost Hboost0)))).
            ++ apply (real_eq_sym _ _ (real_mult_assoc boost budget
                          (real_inv_pos boost Hboost0))).
            ++ exact (real_mult_div boost budget Hboost0).
Defined.

(* ============================================================ *)
(* Part 6：非负 TV₀ 放宽形（mix_k_select）与 le 形                        *)
(* ============================================================ *)

Theorem mix_k_select : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  unfold real_le in Ha.
  destruct Ha as [Ha | Haq].
  - exact (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
  - exists 0%nat.
    apply (real_eq_lt_lt (real_mult (tv_rpow kappa 0) TV0) real_zero budget).
    + apply (real_eq_trans (real_mult (tv_rpow kappa 0) TV0)
               (real_mult real_one TV0) real_zero).
      * exact (RealSetoid.real_eq_mult_compat (tv_rpow kappa 0) TV0
                 real_one TV0 (real_eq_refl real_one) (real_eq_refl TV0)).
      * exact (real_eq_trans (real_mult real_one TV0) TV0 real_zero
                 (mix_mult_one_l TV0) (real_eq_sym _ _ Haq)).
    + exact Hbudget.
Defined.

Corollary mix_k_select_le : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget.
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget) as [k Hk].
  exists k.   apply (RealSetoid.real_lt_le_iff_req). left. exact Hk.
Defined.

(* ============================================================ *)
(* Part 6.5：见证与证明分离（提取效率设计）                                *)
(*   动因：mix_pow_budget / mix_k_select 以 Defined 收束 ⟹ 提取后           *)
(*     运行时强制计算 mix_bernoulli_upper 归纳证书链（Set 层 real_le，       *)
(*     长度 = k，且绑定 tv_rpow 的 Real 值构造 → cauchy 模证强制）⟹ 膨胀/超时 *)
(*   方案：见证（纯计算 k）与证明（不透明 Qed）分离。                        *)
(*   · mix_k_compute : 透明 Definition，仅走 real_arch 枚举（廉价 Q 层），    *)
(*     不构造 tv_rpow / mix_bernoulli_upper ⟹ 提取程序运行时只付 real_arch    *)
(*     ＋基础 Real 运算（real_minus_r/real_mult/real_inv_pos），跳过膨胀链。  *)
(*   · mix_k_spec : Qed 不透明，承载 κ^k·TV₀ < budget 的全证书（经            *)
(*     mix_pow_budget 复用，含 mix_bernoulli_upper）；运行时不强制求值。      *)
(*   · mix_k_select_r1 : existT 封装（witness=mix_k_compute, proof=mix_k_spec）；*)
(*     projT1 归约固定引理 mix_k_select_r1_projT1（Qed 第二分量不影响 projT1   *)
(*     归约——标准事实，机检固定）。                                          *)
(*   零新增公理；mix_k_compute 全树透明、可提取；mix_k_spec 不透明。         *)
(* ============================================================ *)

Definition mix_k_compute (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Hbudget : real_lt real_zero budget) : nat :=
  let w := real_minus_r real_one kappa in
  let wb := real_mult w budget in
  let Hwb := real_mult_pos_compat w budget (tv_omd_pos_of_lt kappa Hk2) Hbudget in
  let (n, _) := real_arch (real_mult TV0 (real_inv_pos wb Hwb)) in n.

(* 见证一致引理（R1 新增证明义务，机检固定）：mix_k_compute 的 k 与
   mix_pow_budget 证书的 k 同源于同一 real_arch sigT 的首投影；后者证明体内
   destruct N 死支精化后呈 S 形，与裸 arch 见证命题等值（0 支由 2≤n 死支排除）。
   real_arch 为 Qed 不透明，二者定义性不等价 ⟹ mix_k_spec 复用证书须经此引理。 *)
Theorem mix_k_compute_eq_pow_budget (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget
  = projT1 (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
Proof.
  unfold mix_k_compute, mix_pow_budget.
  cbv zeta.
  destruct (real_arch (real_mult TV0
             (real_inv_pos (real_mult (real_minus_r real_one kappa) budget)
                (real_mult_pos_compat (real_minus_r real_one kappa) budget
                   (tv_omd_pos_of_lt kappa Hk2) Hbudget)))) as [n [Hge2 Hn]].
  destruct n as [| m].
  - exfalso. lia.
  - reflexivity.
Qed.

Theorem mix_k_spec (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  real_lt (real_mult (tv_rpow kappa (mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget)) TV0) budget.
Proof.
  rewrite (mix_k_compute_eq_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget).
  exact (projT2 (mix_pow_budget kappa TV0 budget Hk1 Hk2 Ha Hbudget)).
Qed.

Definition mix_k_select_r1 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  existT _ (mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget)
         (mix_k_spec kappa TV0 budget Hk1 Hk2 Ha Hbudget).

(* 归约固定：projT1 (mix_k_select_r1 ...) = mix_k_compute ...（Qed 第二分量    *)
(*   不影响 projT1 归约——R1 设计文档新增证明义务，机检固定）               *)
Theorem mix_k_select_r1_projT1 (kappa TV0 budget : Real)
  (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
  (Ha : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget) :
  projT1 (mix_k_select_r1 kappa TV0 budget Hk1 Hk2 Ha Hbudget)
  = mix_k_compute kappa TV0 budget Hk1 Hk2 Hbudget.
Proof. reflexivity. Qed.

Print Assumptions mix_k_compute.
Print Assumptions mix_k_spec.
Print Assumptions mix_k_select_r1.

(* ============================================================ *)
(* Part 7-8（mix_time_explicit / mix_k_calc）：遗留项说明。可判定性实体：  *)
(*   mix_time_explicit 的 TV₀ 符号分叉需「real_le real_zero TV0」的居住者， *)
(*   而该 Or-Set 不可由基座判定构造（构造性逻辑），须随接口显式携带或改    *)
(*   B 形：完整起草（Section MixingTV 9+1 变量面 + tv_doeblin_iter × ④     *)
(*   组装 + δ=1/TV₀=0 支 k:=1 一步闭合 + mix_k_calc Defined 计算器）待    *)
(*   接口扩展后并入。                                                      *)
(* ============================================================ *)

(* ============================================================ *)
(* 审计口（Print Assumptions 追印面，全 Closed 预期）                     *)
(* ============================================================ *)

Print Assumptions mix_pow_budget.
Print Assumptions mix_k_select.
Print Assumptions mix_k_select_le.

Print Assumptions mix_rpow_one.
