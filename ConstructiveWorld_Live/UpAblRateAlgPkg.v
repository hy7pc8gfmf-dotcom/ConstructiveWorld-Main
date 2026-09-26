(* ==========================================================================)
   UpAblRateAlgPkg.v — 抽象率代数封装与主定理 rap_k_select
   使命: 率代数接口 rap_alg（Record 六字段：率列/预算/可判定测试/单调递减操作化/过站窗存在/语义桥）与主定理 rap_k_select（封装到显式步 k 使 rate k < budget，测试次数 ≤ 2·log₂K+5）；几何率实例 rap_geom_alg。
   依赖: QArith.Qring、ZArith、Lia、Lqa、CW_ConstructiveWorld_219、UpReqIterGeomRate、UpReqMixLogB、UpTVDoeblin、UpReqMixingTime。
   对标: 随机算法中的几何加速率与对数测试界（率形可计算化的充分条件刻画）。
   构造性: 零承认词面、零经典逻辑（全件显式见证式构造）；语句面全 Set 层；主定理非平凡增量=最小站与对数测试次数界；Set 组件 Separate Extraction 不含 Obj.magic。
   编译配方: Rocq 9.1 直调 coqc 与 cpu_guard（-LoadLimit 85 -CoreN 2），输出至临时目录，树内零写入。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogB.
Require Import UpTVDoeblin.
Require Import UpReqMixingTime.

(* ============================================================ *)
(* §1 率代数接口（件①）——可算法化率形的充分条件刻画                        *)
(* ============================================================ *)

Record rap_alg : Type := mk_rap_alg {
  rap_rate   : nat -> Real;
  rap_budget : Real;
  rap_test   : nat -> bool;
  rap_mono   : mixb_mono rap_test;
  rap_pass   : sigT (fun k : nat => rap_test k = true);
  rap_bridge : forall n : nat,
                 rap_test n = true -> real_lt (rap_rate n) rap_budget
}.

(* ============================================================ *)
(* §2 搜索辅助引理与主定理（件②）                                          *)
(* ============================================================ *)

(* bool 同站真假矛盾辅助引理（窗站穷尽矛盾情形用）                          *)
Lemma rap_bool_contra : forall b : bool, b = true -> b = false -> False.
Proof.
  intros b H1 H2. rewrite H1 in H2. discriminate H2.
Qed.

(* 辅助引理：双相 fuel 给定下 mixb_sel 的输出站必过测试                     *)
(*（mixb_sel_scale 第一合取支的 Set 面出口——Prop 只以引理应用形态       *)
(*  进 Defined 体，零 Prop 消去） *)
Lemma rap_sel_true : forall (test : nat -> bool) (K k r c : nat),
  mixb_mono test -> test 0%nat = false -> test k = true ->
  (forall j : nat, (j < k)%nat -> test j = false) ->
  (1 <= k)%nat -> (k <= K)%nat -> (2 <= K)%nat ->
  mixb_sel test (Datatypes.S (Datatypes.S (Nat.log2 K)))
           (Datatypes.S (Datatypes.S (Nat.log2 K))) = (r, c) ->
  test r = true.
Proof.
  intros test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel.
  destruct (mixb_sel_scale test K k r c Hm H0 Htk Hmin H1 HK HK2 Hsel)
    as [Hrk _].
  rewrite Hrk. exact Htk.
Qed.

(* 主定理：凡入封装率形皆可预算驱动返回步数（最小过站，对数测试）           *)
Definition rap_k_select (p : rap_alg) :
  sigT (fun k : nat => real_lt (rap_rate p k) (rap_budget p)).
Proof.
  destruct p as [rate budget test mono pass bridge].
  destruct (test 0%nat) eqn:E0.
  - (* 零站即过：k := 0 经桥一步闭合 *)
    exact (existT _ 0%nat (bridge 0%nat E0)).
  - (* 窗站 kw → 界 K := max(kw,2) → 最小站 kmin → 双相搜索 → 桥 *)
    destruct pass as [kw Hkw].
    destruct (igr_k_enum test kw) as [kmin|] eqn:Eenum.
    + pose proof (igr_k_enum_sound test kw kmin Eenum) as Hsnd.
      pose proof (igr_k_enum_min test kw kmin Eenum) as Hmin.
      pose proof (mixb_enum_le test kw kmin Eenum) as HminK.
      assert (H1 : (1 <= kmin)%nat).
      { destruct kmin as [| m]. exfalso. congruence. exact (le_n_S 0 m (le_0_n m)). }
      assert (HK : (kmin <= Nat.max kw 2)%nat)
        by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                    (Nat.le_max_l kw 2))).
      assert (HK2 : (2 <= Nat.max kw 2)%nat) by (apply Nat.le_max_r).
      destruct (mixb_sel test
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
                  (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))))
        as [r c] eqn:Esel.
      exact (existT _ r
               (bridge r
                  (rap_sel_true test (Nat.max kw 2) kmin r c mono E0 Hsnd
                     Hmin H1 HK HK2 Esel))).
    + (* 无窗矛盾：kw ≤ kw 燃料下枚举必有站 *)
      exact (False_rect _
               (rap_bool_contra (test kw) Hkw
                  (igr_k_enum_none test kw Eenum kw (Nat.le_refl kw)))).
Defined.

(* _le 对偶（一步推得） *)
Definition rap_k_select_le (p : rap_alg) :
  sigT (fun k : nat => real_le (rap_rate p k) (rap_budget p)).
Proof.
  destruct (rap_k_select p) as [k Hk].
  exact (existT _ k
           (RealSetoid.real_lt_le_iff_req (rap_rate p k) (rap_budget p)
              (inl Hk))).
Defined.

(* 量级界（Qed 面）：返回站过、以下全败、测试次数 ≤ 2·log₂K+5              *)
Corollary rap_k_select_account : forall (p : rap_alg) (kw r c : nat),
  rap_test p 0%nat = false ->
  rap_test p kw = true ->
  mixb_sel (rap_test p)
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2))))
    (Datatypes.S (Datatypes.S (Nat.log2 (Nat.max kw 2)))) = (r, c) ->
  rap_test p r = true /\
  (forall j : nat, (j < r)%nat -> rap_test p j = false) /\
  (c <= 2 * (Nat.log2 (Nat.max kw 2)) + 5)%nat.
Proof.
  intros p kw r c H0 Hkw Esel.
  destruct (igr_k_enum (rap_test p) kw) as [kmin|] eqn:Eenum.
  - pose proof (igr_k_enum_sound (rap_test p) kw kmin Eenum) as Hsnd.
    pose proof (igr_k_enum_min (rap_test p) kw kmin Eenum) as Hmin.
    pose proof (mixb_enum_le (rap_test p) kw kmin Eenum) as HminK.
    assert (H1 : (1 <= kmin)%nat).
    { destruct kmin as [| m].
      - rewrite H0 in Hsnd. discriminate Hsnd.
      - exact (le_n_S 0 m (le_0_n m)). }
    assert (HK : (kmin <= Nat.max kw 2)%nat)
      by (exact (Nat.le_trans kmin kw (Nat.max kw 2) HminK
                  (Nat.le_max_l kw 2))).
    destruct (mixb_sel_scale (rap_test p) (Nat.max kw 2) kmin r c
                (rap_mono p) H0 Hsnd Hmin H1 HK (Nat.le_max_r kw 2) Esel)
      as [Hrk Hcnt].
    rewrite Hrk.
    split; [ exact Hsnd | split; [ exact Hmin | exact Hcnt ] ].
  - exfalso.
    exact (rap_bool_contra (rap_test p kw) Hkw
             (igr_k_enum_none (rap_test p) kw Eenum kw (Nat.le_refl kw))).
Qed.

(* ============================================================ *)
(* §3 几何率实例（件③，real_ 面 tv_rpow 形）                               *)
(* ============================================================ *)

Local Open Scope Q_scope.

(* 包级实例：rate k := κ^k·A，测试 := mixb_qtest κ0 v b0（Q 层可判定），  *)
(* 桥 := mixb_real_chain 回传链，窗 := real_arch 兜底 + Q-Bernoulli 反解。 *)
(* 证书拆显式参数、构造器直出（体内零 destruct）——投影换算面保归约，    *)
(* 使用侧推论在自身体内做证书拆分。 *)
(* ——mix_k_select 语义的包级复现（语义级实例，不逐字回替）。 *)
Definition rap_geom_alg (kappa A B : Real) (v : Q)
  (Hk1 : real_lt real_zero kappa)
  (HA : real_le real_zero A)
  (epsK : Q) (HepsK : QltT 0 epsK) (NK : nat)
  (HNK : forall n : nat, NatLe NK n -> QltT epsK (projT1 real_one n - projT1 kappa n))
  (Hvc : real_le A (real_const v))
  (epsB : Q) (HepsB : QltT 0 epsB) (NB : nat)
  (HNB : forall n : nat, NatLe NB n -> QltT epsB (projT1 B n - projT1 real_zero n))
  : rap_alg.
Proof.
  assert (Hk0 : 0 < 1 - mixb_mu epsK)
    by (apply mixb_kappa0_pos; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hk0lt : 1 - mixb_mu epsK < 1)
    by (apply mixb_kappa0_lt_one; exact (QltT_to_Qlt 0 epsK HepsK)).
  assert (Hb0 : 0 < epsB * (1 # 2)).
  { apply (Qmult_lt_0_compat epsB (1 # 2)).
    - exact (QltT_to_Qlt 0 epsB HepsB).
    - exact mixb_q_12_pos. }
  assert (Hv0 : 0 <= v) by exact (mixb_v_nonneg A v HA Hvc).
  assert (Hk0le : real_le kappa (real_const (1 - mixb_mu epsK))).
  { apply (RealSetoid.real_lt_le_iff_req). left.
    exact (mixb_kappa0_bridge kappa epsK NK HepsK HNK). }
  assert (Hc0pos : real_lt real_zero (real_const (1 - mixb_mu epsK)))
    by exact (mixb_qpos_const_lt _ Hk0).
  assert (Hbb : real_lt (real_const (epsB * (1 # 2))) B)
    by exact (mixb_b0_bridge B epsB NB HepsB HNB).
  apply (mk_rap_alg (fun k : nat => real_mult (tv_rpow kappa k) A) B
           (mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)))).
  - (* 单调：Q 幂递减 × v 非负 ⟹ 过站集上闭 *)
    exact (mixb_qtest_mono (1 - mixb_mu epsK) v (epsB * (1 # 2)) Hk0
             (Qlt_le_weak (1 - mixb_mu epsK) 1 Hk0lt) Hv0).
  - (* 过站窗：real_arch 兜底 + Q-Bernoulli 反解 *)
    pose (wb := ((1 - (1 - mixb_mu epsK)) * (epsB * (1 # 2)))%Q).
    assert (Hwbpos : 0 < wb).
    { pose proof (mixb_mu_pos epsK (QltT_to_Qlt 0 epsK HepsK)) as Hmu.
      unfold wb.
      apply (Qmult_lt_0_compat (1 - (1 - mixb_mu epsK))
               (epsB * (1 # 2))); [ lra | exact Hb0 ]. }
    assert (Hwbne : ~ (wb == 0)).
    { intro He. apply (Qlt_not_eq 0 wb Hwbpos). apply mixb_qeq_sym.
      exact He. }
    destruct (real_arch (real_const (v * Qinv wb))) as [nA Hpair].
    destruct Hpair as [Hnge2 Harchlt].
    assert (Hqarch : Qlt (v * Qinv wb) (Z.of_nat nA # 1))
      by exact (mixb_const_lt_to_Qlt _ _ Harchlt).
    assert (Hwin : Qle v ((Z.of_nat nA # 1) * wb)).
    { apply Qlt_le_weak.
      apply (Qle_lt_trans v ((v * Qinv wb) * wb)
               ((Z.of_nat nA # 1) * wb)).
      - apply qeq_le. apply mixb_qeq_sym.
        exact (mixb_qmul_inv_cancel v wb Hwbpos).
      - exact (Qmult_lt_compat_r (v * Qinv wb) (Z.of_nat nA # 1) wb
                 Hwbpos Hqarch). }
    assert (HpassnA : mixb_qtest (1 - mixb_mu epsK) v (epsB * (1 # 2)) nA
                      = true).
    { apply (mixb_window_test_true (1 - mixb_mu epsK) v (epsB * (1 # 2))
               nA Hk0 Hk0lt Hv0 Hb0); [ lia | exact Hwin ]. }
    exact (existT _ nA HpassnA).
  - (* Real 语义桥：测试真值 ⟹ κ^n·A < B（mixb 回传链） *)
    intros n Hn.
    exact (mixb_real_chain kappa A B (1 - mixb_mu epsK) v (epsB * (1 # 2))
             n Hk1 Hk0le Hc0pos HA Hvc Hbb Hn).
Defined.

(* 包级语义复现：几何率形 κ^k·A 的预算驱动步返回（mix_k_select 语义）      *)
(* ——证书拆分在本推论体内完成，包构造器直出故投影换算一步闭合。           *)
Corollary rap_geom_k_select : forall (kappa A B : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A -> real_lt real_zero B ->
  sigT (fun v : Q => real_le A (real_const v)) ->
  sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) A) B).
Proof.
  intros kappa A B Hk1 Hk2 HA Hb Htv.
  destruct Hk2 as [epsK [HepsK [NK HNK]]].
  destruct Hb as [epsB [HepsB [NB HNB]]].
  destruct Htv as [v Hvc].
  exact (rap_k_select
           (rap_geom_alg kappa A B v Hk1 HA epsK HepsK NK HNK Hvc
              epsB HepsB NB HNB)).
Defined.

(* 率形单调递减（接口 rap_mono 字段的实例层语义化）：κ ≤ 1 收缩因子        *)
Theorem rap_geom_rate_dec : forall (kappa A : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero A ->
  forall (n : nat),
  real_le (real_mult (tv_rpow kappa (Datatypes.S n)) A)
          (real_mult (tv_rpow kappa n) A).
Proof.
  intros kappa A Hk1 Hk2 HA n.
  assert (Hk2le : real_le kappa real_one).
  { exact (RealSetoid.real_lt_le_iff_req kappa real_one (inl Hk2)). }
  assert (Hnn : real_le real_zero (tv_rpow kappa n)).
  { exact (mix_rpow_nonneg kappa n
             (RealSetoid.real_lt_le_iff_req real_zero kappa (inl Hk1))). }
  assert (Hstep : real_le (real_mult kappa (tv_rpow kappa n))
                          (real_mult real_one (tv_rpow kappa n)))
    by (exact (real_le_mult_compat_weak kappa real_one (tv_rpow kappa n)
                 Hnn Hk2le)).
  apply (real_le_trans _ (real_mult (real_mult real_one (tv_rpow kappa n)) A)
                        (real_mult (tv_rpow kappa n) A)).
  - apply (real_le_trans _ (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + apply (RealSetoid.real_eq_le).
      exact (real_eq_refl (real_mult (real_mult kappa (tv_rpow kappa n)) A)).
    + exact (real_le_mult_compat_weak
               (real_mult kappa (tv_rpow kappa n))
               (real_mult real_one (tv_rpow kappa n)) A HA Hstep).
  - apply (RealSetoid.real_eq_le).
    exact (RealSetoid.real_eq_mult_compat
             (real_mult real_one (tv_rpow kappa n)) A
             (tv_rpow kappa n) A
             (mix_mult_one_l (tv_rpow kappa n)) (real_eq_refl A)).
Qed.

(* ============================================================ *)
(* 假设审计（零承认件，全 Closed 预期）                                     *)
(* ============================================================ *)

Print Assumptions rap_sel_true.
Print Assumptions rap_k_select.
Print Assumptions rap_k_select_le.
Print Assumptions rap_k_select_account.
Print Assumptions rap_geom_alg.
Print Assumptions rap_geom_k_select.
Print Assumptions rap_geom_rate_dec.
