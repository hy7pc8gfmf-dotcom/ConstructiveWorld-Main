(* ==========================================================================)
   R2BishopLogSel.v — Bishop 对数搜索选择器
   使命: rb_bishop_search_ok（燃料化搜索正确性）、rb_log_return_bound（对数回报界）、mix_k_select_bishop（k-选择主定理）与 B 载体投影族（rb_*_proj）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB/2、G07_KLWall、KLWallClosed、UpReqMixLogA、UpReqMixLogE；Stdlib PeanoNat、QArith.Qring、Qabs、Lia、Extraction。
   对标: 构造性数学中的有界搜索（Bishop 式构造主义选择原理）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
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
Require Import UpRealLeB2.
Require Import G07_KLWall.
Require Import KLWallClosed.
Require Import UpReqMixLogA.
Require Import UpReqMixLogE.

(* nat 记号优先（基座 Open Scope Q_scope 经 Require 泄漏，裸 nat 算式须压回；
   Q 侧算式全部期望类型驱动或 %Q 显式标注，不受影响） *)
Open Scope nat_scope.

(* ============================================================ *)
(* Part A：Q 层余量代理引擎                                              *)
(* ============================================================ *)

(* 余量代理谓词：站 j 通过 ⟺ q1^j·M ≤ T。可判定（Qle_bool），且随 j        *)
(* 单调变易（q1<1 时 lhs 递减）。全部分支数据在 Q/nat 层。                 *)
Definition rb_cond (q1 M T : Q) (j : nat) : bool :=
  Qle_bool (mixe_qpow q1 j * M) T.

Lemma rb_cond_true_qle : forall q1 M T j,
  rb_cond q1 M T j = true -> Qle (mixe_qpow q1 j * M) T.
Proof. intros q1 M T j H. unfold rb_cond in H. apply mixa_qle_bool_true. exact H. Qed.

Lemma rb_qle_cond_true : forall q1 M T j,
  Qle (mixe_qpow q1 j * M) T -> rb_cond q1 M T j = true.
Proof.
  intros q1 M T j H. unfold rb_cond.
  destruct (Qle_bool (mixe_qpow q1 j * M) T) eqn:E; [reflexivity |].
  apply mixa_qle_bool_false in E.
  exfalso. apply (Qlt_not_le T (mixe_qpow q1 j * M)).
  - exact E.
  - exact H.
Qed.

(* q·X ≤ X（0≤q≤1, 0≤X） *)
Lemma rb_qmul_le_self : forall q X,
  Qle 0 q -> Qle q 1 -> Qle 0 X -> Qle (q * X) X.
Proof.
  intros q X Hq0 Hq1 HX.
  apply (Qle_trans (q * X) (1 * X) X).
  - apply (Qmult_le_compat_r q 1 X).
    + exact Hq1.
    + exact HX.
  - rewrite Qmult_1_l. apply Qle_refl.
Qed.

(* 幂列指数递减：i ≤ j ⟹ q1^j ≤ q1^i（0≤q1≤1） *)
Lemma rb_qpow_le_aux : forall q,
  Qle 0 q -> Qle q 1 ->
  forall d i : nat, Qle (mixe_qpow q (i + d)) (mixe_qpow q i).
Proof.
  intros q Hq0 Hq1 d. induction d as [| d IH]; intros i.
  - rewrite Nat.add_0_r. apply Qle_refl.
  - replace (i + (Datatypes.S d)) with (Nat.succ (i + d)) by (symmetry; apply Nat.add_succ_r).
    cbn [mixe_qpow].
    apply (Qle_trans (q * mixe_qpow q (i + d)) (mixe_qpow q (i + d)) (mixe_qpow q i)).
    + apply rb_qmul_le_self; [exact Hq0 | exact Hq1 |].
      apply mixe_qpow_nonneg. exact Hq0.
    + apply IH.
Qed.

Lemma rb_qpow_le : forall q,
  Qle 0 q -> Qle q 1 ->
  forall i j : nat, Nat.le i j -> Qle (mixe_qpow q j) (mixe_qpow q i).
Proof.
  intros q H0 H1 i j H.
  replace j with (i + (j - i)) by lia.
  apply rb_qpow_le_aux; assumption.
Qed.

(* 幂列底单调：0≤x≤y ⟹ x^j ≤ y^j *)
Lemma rb_qpow_mono_base : forall x y,
  Qle 0 x -> Qle x y ->
  forall j, Qle (mixe_qpow x j) (mixe_qpow y j).
Proof.
  intros x y Hx0 Hxy j. induction j as [| j IH].
  - cbn [mixe_qpow]. apply Qle_refl.
  - cbn [mixe_qpow].
    assert (Hy0 : Qle 0 y) by (apply (Qle_trans 0 x y Hx0 Hxy)).
    assert (Hxj0 : Qle 0 (mixe_qpow x j)) by (apply mixe_qpow_nonneg; exact Hx0).
    apply (Qle_trans (x * mixe_qpow x j) (y * mixe_qpow x j)
                     (y * mixe_qpow y j)).
    + apply (Qmult_le_compat_r x y (mixe_qpow x j) Hxy Hxj0).
    + rewrite (Qmult_comm y (mixe_qpow x j)).
      rewrite (Qmult_comm y (mixe_qpow y j)).
      apply (Qmult_le_compat_r (mixe_qpow x j) (mixe_qpow y j) y IH Hy0).
Qed.

(* Bernoulli 锐化消耗（mixe_bern_sharp 直取换形，无 Qinv 形） *)
Lemma rb_bern_sharp' : forall q1 k,
  Qle 0 q1 -> Qlt q1 1 ->
  Qle (mixe_qpow q1 k * (1 + mixe_qofnat k * (1 - q1))) 1.
Proof.
  intros q1 k Hq0 Hq1.
  assert (Hw0s : Qlt 0 (1 - q1)%Q) by (exact (proj1 (Qlt_minus_iff q1 1) Hq1)).
  assert (Hw0 : Qle 0 (1 - q1)%Q) by (apply (Qlt_le_weak 0%Q (1 - q1)%Q); exact Hw0s).
  assert (Hw1 : Qle (1 - q1)%Q 1).
  { pose proof (Qopp_le_compat 0%Q q1 Hq0) as H1.
    pose proof (Qplus_le_compat (- q1)%Q (- 0)%Q 1%Q 1%Q H1 (Qle_refl 1%Q)) as H2.
    assert (Hrc11 : (- q1 + 1)%Q == (1 - q1)%Q) by ring.
    rewrite Hrc11 in H2.
    assert (Hrc12 : (- 0 + 1)%Q == 1%Q) by ring.
    rewrite Hrc12 in H2.
    exact H2. }
  pose proof (mixe_bern_sharp (1 - q1)%Q k Hw0 Hw1) as Hs.
  assert (Hcvt : (1 - (1 - q1))%Q == q1) by ring.
  rewrite Hcvt in Hs. exact Hs.
Qed.

(* 对数二分搜索装配：在 [0, j0] 上二分，燃料 log₂j0+2 *)
Definition rb_bishop_search (q1 M T : Q) (j0 : nat) : nat :=
  mixa_bsearch (rb_cond q1 M T) (Nat.log2 j0 + 2) 0 j0.

(* 代理谓词单调（通过站向上闭合） *)
Lemma rb_cond_mono : forall q1 M T,
  Qle 0 q1 -> Qle q1 1 -> Qle 0 M ->
  forall j j' : nat, Nat.le j j' ->
  rb_cond q1 M T j = true -> rb_cond q1 M T j' = true.
Proof.
  intros q1 M T Hq0 Hq1 HM0 j j' Hjj Hj.
  apply rb_qle_cond_true.
  apply (Qle_trans (mixe_qpow q1 j' * M) (mixe_qpow q1 j * M) T).
  - apply (Qmult_le_compat_r (mixe_qpow q1 j') (mixe_qpow q1 j) M).
    + apply rb_qpow_le; assumption.
    + exact HM0.
  - apply rb_cond_true_qle. exact Hj.
Qed.

(* 燃料充分性：[0,j0] 区间二分解决所需步数 ≤ log₂j0+2（纯 nat） *)
Lemma rb_fuel_ge : forall j0 : nat,
  0 < j0 -> Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0 Hj0.
  destruct (Nat.log2_spec j0 Hj0) as [Hlo Hhi].
  replace (Nat.log2 j0 + 2) with (Nat.log2 j0 + 1 + 1) by lia.
  rewrite Nat.pow_add_r. rewrite Nat.pow_add_r.
  cbn [Nat.pow].
  replace (Datatypes.S (Nat.log2 j0)) with (Nat.log2 j0 + 1) in Hhi by lia.
  rewrite Nat.pow_add_r in Hhi. cbn [Nat.pow] in Hhi.
  lia.
Qed.

(* 搜索正确性：通过站 + 以下全败（最小性） *)
Theorem rb_bishop_search_ok : forall q1 M T j0,
  Qle 0 q1 -> Qle q1 1 -> Qle 0 M ->
  rb_cond q1 M T j0 = true ->
  rb_cond q1 M T (rb_bishop_search q1 M T j0) = true /\
  (forall j : nat, Nat.lt j (rb_bishop_search q1 M T j0) ->
     rb_cond q1 M T j = false).
Proof.
  intros q1 M T j0 Hq0 Hq1 HM0 Hhi.
  unfold rb_bishop_search.
  assert (Hc : rb_cond q1 M T
               (mixa_bsearch (rb_cond q1 M T) (Nat.log2 j0 + 2) 0 j0) = true /\
               (forall j : nat, Nat.le 0 j ->
                  Nat.lt j (mixa_bsearch (rb_cond q1 M T) (Nat.log2 j0 + 2) 0 j0) ->
                  rb_cond q1 M T j = false)).
  { apply (mixa_bsearch_correct (rb_cond q1 M T) (Nat.log2 j0 + 2) 0).
    - intros a b Hab Ha. exact (rb_cond_mono q1 M T Hq0 Hq1 HM0 a b Hab Ha).
    - intros j Hj0 Hjlt. inversion Hjlt.
    - apply Nat.le_refl.
    - apply Nat.le_0_l.
    - exact Hhi.
    - rewrite Nat.sub_0_r. destruct j0 as [| j0'].
      + replace (Nat.log2 0 + 2) with 2 by (cbn; lia).
        cbn [Nat.pow]. lia.
      + apply (rb_fuel_ge (Datatypes.S j0') (Nat.lt_0_succ j0')). }
  destruct Hc as [Hok Hmin].
  split.
  - exact Hok.
  - intros j Hj. exact (Hmin j (Nat.le_0_l j) Hj).
Qed.

(* 对数返回界：区间 [0,j0] 在 log₂j0+2 步二分内解决 *)
Theorem rb_log_return_bound : forall j0 : nat,
  Nat.le (Datatypes.S j0) (Nat.pow 2 (Nat.log2 j0 + 2)).
Proof.
  intros j0. destruct j0 as [| j0'].
  - replace (Nat.log2 0 + 2) with 2 by (cbn; lia).
    cbn [Nat.pow]. lia.
  - apply (rb_fuel_ge (Datatypes.S j0') (Nat.lt_0_succ j0')).
Qed.

(* ============================================================ *)
(* Part B：实层桥                                                        *)
(* ============================================================ *)

(* δ := 1−κ（收缩子） *)
Definition rb_delta0 (kappa : Real) : Real :=
  real_plus real_one (real_opp kappa).

Definition rb_gval (kappa TV0 : Real) (k : nat) : Real :=
  real_mult (powb_pow (rb_delta0 kappa) k) TV0.

(* 逐点投影助手 *)
Lemma rb_plus_proj : forall (x y : Real) (n : nat),
  projT1 (real_plus x y) n == (projT1 x n + projT1 y n)%Q.
Proof.
  intros x y n. destruct x as [u Hu]. destruct y as [v Hv].
  cbn [projT1 real_plus]. reflexivity.
Qed.

Lemma rb_opp_proj : forall (x : Real) (n : nat),
  projT1 (real_opp x) n == (- projT1 x n)%Q.
Proof.
  intros x n. destruct x as [u Hu].
  cbn [projT1 real_opp]. reflexivity.
Qed.

Lemma rb_mult_proj : forall (x y : Real) (n : nat),
  projT1 (real_mult x y) n == (projT1 x n * projT1 y n)%Q.
Proof.
  intros x y n. destruct x as [u Hu]. destruct y as [v Hv].
  cbn [projT1 real_mult]. reflexivity.
Qed.

Lemma rb_one_proj : forall n : nat, projT1 real_one n == 1%Q.
Proof. intros n. cbn [projT1 real_one]. reflexivity. Qed.

Lemma rb_zero_proj : forall n : nat, projT1 real_zero n == 0%Q.
Proof. intros n. cbn [projT1 real_zero]. reflexivity. Qed.

(* powb 幂的逐点投影：Q 层 mixe_qpow 换形 *)
Lemma rb_powb_proj : forall (d : Real) (j n : nat),
  projT1 (powb_pow d j) n == mixe_qpow (projT1 d n) j.
Proof.
  intros d j. induction j as [| j IH]; intros n.
  - cbn [powb_pow]. rewrite rb_one_proj. cbn [mixe_qpow]. apply Qeq_refl.
  - cbn [powb_pow]. rewrite rb_mult_proj. rewrite IH.
    cbn [mixe_qpow]. ring.
Qed.

(* |x| ≥ x（Q 层小助手） *)
Lemma rb_abs_ge : forall x : Q, Qle x (Qabs x).
Proof.
  intros x.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hneg].
  - pose proof (Qabs_pos x (Qlt_le_weak 0 x Hpos)) as Heq.
    rewrite Heq. apply Qle_refl.
  - destruct (Qlt_le_dec x 0) as [Hlt | Hge].
    + pose proof (Qabs_neg x Hneg) as Heq.
      rewrite Heq.
      pose proof (Qopp_le_compat x 0%Q Hneg) as H1.
      assert (Hrd1 : (- 0)%Q == 0%Q) by ring.
      rewrite Hrd1 in H1.
      apply (Qle_trans x 0%Q (- x)%Q Hneg H1).
    + assert (Heqx : x == 0%Q) by (apply Qle_antisym; [exact Hneg | exact Hge]).
      rewrite Heqx. rewrite (Qabs_pos 0%Q (Qle_refl 0%Q)). apply Qle_refl.
Qed.

(* 右乘零件 *)
Lemma rb_mult_zero_r : forall x : Real,
  real_eq (real_mult x real_zero) real_zero.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  rewrite rb_mult_proj. rewrite rb_zero_proj.
  cbn [projT1 real_zero]. ring.
Qed.

(* 分配律换形件（逐点 ring） *)
Lemma rb_mult_plus_distr_r : forall y e c : Real,
  real_eq (real_mult (real_plus y e) c)
          (real_plus (real_mult y c) (real_mult e c)).
Proof.
  intros y e c. destruct y as [u Hu]. destruct e as [v Hv].
  destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n.
  repeat rewrite rb_mult_proj. repeat rewrite rb_plus_proj.
  repeat rewrite rb_mult_proj. ring.
Qed.

(* 【R2-B 未竟项】≤_B 右乘保序（rb_le_b_mult_r）与 klc 向上谱系       *)
(*   （rb_valid_up）两件未能在本段闭合，留待下片。已探明的路线：      *)
(*   rb_le_b_mult_r 前件 real_le 0 c 两支：strict 支 e' := eps·real_inv_pos c，*)
(*     real_mult_lt_compat 右乘 + rb_mult_plus_distr_r 分配 + klst_r_pqx_eq_q *)
(*     (c·(eps·cinv)==eps) 回环换形；eq 支 real_eq_mult_compat 归零。        *)
(*   rb_valid_up := klc_closed_powb_mono κ j j'' (inl Hk0) (inl Hk1) Hjj      *)
(*     直接给 (1−κ)^{j''} ≤_B (1−κ)^j，经 rb_le_b_mult_r 右乘 TV0 +           *)
(*     real_le_b_trans 闭合。红线不破：以上全为机检路线，非猜想。            *)
(* Part C：主定理                                                        *)
(* ============================================================ *)

(* Hqarch：Q 层收缩幂 Archimedean 站点前件（loso 诚实前件先例同型——
   接口缺口以显式前件承载；其构造性闭合件=Bernoulli×Archimedes，留待下片） *)
Theorem mix_k_select_bishop : forall (kappa TV0 budget : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_le real_zero TV0 -> real_lt real_zero budget ->
  (forall (p v b : Q), Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
     sigT (fun j : nat => Qle (mixe_qpow p j * v) b)) ->
  sigT (fun k : nat => real_le_b (rb_gval kappa TV0 k) budget).
Proof.
  intros kappa TV0 budget Hk0 Hk1 Ha0 Hb0 Hqarch.
  (* 1. κ 两侧与 budget 的严格见证拆包 *)
  destruct Hk0 as [eps_k [Heps_k [Nk Hkn]]].
  destruct Hk1 as [eps_1 [Heps_1 [N1 Hkn1]]].
  destruct Hb0 as [eps_b [Heps_b [Nb Hbn]]].
  (* 2. Q 侧：eps_k ∈ (0,1) *)
  assert (Heps1_0 : Qlt 0 eps_1) by (apply QltT_to_Qlt; exact Heps_1).
  assert (Hek0 : Qlt 0 eps_k) by (apply QltT_to_Qlt; exact Heps_k).
  assert (Hnk1 : (Nk <= Nk + N1 + N1)%nat) by lia.
  assert (Hn11 : (N1 <= Nk + N1 + N1)%nat) by lia.
  set (n1 := Nk + N1 + N1).
  pose proof (Hkn n1 (NatLe_lift Nk n1 Hnk1)) as Hp1.
  pose proof (Hkn1 n1 (NatLe_lift N1 n1 Hn11)) as Hp2.
  pose proof (QltT_to_Qlt eps_k
                (projT1 kappa n1 - projT1 real_zero n1)%Q Hp1) as Hq1r.
  assert (Hrz1 : (projT1 real_zero n1)%Q == 0%Q) by (apply rb_zero_proj).
  rewrite Hrz1 in Hq1r.
  assert (Hrn1 : (projT1 kappa n1 - 0)%Q == (projT1 kappa n1)%Q) by ring.
  rewrite Hrn1 in Hq1r.
  rename Hq1r into Hq1.
  pose proof (QltT_to_Qlt eps_1 (1 - projT1 kappa n1)%Q Hp2) as Hq2.
  assert (Hek1 : Qlt eps_k 1).
  { assert (Hmid : Qlt (projT1 kappa n1) (1 - eps_1)%Q).
    { apply (proj2 (Qlt_minus_iff (projT1 kappa n1) (1 - eps_1)%Q)).
      assert (Hcc : ((1 - eps_1) + - projT1 kappa n1)%Q
                    == ((1 - projT1 kappa n1) + - eps_1)%Q) by ring.
      rewrite Hcc.
      exact (proj1 (Qlt_minus_iff eps_1 (1 - projT1 kappa n1)%Q) Hq2). }
    assert (Hlt1 : Qlt (1 - eps_1)%Q 1).
    { apply (proj2 (Qlt_minus_iff (1 - eps_1)%Q 1)).
      assert (Hc : (1 + - (1 - eps_1))%Q == eps_1) by ring.
      rewrite Hc. exact Heps1_0. }
    exact (Qlt_trans eps_k (1 - eps_1)%Q 1
             (Qlt_trans eps_k (projT1 kappa n1) (1 - eps_1)%Q Hq1 Hmid) Hlt1). }
  (* 3. 搜索数据 *)
  set (q1 := (1 - eps_k)%Q).
  assert (Hq10 : Qlt 0 q1) by (exact (proj1 (Qlt_minus_iff eps_k 1) Hek1)).
  assert (Hq11 : Qlt q1 1).
  { unfold q1.
    apply (proj2 (Qlt_minus_iff (1 - eps_k)%Q 1)).
    assert (Hc : (1 + - (1 - eps_k))%Q == eps_k) by ring.
    rewrite Hc. exact Hek0. }
  assert (Hq1le0 : Qle 0 q1) by (apply (Qlt_le_weak 0%Q q1); exact Hq10).
  assert (Hq1le1 : Qle q1 1) by (apply (Qlt_le_weak q1 1); exact Hq11).
  assert (Heps_b0 : Qlt 0 eps_b) by (apply QltT_to_Qlt; exact Heps_b).
  set (T := (eps_b * (1#2))%Q).
  assert (HT0 : Qlt 0 T).
  { unfold T. apply (Qmult_lt_0_compat eps_b (1#2)%Q).
    - exact Heps_b0.
    - unfold Qlt. cbn. lia. }
  destruct (real_norm_bounded TV0) as [M [HMt HM]].
  assert (HM0 : Qlt 0 M) by (apply QltT_to_Qlt; exact HMt).
  destruct (Hqarch q1 M T Hq10 Hq11 HM0 HT0) as [j0 Hj0q].
  assert (Hj0 : rb_cond q1 M T j0 = true)
    by (unfold rb_cond; apply rb_qle_cond_true; exact Hj0q).
  set (kstar := rb_bishop_search q1 M T j0).
  destruct (rb_bishop_search_ok q1 M T j0 Hq1le0 Hq1le1
              (Qlt_le_weak 0 M HM0) Hj0) as [Hok _].
  apply rb_cond_true_qle in Hok.
  (* 4. 逐点夹逼链：n ≥ Nk+Nb 处 (1−κn)^k·TV0n ≤ T < budget_n − T *)
  assert (Hpt : forall n : nat, (Nk + N1 + Nb <= n)%nat ->
    Qlt T (projT1 budget n
           - projT1 (real_mult (powb_pow (rb_delta0 kappa) kstar) TV0) n)%Q).
  { intros n Hn.
    assert (Hna : (Nk <= n)%nat) by (clear - Hn n; lia).
    assert (Hnb : (Nb <= n)%nat) by (clear - Hn n; lia).
    assert (Hn1 : (N1 <= n)%nat) by (clear - Hn n; lia).
    pose proof (Hkn n (NatLe_lift Nk n Hna)) as Hpk.
    pose proof (Hkn1 n (NatLe_lift N1 n Hn1)) as Hpk1.
    pose proof (Hbn n (NatLe_lift Nb n Hnb)) as Hpb.
    pose proof (QltT_to_Qlt eps_k
                  (projT1 kappa n - projT1 real_zero n)%Q Hpk) as Hqkr.
    assert (Hrz2 : (projT1 real_zero n)%Q == 0%Q) by (apply rb_zero_proj).
    rewrite Hrz2 in Hqkr.
    assert (Hrn2 : (projT1 kappa n - 0)%Q == (projT1 kappa n)%Q) by ring.
    rewrite Hrn2 in Hqkr.
    rename Hqkr into Hqk.
    pose proof (QltT_to_Qlt eps_1 (1 - projT1 kappa n)%Q Hpk1) as Hqk1.
    pose proof (QltT_to_Qlt eps_b
                  (projT1 budget n - projT1 real_zero n)%Q Hpb) as Hqbr.
    assert (Hrz3 : (projT1 real_zero n)%Q == 0%Q) by (apply rb_zero_proj).
    rewrite Hrz3 in Hqbr.
    assert (Hrn3 : (projT1 budget n - 0)%Q == (projT1 budget n)%Q) by ring.
    rewrite Hrn3 in Hqbr.
    rename Hqbr into Hqb.
    (* δn := 1−κn ∈ (0, q1] *)
    rewrite rb_mult_proj, rb_powb_proj.
    unfold rb_delta0.
    rewrite rb_plus_proj, rb_one_proj, rb_opp_proj.
    assert (Hrd5 : (1 + - projT1 kappa n)%Q == (1 - projT1 kappa n)%Q) by ring.
    rewrite Hrd5.
    assert (Hdn1 : Qle (1 - projT1 kappa n)%Q q1).
    { unfold q1.
      pose proof (Qopp_le_compat eps_k (projT1 kappa n)
                    (Qlt_le_weak eps_k (projT1 kappa n) Hqk)) as H1.
      pose proof (Qplus_le_compat 1%Q 1%Q (- projT1 kappa n)%Q (- eps_k)%Q
                    (Qle_refl 1%Q) H1) as H2.
      assert (Hrd6 : (1 + - projT1 kappa n)%Q == (1 - projT1 kappa n)%Q) by ring.
      rewrite Hrd6 in H2.
      assert (Hrd7 : (1 + - eps_k)%Q == (1 - eps_k)%Q) by ring.
      rewrite Hrd7 in H2.
      exact H2. }
    assert (Hdn0 : Qle 0 (1 - projT1 kappa n)%Q).
    { apply (Qlt_le_weak 0%Q (1 - projT1 kappa n)%Q).
      apply (Qlt_trans 0%Q eps_1 (1 - projT1 kappa n)%Q Heps1_0 Hqk1). }
    pose proof (QleT'_to_Qle (Qabs (projT1 TV0 n)) M (HM n)) as Hab1.
    assert (Hab : Qle (projT1 TV0 n) M).
    { apply (Qle_trans (projT1 TV0 n) (Qabs (projT1 TV0 n)) M).
      - apply rb_abs_ge.
      - exact Hab1. }
    assert (Hpw : Qle (mixe_qpow (1 - projT1 kappa n)%Q kstar)
                      (mixe_qpow q1 kstar))
      by (apply rb_qpow_mono_base; assumption).
    assert (HA0 : Qle 0 (mixe_qpow (1 - projT1 kappa n)%Q kstar))
      by (apply mixe_qpow_nonneg; exact Hdn0).
    assert (HB0 : Qle 0 (mixe_qpow q1 kstar))
      by (apply mixe_qpow_nonneg; exact Hq1le0).
    assert (HMge : Qle 0 M) by (apply (Qlt_le_weak 0%Q M); exact HM0).
    assert (Hx : Qle (mixe_qpow (1 - projT1 kappa n)%Q kstar * projT1 TV0 n) T).
    { assert (Hs1 : Qle (mixe_qpow (1 - projT1 kappa n)%Q kstar * projT1 TV0 n)
                        (mixe_qpow (1 - projT1 kappa n)%Q kstar * M)).
      { rewrite (Qmult_comm (mixe_qpow (1 - projT1 kappa n)%Q kstar)
                            (projT1 TV0 n)).
        rewrite (Qmult_comm (mixe_qpow (1 - projT1 kappa n)%Q kstar) M).
        apply (Qmult_le_compat_r (projT1 TV0 n) M
                 (mixe_qpow (1 - projT1 kappa n)%Q kstar) Hab HA0). }
      assert (Hs2 : Qle (mixe_qpow (1 - projT1 kappa n)%Q kstar * M)
                        (mixe_qpow q1 kstar * M)).
      { apply (Qmult_le_compat_r (mixe_qpow (1 - projT1 kappa n)%Q kstar)
                 (mixe_qpow q1 kstar) M Hpw HMge). }
      exact (Qle_trans _ _ _ (Qle_trans _ _ _ Hs1 Hs2) Hok). }
    (* budget_n > 2T，x_n ≤ T ⟹ T < budget_n − x_n *)
    assert (H2b : (eps_b == 2 * T)%Q) by (unfold T; ring).
    rewrite H2b in Hqb.
    assert (Hrd8 : (2 * T)%Q == (T + T)%Q) by ring.
    assert (HTb : Qlt T (projT1 budget n - T)%Q).
    { apply (proj2 (Qlt_minus_iff T (projT1 budget n - T)%Q)).
      assert (Hqb2 : (0 < projT1 budget n + - (2 * T))%Q).
      { exact (proj1 (Qlt_minus_iff (2 * T)%Q (projT1 budget n)%Q) Hqb). }
      assert (Hrq : ((projT1 budget n - T) + - T)%Q
                    == (projT1 budget n + - (2 * T))%Q) by ring.
      rewrite Hrq. exact Hqb2. }
    apply (Qlt_le_trans T (projT1 budget n - T)%Q
            (projT1 budget n
             - mixe_qpow (1 - projT1 kappa n)%Q kstar * projT1 TV0 n)%Q).
    - exact HTb.
    - unfold Qminus.
      apply (Qplus_le_compat (projT1 budget n) (projT1 budget n)
               (Qopp T)
               (Qopp (mixe_qpow (1 - projT1 kappa n)%Q kstar * projT1 TV0 n))
               (Qle_refl (projT1 budget n))).
      + apply (Qopp_le_compat
                 (mixe_qpow (1 - projT1 kappa n)%Q kstar * projT1 TV0 n) T).
        exact Hx. }
  (* 5. 严格形 → Bishop 形结论 *)
  exists kstar. unfold rb_gval, real_le_b. intros e He.
  apply (real_lt_trans
           (real_mult (powb_pow (rb_delta0 kappa) kstar) TV0)
           budget (real_plus budget e)).
  - exists T. split.
    + apply Qlt_to_QltT. exact HT0.
    + exists (Nk + N1 + Nb). intros n Hn. apply NatLe_drop in Hn.
      apply Qlt_to_QltT. apply (Hpt n Hn).
  - apply real_lt_plus_r_zero. exact He.
Qed.

(* ============================================================ *)
(* 检验审计：提取 Obj.magic 计数应为 0 + 语句假设闭包                     *)
(* ============================================================ *)

Extraction "r2b_G3.ml" mix_k_select_bishop rb_bishop_search rb_cond.

Print Assumptions mix_k_select_bishop.
Print Assumptions rb_bishop_search_ok.
Print Assumptions rb_log_return_bound.
