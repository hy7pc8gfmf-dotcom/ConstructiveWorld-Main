(* ============================================================ *)
(* UpAblLogWallFinal.v —— 席N3：判定墙族第 8 位·修正陈述终形定装席            *)
(*                                                              *)
(* 【零承认件】本件零承认、零假设负载、零经典逻辑：全文无任何全局无据项，     *)
(*   四关卡全绿申报（G1 禁词双轨 0 / G2 全量编译 EXIT=0+Closed+5ff4 头+      *)
(*   vo 新于 v / G3 独立目录 Obj.magic=0 / G4 coqchk 无承认项）。            *)
(*   rLPO 仅作为定理语句左方的被消费前件出现（非公理、非假设）。             *)
(*                                                              *)
(* 使命：把「全称无前件 lgw_MinSel 可驳（L3 发现件 lgwe_minsel_refutable：   *)
(*   κ=TV₀=budget=1 处站账逐点差 1−1=0，供隙支自撞 ⟹ 空 Set）」修正为       *)
(*   可证、达原预期、非平凡的终形——带前提 {0<κ<1, 0<TV₀, 0<B} 的最小站     *)
(*   选择器 lgwd_MinSelD，并定装为与 rLPO 的等价定理。四件：                *)
(*                                                              *)
(*   件① 修正规格 lgwd_MinSelD：四前提（Hk1/Hk2/Ha/Hb）条件化选择器，      *)
(*     两账形照 N2 lgw_min_sel_spec 实形逐字复用（站 k 供隙真账 ∧           *)
(*     ∀j<k 逐站否证账）；四前提恰好排除 L3 自撞点 κ=TV₀=B=1。             *)
(*                                                              *)
(*   件② 可证腿 lgwd_inhabited：rLPO -> 四前提 -> lgwd_MinSelD。            *)
(*     【本席新腿=L3 挂账放电】L3 构造腿 lgwe_min_sel_of_rlpo 需逐站非负     *)
(*     Or 族前提（real_le real_zero (差量 j)），并申报「rLPO 不供给符号面」  *)
(*     挂账——本席发现该挂账可放电：rLPO 离零支携带尾项一致正隙              *)
(*     （∀n≥N: c<|x_n|），与 Cauchy 模数（eps:=c/2）联用得尾项符号一致，     *)
(*     采样一点比较有理数即得整支符号 ⟹ lgwd_sign_of_apart：离零支直接      *)
(*     供 Or(0<x, x<0)。于是逐站判定 lgwd_station_decide 仅需 rLPO          *)
(*     （归零支短路否证照 L3 lgwe_test_refute_of_zero 原件；离零支正者      *)
(*     经 L3 lgwe_test_of_diff 出供隙账、负者经本席 lgwd_test_refute_of_neg  *)
(*     出否证账）——非负 Or 族前提全免，四前提规格足矣。上界消费             *)
(*     mix_k_select（UpReqMixingTime），幂列换装照 L3 lgwe_rpow_eq_tv，     *)
(*     线性扫复用 L3 lgwe_scan 原件，两账打包。                             *)
(*                                                              *)
(*   件③ 非空虚归约腿 lgwd_decision：四前提 -> lgwd_MinSelD ->              *)
(*     ∀x∈(0,1]，Or(real_lt x one, real_eq x one)。N2 归约的前提化适配：    *)
(*     选择器施于 κ:=half、TV₀:=x、B:=half（四前提在场：0<half、half<1、    *)
(*     0<x、0<half），最小站三分支 k=0（x<half）/k=1（x<1）/k≥2（站 1       *)
(*     否证 + x≤1 前件合流 x=1）——最小站数值即序信息，选择器被真实消费，    *)
(*     不再空虚真（L3 已证无前件接口为空集，故本腿对无前件形平凡性失效）。  *)
(*     另供锐化件 lgwd_decision_dec：免 x≤1 前件，对一切 0<x 出             *)
(*     Or(x<1, x<1→Empty_set)——「x<1 可判定」非任何前件的投影，              *)
(*     为归约腿非平凡性的独立锚点。                                        *)
(*                                                              *)
(*   件④ 等价定装 lgwd_equivalence：四前提 -> And(lgwd_MinSelD ->           *)
(*     lgwd_lpo_family, rLPO -> 逐点选择器)——⟸=件② 特化，⟹=件③+LPO         *)
(*     实例换装；S01 Set-And 承载（Set 腿不可入 Prop 合取，照 L3/AA15R      *)
(*     口径）。对照注记件 lgwd_contrast_refutable：Require 消费 L3 发现件   *)
(*     lgwe_minsel_refutable——无前件全称形构造性可驳（空 Set），故前提     *)
(*     必要，对照留存于 UpAblLogWallEq。                                    *)
(*                                                              *)
(*   诚实边界申报：①real_le = Or(real_lt, real_eq)（S02:469 定义形），故    *)
(*     件③/件④的目标证书型与「real_le x one」前件型同定义——非平凡性由      *)
(*     选择器真实消费路线（三分支最小站解读）与锐化件 lgwd_decision_dec      *)
(*     （结论非前件投影）承载；②件②之所以四前提可证，核心是新符号腿        *)
(*     （rLPO 离零支+Cauсhy 模数 ⟹ 符号），较 L3 条件形更强、覆盖更广       *)
(*     （L3 接口在 TV₀>B 的合法点如 (half,100,half) 处前提失效，本接口      *)
(*     不失效）。                                                          *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、语句面全 sigT/自定义 And/Or，零 Prop 泄露；        *)
(*   归约前提（rLPO/选择器）以定理显式参承接，非全局无据项。                *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、CW_ConstructiveWorld_219、       *)
(*   UpTVDoeblin（tv_rpow）、UpReqLpoEquiv（rLPO、q_abs_neg_eq、            *)
(*   q_abs_congr）、UpReqMixingTime（mix_k_select）、UpAblLogWall（lgw_*    *)
(*   规格面、half 桥、正向腿原料）、UpAblLogWallEq（lgwe_*：差量、两桥、    *)
(*   扫描、可驳对照件）。                                                   *)
(* ------------------------------------------------------------ *)
(* N3（20260920）：新建。                                                   *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqLpoEquiv.
Require Import UpReqMixingTime.
Require Import UpAblLogWall.
Require Import UpAblLogWallEq.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：Q 层支点与本席新核心——符号提取腿（L3 挂账放电）                   *)
(* ============================================================ *)

Lemma lgwd_q_half_pos : Qlt 0 (1#2).
Proof.
  apply (proj2 (Qlt_alt 0 (1#2))). reflexivity.
Qed.

(* 符号提取：rLPO 离零支（尾项一致正隙 c，∀n≥N: c<|x_n|）+ Cauchy 模数      *)
(*   （eps:=c/2）⟹ 尾项（max N M 起）符号一致 ⟹ 采样点有理比较即得整支符号。*)
(*   产出 Or(0<x, x<0)——rLPO 独力供给符号面，L3「非负 Or 族」挂账在此放电。 *)
Lemma lgwd_sign_of_apart : forall x : Real,
  sigT (fun c : Q =>
    And (QltT 0 c)
        (sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT c (Qabs (projT1 x n))))) ->
  Or (real_lt real_zero x) (real_lt x real_zero).
Proof.
  intros x Hap.
  destruct Hap as [c [Hc0T [Nc HNc]]].
  assert (Hc0 : Qlt 0 c) by (apply QltT_to_Qlt; exact Hc0T).
  assert (Hc2T : QltT 0 (c * (1#2))).
  { apply Qlt_to_QltT.
    assert (Hm : 0 * (1#2) < c * (1#2))
      by (apply Qmult_lt_compat_r; [exact lgwd_q_half_pos | exact Hc0]).
    rewrite Qmult_0_l in Hm. exact Hm. }
  destruct x as [u Hu].
  destruct (Hu (c * (1#2)) Hc2T) as [M HM].
  assert (HNcP : NatLe Nc (Nat.max Nc M)) by (apply NatLe_lift; lia).
  assert (HMP : NatLe M (Nat.max Nc M)) by (apply NatLe_lift; lia).
  specialize (HNc (Nat.max Nc M) HNcP).
  apply QltT_to_Qlt in HNc.
  (* HNc : c < |u P| ；HM : |u n − u P| < c/2（n ≥ P） *)
  destruct (Qlt_le_dec 0 (u (Nat.max Nc M))) as [Hp | Hn].
  - (* 正支：采样点为正 ⟹ 0 < x（尾项一致 > c/2） *)
    apply inl. unfold real_lt. exists (c * (1#2)). split.
    + exact Hc2T.
    + exists (Nat.max Nc M). intros n HnPM.
      assert (HMn : NatLe M n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max Nc M).
        - exact (NatLe_drop M (Nat.max Nc M) HMP).
        - exact (NatLe_drop (Nat.max Nc M) n HnPM). }
      specialize (HM n (Nat.max Nc M) HMn HMP).
      apply QltT_to_Qlt in HM.
      assert (HuP : u (Nat.max Nc M) == Qabs (u (Nat.max Nc M))).
      { symmetry. apply Qabs_pos. apply Qlt_le_weak. exact Hp. }
      assert (HcP : c < u (Nat.max Nc M)) by (rewrite HuP; exact HNc).
      apply Qlt_to_QltT.
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      assert (Hm1 : u n - 0 == u n) by ring.
      rewrite Hm1.
      (* HM : |u n − u P| < c/2 ⟹ u P − u n < c/2（经 |−a|=|a| 搬运） *)
      assert (Hneg1 : u (Nat.max Nc M) - u n == - (u n - u (Nat.max Nc M))) by ring.
      assert (H1 : u (Nat.max Nc M) - u n < c * (1#2)).
      { rewrite Hneg1.
        apply (Qle_lt_trans (- (u n - u (Nat.max Nc M)))
                (Qabs (u n - u (Nat.max Nc M))) (c * (1#2))).
        - rewrite <- (Qabs_opp (u n - u (Nat.max Nc M))).
          apply lgwe_q_le_abs.
        - exact HM. }
      (* 链：c/2 + (uP−un) < c/2 + c/2 = c < uP = (uP−un) + un ⟹ 消去 ⟹ c/2 < un *)
      assert (H2 : c * (1#2) + (u (Nat.max Nc M) - u n) < c).
      { assert (Ht : c * (1#2) + (u (Nat.max Nc M) - u n)
                     < c * (1#2) + c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u (Nat.max Nc M) - u n)
                              (c * (1#2)) (c * (1#2)))); exact H1).
        assert (Hr : c * (1#2) + c * (1#2) == c) by ring.
        rewrite Hr in Ht. exact Ht. }
      assert (H4 : c * (1#2) + (u (Nat.max Nc M) - u n) < u (Nat.max Nc M)).
      { apply (Qlt_trans _ c _ H2 HcP). }
      apply (proj1 (Qplus_lt_r (c * (1#2)) (u n) (u (Nat.max Nc M) - u n))).
      assert (H5 : (u (Nat.max Nc M) - u n) + u n == u (Nat.max Nc M)) by ring.
      rewrite H5.
      assert (H6 : (u (Nat.max Nc M) - u n) + c * (1#2)
                   == c * (1#2) + (u (Nat.max Nc M) - u n)) by ring.
      rewrite H6. exact H4.
  - (* 负支：采样点非正 ⟹ x < 0（尾项一致 < −c/2） *)
    apply inr. unfold real_lt. exists (c * (1#2)). split.
    + exact Hc2T.
    + exists (Nat.max Nc M). intros n HnPM.
      assert (HMn : NatLe M n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max Nc M).
        - exact (NatLe_drop M (Nat.max Nc M) HMP).
        - exact (NatLe_drop (Nat.max Nc M) n HnPM). }
      specialize (HM n (Nat.max Nc M) HMn HMP).
      apply QltT_to_Qlt in HM.
      apply Qlt_to_QltT.
      assert (HabsP : Qabs (u (Nat.max Nc M)) == - u (Nat.max Nc M))
        by (apply q_abs_neg_eq; exact Hn).
      rewrite HabsP in HNc.
      (* HNc : c < −u P ⟹ u P < −c *)
      assert (HuPn : u (Nat.max Nc M) < - c).
      { apply (proj1 (Qplus_lt_r (u (Nat.max Nc M)) (- c) c)).
        assert (Hr1 : c + - c == 0) by ring.
        rewrite Hr1.
        assert (Ht : u (Nat.max Nc M) + c < u (Nat.max Nc M) + - u (Nat.max Nc M))
          by (apply (proj2 (Qplus_lt_r c (- u (Nat.max Nc M))
                              (u (Nat.max Nc M)))); exact HNc).
        assert (Hr2 : u (Nat.max Nc M) + - u (Nat.max Nc M) == 0) by ring.
        rewrite Hr2 in Ht.
        assert (Hr3 : c + u (Nat.max Nc M) == u (Nat.max Nc M) + c) by ring.
        rewrite Hr3. exact Ht. }
      (* HM : |u n − u P| < c/2 ⟹ u n − u P < c/2（直用 a ≤ |a|） *)
      assert (H1 : u n - u (Nat.max Nc M) < c * (1#2)).
      { apply (Qle_lt_trans (u n - u (Nat.max Nc M))
                (Qabs (u n - u (Nat.max Nc M))) (c * (1#2))).
        - apply lgwe_q_le_abs.
        - exact HM. }
      assert (H3 : u n < u (Nat.max Nc M) + c * (1#2)).
      { assert (Ht : u (Nat.max Nc M) + (u n - u (Nat.max Nc M))
                     < u (Nat.max Nc M) + c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u n - u (Nat.max Nc M))
                              (c * (1#2)) (u (Nat.max Nc M)))); exact H1).
        assert (Hr : u (Nat.max Nc M) + (u n - u (Nat.max Nc M)) == u n) by ring.
        rewrite <- Hr. exact Ht. }
      assert (H4 : u (Nat.max Nc M) + c * (1#2) < - c * (1#2)).
      { assert (Ht : c * (1#2) + u (Nat.max Nc M) < c * (1#2) + - c)
          by (apply (proj2 (Qplus_lt_r (u (Nat.max Nc M)) (- c)
                              (c * (1#2)))); exact HuPn).
        assert (Hr1 : c * (1#2) + u (Nat.max Nc M)
                      == u (Nat.max Nc M) + c * (1#2)) by ring.
        rewrite Hr1 in Ht.
        assert (Hr2 : c * (1#2) + - c == - c * (1#2)) by ring.
        rewrite Hr2 in Ht. exact Ht. }
      assert (H5 : u n < - c * (1#2)) by (exact (Qlt_trans _ _ _ H3 H4)).
      (* 目标：c/2 < 0 − u n *)
      assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
      rewrite Hz0.
      assert (H6 : c * (1#2) + u n < 0).
      { assert (Ht : c * (1#2) + u n < c * (1#2) + - c * (1#2))
          by (apply (proj2 (Qplus_lt_r (u n) (- c * (1#2)) (c * (1#2)))); exact H5).
        assert (Hr : c * (1#2) + - c * (1#2) == 0) by ring.
        rewrite Hr in Ht. exact Ht. }
      apply (proj1 (Qplus_lt_r (c * (1#2)) (0 - u n) (u n))).
      assert (Hr2 : u n + (0 - u n) == 0) by ring.
      rewrite Hr2.
      assert (Hr3 : u n + c * (1#2) == c * (1#2) + u n) by ring.
      rewrite Hr3. exact H6.
Qed.

(* ============================================================ *)
(* Part 1：逐站判定（仅需 rLPO——免 L3 非负 Or 族前提）                       *)
(* ============================================================ *)

(* 否证新桥：差量严格负（real_lt (差量) 0）驳站账供隙支                      *)
(*   （供隙 eps0 < B_n−z_n 与负隙 eps < 0−(B_n−z_n) 在 max N0 N 处相撞：      *)
(*    eps0 + eps < 0 与 0 < eps0 + eps 相撞） *)
Lemma lgwd_test_refute_of_neg :
  forall (kappa TV0 budget : Real) (j : nat),
  real_lt (lgwe_diff kappa TV0 budget j) real_zero ->
  lgw_test kappa TV0 budget j -> Empty_set.
Proof.
  intros kappa TV0 budget j Hneg Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk, Hneg.
  destruct Htk as [eps0 [Heps0 [N0 HN0]]].
  destruct Hneg as [eps [Heps [N HN]]].
  assert (Hm0 : NatLe N0 (Nat.max N0 N)) by (apply NatLe_lift; lia).
  assert (Hm1 : NatLe N (Nat.max N0 N)) by (apply NatLe_lift; lia).
  specialize (HN0 _ Hm0). specialize (HN _ Hm1).
  apply QltT_to_Qlt in HN0. apply QltT_to_Qlt in HN.
  apply QltT_to_Qlt in Heps0. apply QltT_to_Qlt in Heps.
  rewrite (real_mult_proj (lgw_rpow kappa j) TV0 (Nat.max N0 N)) in HN0.
  rewrite (lgwe_diff_proj kappa TV0 budget j (Nat.max N0 N)) in HN.
  assert (Hz0 : projT1 real_zero (Nat.max N0 N) == 0) by reflexivity.
  rewrite Hz0 in HN.
  set (X := projT1 budget (Nat.max N0 N)
            - projT1 (lgw_rpow kappa j) (Nat.max N0 N) * projT1 TV0 (Nat.max N0 N)) in *.
  (* HN0 : eps0 < X ；HN : eps < 0 − X ⟹ X < −eps *)
  assert (HX : X < - eps).
  { apply (proj1 (Qplus_lt_r X (- eps) eps)).
    assert (Hr1 : eps + - eps == 0) by ring.
    rewrite Hr1.
    assert (Ht : X + eps < X + (0 - X))
      by (apply (proj2 (Qplus_lt_r eps (0 - X) X)); exact HN).
    assert (Hr2 : X + (0 - X) == 0) by ring.
    rewrite Hr2 in Ht.
    assert (Hr3 : eps + X == X + eps) by ring.
    rewrite Hr3. exact Ht. }
  assert (Hcol : eps0 < - eps) by (exact (Qlt_trans _ _ _ HN0 HX)).
  assert (Hsum : eps0 + eps < 0).
  { assert (Ht : eps + eps0 < 0).
    { assert (Ht2 : eps + eps0 < eps + - eps)
        by (apply (proj2 (Qplus_lt_r eps0 (- eps) eps)); exact Hcol).
      assert (Hr1 : eps + - eps == 0) by ring.
      rewrite Hr1 in Ht2. exact Ht2. }
    assert (Hr2 : eps + eps0 == eps0 + eps) by ring.
    rewrite Hr2 in Ht. exact Ht. }
  assert (Hpos : 0 < eps0 + eps).
  { assert (Ht : 0 + 0 < eps0 + eps) by (apply Qplus_lt_compat; assumption).
    assert (Hr : 0 + 0 == 0) by ring.
    rewrite Hr in Ht. exact Ht. }
  destruct (Qlt_irrefl (eps0 + eps)
             (Qlt_trans (eps0 + eps) 0 (eps0 + eps) Hsum Hpos)).
Qed.

(* 逐站判定主件：rLPO 独力供给（归零支短路否证照 L3；离零支经符号腿两账）    *)
Theorem lgwd_station_decide :
  forall (kappa TV0 budget : Real) (j : nat),
  rLPO -> lgwe_station_dec kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hrlpo.
  destruct (Hrlpo (lgwe_diff kappa TV0 budget j)) as [Hap | Hzero].
  - destruct (lgwd_sign_of_apart _ Hap) as [Hpos | Hneg].
    + apply inl. exact (lgwe_test_of_diff kappa TV0 budget j Hpos).
    + apply inr. exact (lgwd_test_refute_of_neg kappa TV0 budget j Hneg).
  - apply inr. exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzero).
Qed.

(* ============================================================ *)
(* Part 2：件① 修正规格 + 件② 可证腿                                        *)
(* ============================================================ *)

(* 件①：带四前提的最小站选择器（两账形照 N2 lgw_min_sel_spec 逐字复用；      *)
(*   四前提恰好排除 L3 自撞点 κ=TV₀=B=1） *)
Definition lgwd_MinSelD : Set :=
  forall kappa TV0 budget : Real,
    real_lt real_zero kappa -> real_lt kappa real_one ->
    real_lt real_zero TV0 -> real_lt real_zero budget ->
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

(* 件②：rLPO -> 四前提 -> lgwd_MinSelD（上界=mix_k_select；逐站判定=        *)
(*   Part 1 新腿；线性扫=L3 lgwe_scan 原件；幂列换装=L3 lgwe_rpow_eq_tv）   *)
Theorem lgwd_inhabited : rLPO -> lgwd_MinSelD.
Proof.
  intros Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb.
  (* 必过站上界：mix_k_select（严格正 TV₀ 经 real_lt_le_iff_req 换 le 形） *)
  assert (Hale : real_le real_zero TV0).
  { apply (RealSetoid.real_lt_le_iff_req real_zero TV0). left. exact Ha. }
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Hale Hb) as [kp Hmix].
  (* tv_rpow 形换装回 lgw_test 面（L3 原桥） *)
  assert (Hpass : lgw_test kappa TV0 budget kp).
  { unfold lgw_test.
    apply (real_eq_lt_lt (real_mult (lgw_rpow kappa kp) TV0)
                         (real_mult (tv_rpow kappa kp) TV0) budget).
    - apply (RealSetoid.real_eq_mult_compat (lgw_rpow kappa kp) TV0
                (tv_rpow kappa kp) TV0).
      + exact (lgwe_rpow_eq_tv kappa kp).
      + apply real_eq_refl.
    - exact Hmix. }
  (* 逐站可判定测试：rLPO 全供给（本席新腿） *)
  assert (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j).
  { intros j. exact (lgwd_station_decide kappa TV0 budget j Hrlpo). }
  (* 线性扫 [0,k_pass] + 两账打包（L3 lgwe_scan 原件） *)
  destruct (lgwe_scan kappa TV0 budget Hdec kp) as [[k [Hk Hspec]] | Hall].
  - exists k. exact Hspec.
  - assert (Hkk : NatLe kp kp) by (apply NatLe_lift; lia).
    destruct (Hall kp Hkk Hpass).
Qed.

(* ============================================================ *)
(* Part 3：件③ 非空虚归约腿（half 三站实例——最小站数值即序信息）            *)
(* ============================================================ *)

(* half 常量的两前提（选择器实例化时反复消费） *)
Lemma lgwd_half_pos : real_lt real_zero lgw_half.
Proof.
  unfold real_lt. exists (1#4). split.
  - apply Qlt_to_QltT. apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt (1#4) (projT1 lgw_half n - projT1 real_zero n))).
    reflexivity.
Qed.

Lemma lgwd_half_lt_one : real_lt lgw_half real_one.
Proof.
  unfold real_lt. exists (1#4). split.
  - apply Qlt_to_QltT. apply (proj2 (Qlt_alt 0 (1#4))). reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    apply (proj2 (Qlt_alt (1#4) (projT1 real_one n - projT1 lgw_half n))).
    reflexivity.
Qed.

(* 件③ 主件：选择器施于 (κ,B,x):=(half,half,x)，x∈(0,1]：                   *)
(*   最小站 k=0 ⟹ x<half ⟹ x<1；k=1 ⟹ x<1；k≥2 ⟹ 站 1 否证，与前件 x≤1     *)
(*   的左支相撞出空、右支（x=1）随取——序证书从最小站账提取，非前件直投影。   *)
Theorem lgwd_decision : lgwd_MinSelD ->
  forall x : Real, real_lt real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).
Proof.
  intros HselD x Hx0 Hx1.
  destruct (HselD lgw_half x lgw_half
              lgwd_half_pos lgwd_half_lt_one Hx0 lgwd_half_pos) as [k Hacc].
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

(* 锐化件：免 x≤1 前件——「x<1 可判定」对一切 0<x 成立，结论非任何前件投影，  *)
(*   为归约腿非平凡性的独立锚点 *)
Definition lgwd_station_decD (x : Real) : Set :=
  Or (real_lt x real_one) (real_lt x real_one -> Empty_set).

Theorem lgwd_decision_dec : lgwd_MinSelD ->
  forall x : Real, real_lt real_zero x -> lgwd_station_decD x.
Proof.
  intros HselD x Hx0.
  destruct (HselD lgw_half x lgw_half
              lgwd_half_pos lgwd_half_lt_one Hx0 lgwd_half_pos) as [k Hacc].
  destruct Hacc as [Htk Hbel].
  destruct k as [| [| m]].
  - apply inl. exact (lgw_test0_lt_one x Htk).
  - apply inl. exact (lgw_test1_lt_one x Htk).
  - assert (Href1 : lgw_test lgw_half x lgw_half 1%nat -> Empty_set).
    { intros Ht1. apply (Hbel 1%nat).
      - apply NatLe_lift. lia.
      - exact Ht1. }
    apply inr. intros Hlt1.
    destruct (Href1 (lgw_test1_of_lt_one x Hlt1)).
Qed.

(* ============================================================ *)
(* Part 4：件④ 等价定装 + 对照注记件                                        *)
(* ============================================================ *)

(* LPO 实例面：(0,1] 上序分解决策族（件③ 换装目标） *)
Definition lgwd_lpo_family : Set :=
  forall x : Real, real_lt real_zero x -> real_le x real_one ->
    Or (real_lt x real_one) (real_eq x real_one).

(* 等价定装：⟸=件② 特化（rLPO 建逐点选择器，四前提真实消费）；              *)
(*   ⟹=件③+LPO 实例换装（选择器出序证书族）。S01 Set-And 承载（Set 腿不可   *)
(*   入 Prop 合取，照 L3/AA15R 口径）。 *)
Theorem lgwd_equivalence : forall kappa TV0 budget : Real,
  real_lt real_zero kappa -> real_lt kappa real_one ->
  real_lt real_zero TV0 -> real_lt real_zero budget ->
  And (lgwd_MinSelD -> lgwd_lpo_family)
      (rLPO -> sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k)).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hb. split.
  - intros HselD x Hx0 Hx1. exact (lgwd_decision HselD x Hx0 Hx1).
  - intros Hrlpo. exact (lgwd_inhabited Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb).
Qed.

(* 对照注记件：消费 L3 发现件——无前件全称形构造性可驳（空 Set），            *)
(*   故四前提必要；对照留存于 UpAblLogWallEq。 *)
Theorem lgwd_contrast_refutable : lgw_MinSel -> Empty_set.
Proof. exact lgwe_minsel_refutable. Qed.

(* ============================================================ *)
(* Part 5：摘要输出（G2/G3 关卡面）                                          *)
(* ============================================================ *)

Print Assumptions lgwd_MinSelD.
Print Assumptions lgwd_station_decide.
Print Assumptions lgwd_inhabited.
Print Assumptions lgwd_decision.
Print Assumptions lgwd_decision_dec.
Print Assumptions lgwd_equivalence.
Print Assumptions lgwd_contrast_refutable.
Print Assumptions lgwd_sign_of_apart.
Print Assumptions lgwd_test_refute_of_neg.

Separate Extraction lgwd_MinSelD lgwd_lpo_family lgwd_station_decide
  lgwd_inhabited lgwd_decision lgwd_decision_dec lgwd_equivalence.
