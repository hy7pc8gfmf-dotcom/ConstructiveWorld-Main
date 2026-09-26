(* ============================================================ *)
(* UpAblLogWallEq.v —— 最小站选择器与 rLPO 的双向等价（条件化接口）         *)
(*                                                                *)
(* 使命：本件把 UpAblLogWall 的单向归约补全为双向等价 lgwe_equivalence：     *)
(*   正向 = lgw_lpo_of_min_sel（Require 复用）；反向 = lgwe_min_sel_of_rlpo  *)
(*   （rLPO ⟹ 条件化选择器接口 lgwe_MinSelC）；合取以 Qed 收尾，            *)
(*   非提取面，体例同 UpReqLpoEquiv 的 lpn_equivalence。                     *)
(*                                                                *)
(* 空集定理 lgwe_minsel_refutable：全称无前提接口 lgw_MinSel 为空集——取     *)
(*   kappa=TV0=budget=real_one，站点测试 test k 逐点差 = 1−1 = 0，           *)
(*   供隙支 eps<0 与 0<eps 矛盾，逐站可驳 ⟹ lgw_MinSel -> Empty_set          *)
(*   为闭项定理。推论：                                                     *)
(*   ①「rLPO -> lgw_MinSel」若可证则立得 rLPO -> Empty_set，故全称无前提    *)
(*     接口的正向构造构造性不可能——字面形式的双向等价不可达；               *)
(*   ②「lgw_MinSel 经典可满足」的说法被本件精化：该接口连经典也不可满足     *)
(*     （kappa=TV0=budget=real_one 处最小站不存在），lgw_lpo_of_min_sel      *)
(*     作为条件定理仍然成立但前提恒假（空虚真）。                           *)
(*                                                                *)
(* 正向构造（诚实条件化）lgwe_min_sel_of_rlpo，rLPO 的三段使用路线：        *)
(*   ① 可判定测试 lgwe_station_decide：rLPO 施于站差量                     *)
(*     lgwe_diff j := budget − kappa^j·TV0（real_plus/real_opp 减法形）：   *)
(*     rLPO 归零支 ⟹ 免序数据直接否证（rLPO 的实质使用点）；离零支 ⟹       *)
(*     使用该站非负 Or 形（real_le real_zero 差量）完成两态判定——          *)
(*     非负 Or 形是 rLPO 不供给的符号面序数据（rLPO 只有离零/归零二分，     *)
(*     无正负向），如实注记为序数据缺口。                                   *)
(*   ② 有界线性搜索 lgwe_scan：搜索上界不任意取，使用 mix_k_select         *)
(*     （UpReqMixingTime 四正性前提）取必过站 k_pass，nat 线性扫            *)
(*     [0,k_pass] 找首过站（过站集沿幂列递减向上封闭）。                    *)
(*   ③ 两态合成：首过站真态（供隙支）+ 此前逐站否证态（否证支），           *)
(*     合成 lgw_min_sel_spec（与 UpAblLogWall 规格同形，零改规格）。         *)
(*   幂列转换：mix_k_select 返回 tv_rpow 形，经 lgwe_rpow_eq_tv             *)
(*   （lgw_rpow 与 tv_rpow 同构形的 real_eq 逐站迁移）+ real_eq_lt_lt       *)
(*   转回 lgw_test 形；tv/lgw 两幂族 base real_one、步 real_mult 同构。     *)
(*                                                                *)
(* 等价合成 lgwe_equivalence：正向肢 = lgw_lpo_of_min_sel（Require 复用）； *)
(*   反向肢 = lgwe_min_sel_of_rlpo（rLPO -> lgwe_MinSelC，lgwe_MinSelC =    *)
(*   四正性前提+非负 Or 族条件化的选择器接口）。合成 Prop 合取（/\，Qed     *)
(*   收尾，非提取面），照 UpReqLpoEquiv 的 lpn_equivalence 体例。            *)
(*   诚实边界：反向肢接口为条件化形——全称无前提形已被 lgwe_minsel_refutable *)
(*   驳斥，条件化是唯一可行路线；条件里的非负 Or 族在 Real 乘法单调性引理   *)
(*                                                                *)
(* 构造性注记：纯构造性、零承认；选择器本体 sigT/Set 形（lgwe_MinSelC、     *)
(*   lgwe_scan、lgwe_station_dec 全 Set），合取走 Prop Qed 形               *)
(*   （体例同 UpReqLpoEquiv）。                                             *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、CW_ConstructiveWorld_219、       *)
(*   UpTVDoeblin（tv_rpow）、UpReqLpoEquiv（rLPO、q_abs_congr）、            *)
(*   UpReqMixingTime（mix_k_select）、UpAblLogWall（lgw_* 规格与正向肢）。   *)
(* 对标：stdlib QArith/Arith；mathlib 无构造性对应物。                      *)
(* 编译配方：Rocq 9.1 直调 coqc + cpu_guard（-LoadLimit 85 -CoreN 2），     *)
(*   输出至临时目录，树内零写入。                                           *)
(* ------------------------------------------------------------ *)
(*                                                                *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
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
Require Import UpReqLpoEquiv.
Require Import UpReqMixingTime.
Require Import UpAblLogWall.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 站差量（Real 减法形：real_plus budget (real_opp 幂积)）               *)
(* ============================================================ *)

Definition lgwe_diff (kappa TV0 budget : Real) (j : nat) : Real :=
  real_plus budget (real_opp (real_mult (lgw_rpow kappa j) TV0)).

Lemma lgwe_diff_proj : forall (kappa TV0 budget : Real) (j n : nat),
  projT1 (lgwe_diff kappa TV0 budget j) n ==
  projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n.
Proof.
  intros kappa TV0 budget j n. unfold lgwe_diff.
  rewrite (real_plus_proj budget (real_opp (real_mult (lgw_rpow kappa j) TV0)) n).
  rewrite (real_opp_proj (real_mult (lgw_rpow kappa j) TV0) n).
  rewrite (real_mult_proj (lgw_rpow kappa j) TV0 n).
  ring.
Qed.

(* Q 层辅助引理：a <= |a|（Qabs_pos / 负支 Qopp_le_compat 两分）            *)
Lemma lgwe_q_le_abs : forall a : Q, a <= Qabs a.
Proof.
  intros a. destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)). apply Qle_refl.
  - rewrite (q_abs_neg_eq a Hneg).
    apply (Qle_trans a 0 (- a)).
    + exact Hneg.
    + apply (Qopp_le_compat a 0). exact Hneg.
Qed.

(* ============================================================ *)
(* §1 接口空集定理——全称无前提接口的构造性驳斥                             *)
(* ============================================================ *)

Lemma lgwe_rpow_one_proj : forall (k n : nat),
  projT1 (lgw_rpow real_one k) n == 1.
Proof.
  intros k. induction k as [|k IH]; intros n.
  - (* 归纳基座：lgw_rpow real_one 0 定义性归约至实幺元投影，右端显式取 1 *)
    exact (Qeq_refl 1).
  - cbn [lgw_rpow].
    rewrite (real_mult_proj real_one (lgw_rpow real_one k) n).
    rewrite IH.
    (* 归纳步：幺元投影恒 1，乘 1 后两端显式同为 1 *)
    exact (Qeq_refl 1).
Qed.

(* kappa=TV0=budget=real_one 处站点测试逐点差 = 1−1 = 0，供隙支自相矛盾 ⟹ 全称接口空集 *)
Theorem lgwe_minsel_refutable : lgw_MinSel -> Empty_set.
Proof.
  intros Hsel.
  destruct (Hsel real_one real_one real_one) as [k [Htk _]].
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  assert (HNN : NatLe N N) by (apply (NatLe_lift _ _ (Nat.le_refl N))).
  specialize (HN N HNN).
  apply QltT_to_Qlt in HN. apply QltT_to_Qlt in Heps.
  assert (Hz : projT1 real_one N
               - projT1 (real_mult (lgw_rpow real_one k) real_one) N == 0).
  { assert (H1 : projT1 real_one N == 1) by exact (Qeq_refl 1).
    rewrite H1.
    rewrite (real_mult_proj (lgw_rpow real_one k) real_one N).
    rewrite (lgwe_rpow_one_proj k N).
    rewrite H1. exact (Qeq_refl 0). }
  rewrite Hz in HN.
  destruct (Qlt_irrefl eps (Qlt_trans eps 0 eps HN Heps)).
Qed.

(* ============================================================ *)
(* §2 幂族转换桥（lgw_rpow 与 tv_rpow 同构形 real_eq 迁移）                 *)
(* ============================================================ *)

Lemma lgwe_rpow_eq_tv : forall (a : Real) (j : nat),
  real_eq (lgw_rpow a j) (tv_rpow a j).
Proof.
  intros a j. induction j as [|j IH].
  - apply real_eq_refl.
  - cbn [lgw_rpow tv_rpow].
    apply (RealSetoid.real_eq_mult_compat a (lgw_rpow a j) a (tv_rpow a j)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* ============================================================ *)
(* §3 站点测试双桥（供隙支直转 / 归零否证桥）                               *)
(* ============================================================ *)

(* 供隙支：real_lt 0 (差量) 与 lgw_test j 的投影内容同一（同一差量投影形） *)
Lemma lgwe_test_of_diff : forall (kappa TV0 budget : Real) (j : nat),
  real_lt real_zero (lgwe_diff kappa TV0 budget j) ->
  lgw_test kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hlt.
  unfold real_lt in Hlt. destruct Hlt as [eps [Heps [N HN]]].
  unfold lgw_test. unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    rewrite (lgwe_diff_proj kappa TV0 budget j n) in HN.
    assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
    rewrite Hz in HN.
    apply Qlt_to_QltT.
    rewrite (real_mult_proj (lgw_rpow kappa j) TV0 n).
    assert (Hm : projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n - 0
                 == projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n) by ring.
    rewrite Hm in HN.
    exact HN.
Qed.

(* 否证桥：差量归零形（任意 eps 存在 N 界内 |d_n|<eps）驳站点测试供隙支     *)
(*   （供隙 eps0 与归零 |d_n|<eps0 在 max N0 N1 处矛盾）                    *)
Lemma lgwe_test_refute_of_zero :
  forall (kappa TV0 budget : Real) (j : nat),
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (Qabs (projT1 (lgwe_diff kappa TV0 budget j) n)) eps)) ->
  lgw_test kappa TV0 budget j -> Empty_set.
Proof.
  intros kappa TV0 budget j Hz Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps0 [Heps0 [N0 HN0]]].
  destruct (Hz eps0 Heps0) as [N1 HN1].
  assert (Hm0 : NatLe N0 (Nat.max N0 N1)) by (apply (NatLe_lift _ _ (Nat.le_max_l N0 N1))).
  assert (Hm1 : NatLe N1 (Nat.max N0 N1)) by (apply (NatLe_lift _ _ (Nat.le_max_r N0 N1))).
  specialize (HN0 _ Hm0). specialize (HN1 _ Hm1).
  apply QltT_to_Qlt in HN0. apply QltT_to_Qlt in HN1.
  rewrite (real_mult_proj (lgw_rpow kappa j) TV0 (Nat.max N0 N1)) in HN0.
  rewrite (lgwe_diff_proj kappa TV0 budget j (Nat.max N0 N1)) in HN1.
  set (X := projT1 budget (Nat.max N0 N1)
            - projT1 (lgw_rpow kappa j) (Nat.max N0 N1) * projT1 TV0 (Nat.max N0 N1)) in *.
  assert (HX : X < eps0).
  { apply (Qle_lt_trans X (Qabs X) eps0).
    - apply lgwe_q_le_abs.
    - exact HN1. }
  destruct (Qlt_irrefl eps0 (Qlt_trans _ _ _ HN0 HX)).
Qed.

(* ============================================================ *)
(* §4 可判定测试（rLPO 实质使用点：归零支免序数据直接否证；                 *)
(*     离零支使用非负 Or 形完成两态判定——符号面为序数据缺口）               *)
(* ============================================================ *)

Definition lgwe_station_dec (kappa TV0 budget : Real) (j : nat) : Set :=
  Or (lgw_test kappa TV0 budget j)
     (lgw_test kappa TV0 budget j -> Empty_set).

Theorem lgwe_station_decide :
  forall (kappa TV0 budget : Real) (j : nat),
  rLPO -> real_le real_zero (lgwe_diff kappa TV0 budget j) ->
  lgwe_station_dec kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hrlpo Hnn.
  destruct (Hrlpo (lgwe_diff kappa TV0 budget j)) as [Hapart | Hzero].
  - (* rLPO 离零支（首支）：使用该站非负 Or 形（real_le 两支） *)
    unfold real_le in Hnn. destruct Hnn as [Hge | Heq0].
    + apply inl. exact (lgwe_test_of_diff kappa TV0 budget j Hge).
    + (* 非负 Or 右支（差量归零）与离零支矛盾得空 ⟹ 取否证支 *)
      apply inr. intros Htk.
      destruct Hapart as [c [Hc0 [Nc HNc]]].
      assert (Hzf : (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT (Qabs (projT1 (lgwe_diff kappa TV0 budget j) n)) eps))).
      { intros eps Heps. destruct (Heq0 eps Heps) as [N HN].
        exists N. intros n Hn. specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        assert (Hz0 : projT1 real_zero n == 0) by exact (Qeq_refl 0).
        rewrite Hz0 in HN.
        assert (H1 : (0 - projT1 (lgwe_diff kappa TV0 budget j) n)%Q
                     == (- projT1 (lgwe_diff kappa TV0 budget j) n)%Q) by ring.
        rewrite (q_abs_congr _ _ H1) in HN.
        rewrite (Qabs_opp (projT1 (lgwe_diff kappa TV0 budget j) n)) in HN.
        apply Qlt_to_QltT. exact HN. }
      exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzf Htk).
  - (* rLPO 归零支（次支）：免序数据否证短路 *)
    apply inr. exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzero).
Qed.

(* ============================================================ *)
(* §5 有界线性搜索（使用 mix_k_select 必过站作上界，nat 线性扫）            *)
(* ============================================================ *)

(* 搜索基座：站 0 过 ⟹ 首过站 0（无需否证任何站）；站 0 挡 ⟹ 全 [0,0] 否证 *)
Lemma lgwe_scan_O : forall (kappa TV0 budget : Real),
  (forall j : nat, lgwe_station_dec kappa TV0 budget j) ->
  Or
    (sigT (fun k : nat => And (NatLe k 0%nat) (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j 0%nat -> lgw_test kappa TV0 budget j -> Empty_set).
Proof.
  intros kappa TV0 budget Hdec.
  destruct (Hdec 0%nat) as [Hpass | Href].
  - apply inl. exists 0%nat. split.
    + apply (NatLe_lift _ _ (Nat.le_refl 0%nat)).
    + split.
      * exact Hpass.
      * intros j Hj _.
        assert (Hd : (Datatypes.S j <= 0)%nat) by (apply NatLe_drop; exact Hj).
        assert (HF : False) by exact (Nat.nle_succ_0 j Hd).
        destruct HF.
  - apply inr. intros j Hj Htj.
    assert (Hd : (j <= 0)%nat) by (apply NatLe_drop; exact Hj).
    assert (Hj0 : j = 0%nat) by exact (proj1 (Nat.le_0_r j) Hd).
    rewrite Hj0 in Htj. apply Href. exact Htj.
Qed.

(* 搜索步：前段 [0,m'] 已决——首过站承担上界放宽；全挡 ⟹ 并入站 S m' 判定 *)
Lemma lgwe_scan_S : forall (kappa TV0 budget : Real) (m' : nat),
  (forall j : nat, lgwe_station_dec kappa TV0 budget j) ->
  Or
    (sigT (fun k : nat => And (NatLe k m') (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j m' -> lgw_test kappa TV0 budget j -> Empty_set) ->
  Or
    (sigT (fun k : nat => And (NatLe k (Datatypes.S m')) (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j (Datatypes.S m') -> lgw_test kappa TV0 budget j -> Empty_set).
Proof.
  intros kappa TV0 budget m' Hdec Hscan.
  destruct Hscan as [[k [Hk Hspec]] | Hall].
  - apply inl. exists k. split.
    + assert (Hd : (k <= m')%nat) by (apply NatLe_drop; exact Hk).
      apply (NatLe_lift _ _ (Nat.le_le_succ_r _ _ Hd)).
    + exact Hspec.
  - destruct (Hdec (Datatypes.S m')) as [Hpass | Href].
    + apply inl. exists (Datatypes.S m'). split.
      * apply (NatLe_lift _ _ (Nat.le_refl (Datatypes.S m'))).
      * split.
        -- exact Hpass.
        -- intros j Hj Htj.
           apply (Hall j).
           ++ assert (Hd : (Datatypes.S j <= Datatypes.S m')%nat)
                by (apply NatLe_drop; exact Hj).
              apply (NatLe_lift _ _ (proj2 (Nat.succ_le_mono j m') Hd)).
           ++ exact Htj.
    + apply inr. intros j Hj Htj.
      destruct (Nat.leb j m') eqn:Elb.
      * (* j ≤ m'：前段否证结论承担 *)
        apply (Hall j).
        -- apply NatLe_lift. exact (proj1 (Nat.leb_le j m') Elb).
        -- exact Htj.
      * (* m' < j ∧ j ≤ S m' ⟹ j = S m'：本站否证 *)
        apply (proj1 (Nat.leb_gt j m')) in Elb.
        assert (Hd : (j <= Datatypes.S m')%nat) by (apply NatLe_drop; exact Hj).
        assert (Heq : j = Datatypes.S m')
          by exact (Nat.le_antisymm j (Datatypes.S m') Hd Elb).
        rewrite Heq in Htj. apply Href. exact Htj.
Qed.

Fixpoint lgwe_scan (kappa TV0 budget : Real)
  (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j) (m : nat)
  : Or
      (sigT (fun k : nat => And (NatLe k m) (lgw_min_sel_spec kappa TV0 budget k)))
      (forall j : nat, NatLe j m -> lgw_test kappa TV0 budget j -> Empty_set) :=
  match m with
  | O => lgwe_scan_O kappa TV0 budget Hdec
  | Datatypes.S m' =>
      lgwe_scan_S kappa TV0 budget m' Hdec (lgwe_scan kappa TV0 budget Hdec m')
  end.

(* ============================================================ *)
(* §6 正向构造主定理（条件化选择器接口 + rLPO 使用合成）                    *)
(* ============================================================ *)

(* 条件化选择器接口：四正性前提（mix_k_select 同形）+ 逐站非负 Or 族        *)
Definition lgwe_MinSelC : Set :=
  forall kappa TV0 budget : Real,
    real_lt real_zero kappa -> real_lt kappa real_one ->
    real_le real_zero TV0 -> real_lt real_zero budget ->
    (forall j : nat, real_le real_zero (lgwe_diff kappa TV0 budget j)) ->
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

Theorem lgwe_min_sel_of_rlpo : rLPO -> lgwe_MinSelC.
Proof.
  intros Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb Hnn.
  (* ② 必过站上界：mix_k_select（tv_rpow 形）经转换桥转回 lgw_test 形 *)
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Ha Hb) as [kp Hmix].
  assert (Hpass : lgw_test kappa TV0 budget kp).
  { unfold lgw_test.
    apply (real_eq_lt_lt (real_mult (lgw_rpow kappa kp) TV0)
                         (real_mult (tv_rpow kappa kp) TV0) budget).
    - apply (RealSetoid.real_eq_mult_compat (lgw_rpow kappa kp) TV0
                (tv_rpow kappa kp) TV0).
      + exact (lgwe_rpow_eq_tv kappa kp).
      + apply real_eq_refl.
    - exact Hmix. }
  (* ① 逐站可判定测试（rLPO 实质使用点在 lgwe_station_decide 内） *)
  assert (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j).
  { intros j. apply lgwe_station_decide.
    - exact Hrlpo.
    - exact (Hnn j). }
  (* ③ 线性扫 [0,k_pass] + 两态合成 *)
  destruct (lgwe_scan kappa TV0 budget Hdec kp) as [[k [Hk Hspec]] | Hall].
  - exists k. exact Hspec.
  - assert (Hkk : NatLe kp kp) by (apply (NatLe_lift _ _ (Nat.le_refl kp))).
    destruct (Hall kp Hkk Hpass).
Qed.

(* ============================================================ *)
(* §7 等价合成（正向肢 = lgw_lpo_of_min_sel；反向肢 = lgwe_min_sel_of_rlpo； *)
(*     Prop 合取 Qed 收尾，非提取面，体例同 UpReqLpoEquiv 的 lpn_equivalence） *)
(* ============================================================ *)

Theorem lgwe_equivalence :
  And (lgw_MinSel -> lgw_lpo_family) (rLPO -> lgwe_MinSelC).
Proof.
  split.
  - exact lgw_lpo_of_min_sel.
  - exact lgwe_min_sel_of_rlpo.
Qed.

(* ============================================================ *)
(* §8 假设审计与提取出口                                                   *)
(* ============================================================ *)

Print Assumptions lgwe_minsel_refutable.
Print Assumptions lgwe_station_decide.
Print Assumptions lgwe_min_sel_of_rlpo.
Print Assumptions lgwe_rpow_eq_tv.
Print Assumptions lgwe_equivalence.

Separate Extraction lgwe_diff lgwe_station_dec lgwe_MinSelC.
