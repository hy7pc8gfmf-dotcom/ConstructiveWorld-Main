(* 五字段指针｜模块：piu1901_leibsep_q_kernel_closed。使命：Leibniz pi_L 分离
   内核（leibsep_q_kernel）证书常元的语句面闭合——tdm225 五实例主证书形
   （sigT c, 0<c 且 QeqT c 〈闭式链〉 且 real_const c < |pi_L - q|）的 pi_L
   对应件。钉定项为内核定义链的 eps2 链（b0:=1/den q, n_sel, BF, BFd, K,
   eps1:=Qmin eg (Qmin el (Qmin (1/3) ((1/2)/K))), WING, eps2:=Qmin eps1
   (WING/(2K))）经门精度参量 (1/8) 与终项倍率 2 的复合；分离距离面经由
   leibsep_q_kernel_guarded 的窗级与 leibsep_metric_pi_transport 传输在三角
   收拢下合成。域守卫 QltT 0 q 承袭 eps2 链 WING 正性前提面（lw0_Wb_pos
   前提形；q=0 处 WING=0 使 eps2 链值为零，q<=0 处 WING 正性超出
   lw0_Wb_pos 前提形——q<=0 领地面由零前提内核 leibsep_q_kernel 本身
   承载，不在本件重复）。
  依赖：S01_BaseRing（And 积型/Id/NatLe/NatLe_lift/NatLe_drop）、
   S02_CauchyComplete（real_lt/real_eq/QltT_to_Qlt/Qlt_to_QltT）、
   S03_QExp（real_metric/real_const）、DTPT（q_fact）、LW0PiIrrational
   （lw0_Wb/lw0_n_select/lw0_pi_d0_of/lw0_QltT_le）、LW0MLicBridge
   （lw0m_e/lw0m_xL/lw0m_vanish_pi）、LW0LeibSeparation（内核/门/传输/
   caps/岸件/矛盾机与 S973 记名）。
  对标行：LW0LeibSeparation.v :5452（leibsep_q_kernel 内核源，:5484-5635
   闭式链逐行）；LW0LeibSeparation.v :298（leibsep_pi_sep_alpha_guarded
   传输面）；tdm225 母版 u5c_sqrt2_closed_measure（QeqT 钉定语句形）；
   LW1PiMeasure lw1m_b_cert_face（下游证书前提装填位）。
  构造性注记：零公理零承认（件尾 Print Assumptions 应 Closed）；语句面全
   Set 层（sigT/And/QeqT/QltT/real_lt 均 Set 值）；证内 Qlt 仅作推导辅助，
   出口位一律 Qlt_to_QltT 回 Set；辅助件 piu1901_dist_assemble 的线性
   不等式段以 lra 承担（辅助步，例外册在册用法，于此申报）。诚实边界：
   域守卫 QltT 0 q 居前提位（诚实接口披露）；钉定项经
   projT1 real_pi_geom_lt_ten_thirds 与 projT1 real_pi_leibniz_lt_ten_thirds
   引用包络见证（S10_KVQuantTrig 内 Lemma，Qed 不透明，钉定为项级自反而非可计算闭式；包络见证的显式化属独立分析件）。
  编译配方：coqc -native-compiler no -q -Q <本件目录> "" -Q
   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.
Require Import UpReqAltSumPos.
Require Import LW2TrigBridge.
Require Import DTPT.
Require Import LW0MLicBridge.
Require Import LW0PiIrrational.
Require Import Local.LW0LeibSeparation.

(* eps2 链的具名定义面（全部 Defined 透明；逐字对应内核 :5465-5469/:5596/:5609
   的 set 链，delta 展开即内核项）。 *)
Definition piu1901_b0 (q : Q) : Q := (Z.pos (Qden q) # 1)%Q.

Definition piu1901_nsel (q : Q) : nat :=
  (lw0_n_select (10 * lw0_pi_d0_of (piu1901_b0 q)) 0 + 1)%nat.

Definition piu1901_BF (q : Q) : Q :=
  Qabs (qpoly_eval (lw0_F (lw0_niven_f q (piu1901_b0 q) (piu1901_nsel q))
                          (piu1901_nsel q)) q).

Definition piu1901_BFd (q : Q) : Q :=
  Qabs (qpoly_eval (qpoly_deriv
          (lw0_F (lw0_niven_f q (piu1901_b0 q) (piu1901_nsel q))
                 (piu1901_nsel q))) q).

Definition piu1901_K (q : Q) : Q :=
  (piu1901_BF q * ((11 # 3)%Q * S973 + (1 # 4))
   + piu1901_BFd q * (S973 + (1 # 4)) + (1 # 8))%Q.

Definition piu1901_eps1 (q eg el : Q) : Q :=
  Qmin eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / piu1901_K q))).

Definition piu1901_WING (q : Q) : Q :=
  (q_fact (piu1901_nsel q)
     * (lw0_Wb (piu1901_b0 q) q (piu1901_nsel q) 0 * (2 # 27))%Q)%Q.

Definition piu1901_eps2 (q eg el : Q) : Q :=
  Qmin (piu1901_eps1 q eg el) (piu1901_WING q / (2 * piu1901_K q)%Q).

(* 分离距离面的装配机：门真守卫（e N + 2c0 严格小于点距）给定后，
   窗级（leibsep_q_kernel_guarded：一切 m >= M 有 2c0 < |xL m - q|）与
   传输（leibsep_metric_pi_transport：|pi_L 度量投影 - |xL m - q|| < c0/2
   于尾段）在三角收拢下给出 real_lt (real_const c0) (|pi_L - q|)。
   见证 c0/2 位取自传输 eps（内核 :294-296 传输设计面）。 *)
Lemma piu1901_dist_assemble :
  forall (q c0 : Q) (N : nat),
    QltT 0 c0 ->
    (1 <= N)%nat ->
    QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)) ->
    And (real_lt (real_const c0)
           (real_metric real_pi_geom (real_const q)))
        (sigT (fun M : nat => forall m : nat, NatLe M m ->
           QltT (2 * c0)%Q (Qabs ((lw0m_xL m - q)%Q)))).
Proof.
  intros q c0 N Hc0 HN1 Hguard.
  destruct (leibsep_q_kernel_guarded q N c0 HN1 Hguard) as [M HM].
  assert (Hc0h : Qlt 0 ((1 # 2) * c0)%Q).
  { apply (leibsep_qlt_of_half c0). apply QltT_to_Qlt. exact Hc0. }
  assert (Hc0hT : QltT 0 ((1 # 2) * c0)%Q) by (apply Qlt_to_QltT; exact Hc0h).
  destruct (leibsep_metric_pi_transport q ((1 # 2) * c0)%Q Hc0hT) as [Nr HNr].
  split.
  - exists ((1 # 2) * c0)%Q. split.
    + exact Hc0hT.
    + exists (Nat.max M Nr). intros n Hn.
      assert (HMaxM : NatLe M n).
      { apply NatLe_lift.
        pose proof (NatLe_drop (Nat.max M Nr) n Hn) as Hmax.
        apply (Nat.le_trans M (Nat.max M Nr) n (Nat.le_max_l M Nr) Hmax). }
      assert (HMaxN : NatLe Nr n).
      { apply NatLe_lift.
        pose proof (NatLe_drop (Nat.max M Nr) n Hn) as Hmax.
        apply (Nat.le_trans Nr (Nat.max M Nr) n (Nat.le_max_r M Nr) Hmax). }
      pose proof (QltT_to_Qlt _ _ (HM n HMaxM)) as Hk.
      pose proof (QltT_to_Qlt _ _ (HNr n HMaxN)) as Ht.
      pose proof (leibsep_qabs_low _ _ Ht) as Htlo.
      (* 纯 c0 形收拢：窗级 2c0 < |xL n - q| 与传输 |xL n - q| 近真合成
         |pi_L 投影 n - c0| > c0 + c0/2（三角不等式差和拆分）。 *)
      assert (Hfin : Qlt ((1 # 2) * c0)
                     (projT1 (real_metric real_pi_geom (real_const q)) n
                      - c0)%Q).
      { pose proof (leibsep_qlt_minus _ _ Hk) as HX.
        pose proof (leibsep_qlt_minus _ _ Htlo) as HY0.
        assert (EY : ((projT1 (real_metric real_pi_geom (real_const q)) n
                       - Qabs ((lw0m_xL n - q)%Q))
                      - - ((1 # 2) * c0))%Q
                     == ((projT1 (real_metric real_pi_geom (real_const q)) n
                          - Qabs ((lw0m_xL n - q)%Q)) + (1 # 2) * c0)%Q) by ring.
        assert (ESUM : (Qabs ((lw0m_xL n - q)%Q) - 2 * c0
                        + ((projT1 (real_metric real_pi_geom (real_const q)) n
                           - Qabs ((lw0m_xL n - q)%Q)) + (1 # 2) * c0))%Q
                       == ((projT1 (real_metric real_pi_geom (real_const q)) n
                            - c0) - (1 # 2) * c0)%Q) by ring.
        assert (HS : Qlt 0 ((projT1 (real_metric real_pi_geom (real_const q)) n
                             - c0) - (1 # 2) * c0)%Q).
        { apply (leibsep_qlt_wd2 0
                   (Qabs ((lw0m_xL n - q)%Q) - 2 * c0
                    + ((projT1 (real_metric real_pi_geom (real_const q)) n
                        - Qabs ((lw0m_xL n - q)%Q)) + (1 # 2) * c0))%Q
                   0
                   ((projT1 (real_metric real_pi_geom (real_const q)) n
                     - c0) - (1 # 2) * c0)%Q
                   (Qeq_refl 0) ESUM).
          apply (leibsep_qlt_sum (Qabs ((lw0m_xL n - q)%Q) - 2 * c0)%Q
                   ((projT1 (real_metric real_pi_geom (real_const q)) n
                     - Qabs ((lw0m_xL n - q)%Q)) + (1 # 2) * c0)%Q).
          - exact HX.
          - exact (leibsep_qlt_wd2 0
                     ((projT1 (real_metric real_pi_geom (real_const q)) n
                       - Qabs ((lw0m_xL n - q)%Q))
                      - - ((1 # 2) * c0))%Q
                     0
                     ((projT1 (real_metric real_pi_geom (real_const q)) n
                       - Qabs ((lw0m_xL n - q)%Q)) + (1 # 2) * c0)%Q
                     (Qeq_refl 0) EY HY0). }
        exact (proj2 (Qlt_minus_iff ((1 # 2) * c0)
                        ((projT1 (real_metric real_pi_geom (real_const q)) n
                          - c0)%Q)) HS). }
      apply Qlt_to_QltT. exact Hfin.
  - exists M. exact HM.
Qed.

(* 内核证书常元的闭合核：门三分两真支在 eps2 统一精度位下装配，
   双假支由 caps 链与矛盾机（leibsep_false_branch_contra）消去。
   域守卫 QltT 0 q 供 eps2 链 WING 正性前提（lw0_Wb_pos 前提形）。 *)
Lemma piu1901_kernel_closed_core :
  forall q : Q,
    QltT 0 q ->
    sigT (fun c0 : Q =>
      And (QltT 0 c0)
        (And (QeqT c0 (piu1901_eps2 q (projT1 real_pi_geom_lt_ten_thirds)
                                       (projT1 real_pi_leibniz_lt_ten_thirds)
                        * (1 # 8))%Q)
          (And (real_lt (real_const c0)
                  (real_metric real_pi_geom (real_const q)))
               (sigT (fun N : nat => forall m : nat, NatLe N m ->
                  QltT (2 * c0)%Q (Qabs ((lw0m_xL m - q)%Q))))))).
Proof.
  intros q Hqpos.
  destruct real_pi_geom_lt_ten_thirds as [eg [Hegp [N0g HN0g]]].
  destruct real_pi_leibniz_lt_ten_thirds as [el [Help [N0l HN0l]]].
  destruct real_pi_leibniz_gt_three as [e3 [He3p [N3 HN3]]].
  pose proof (QltT_to_Qlt 0 eg Hegp) as Hegp'.
  pose proof (QltT_to_Qlt 0 el Help) as Help'.
  pose proof (QltT_to_Qlt 0 e3 He3p) as He3p'.
  pose proof (QltT_to_Qlt _ _ Hqpos) as Hqpos'.
  set (b0 := (Z.pos (Qden q) # 1)%Q).
  set (n_sel := (lw0_n_select (10 * lw0_pi_d0_of b0) 0 + 1)%nat).
  set (BF := Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q)).
  set (BFd := Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q)).
  set (K := (BF * ((11 # 3)%Q * S973 + (1 # 4)) + BFd * (S973 + (1 # 4)) + (1 # 8))%Q).
  assert (Hb0 : QltT 0 b0).
  { apply Qlt_to_QltT. unfold b0, Qlt. cbn. reflexivity. }
  assert (HBF0 : Qle 0 BF) by (apply Qabs_nonneg).
  assert (HBFd0 : Qle 0 BFd) by (apply Qabs_nonneg).
  assert (Hns2 : (2 <= n_sel)%nat) by (unfold n_sel, lw0_n_select; lia).
  assert (HK1 : Qle (1 # 8) K).
  { unfold K. assert (Hc1 : Qle 0 ((11 # 3)%Q * S973 + (1 # 4))%Q).
    { assert (Hp : Qlt 0 ((11 # 3)%Q * S973 + (1 # 4))%Q)
        by (unfold S973; vm_compute; reflexivity).
      apply Qlt_le_weak. exact Hp. }
    assert (Hc2 : Qle 0 (S973 + (1 # 4))%Q).
    { assert (Hp : Qlt 0 (S973 + (1 # 4))%Q) by (unfold S973; vm_compute; reflexivity).
      apply Qlt_le_weak. exact Hp. }
    unfold S973.
    assert (Hp1 : Qle 0 (BF * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q).
    { apply Qmult_le_0_compat; assumption. }
    assert (Hp2 : Qle 0 (BFd * (S973 + (1 # 4))%Q)%Q).
    { apply Qmult_le_0_compat; [exact HBFd0 | exact Hc2]. }
    apply (Qle_trans (1 # 8)
             ((1 # 8)%Q + (BF * ((11 # 3)%Q * S973 + (1 # 4))
                           + BFd * (S973 + (1 # 4)))%Q)%Q K).
    - apply QleT'_to_Qle.
      apply (qleT'_plus_nonneg_rT (1 # 8)%Q
               (BF * ((11 # 3)%Q * S973 + (1 # 4)) + BFd * (S973 + (1 # 4)))%Q).
      apply Qle_to_QleT'.
      apply (Qplus_le_compat 0%Q (BF * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q 0%Q
               (BFd * (S973 + (1 # 4))%Q)%Q).
      + exact Hp1.
      + exact Hp2.
    - unfold K. apply QleT'_to_Qle. apply qeq_leT'. ring. }
  assert (HKpos : Qlt 0 K).
  { apply (Qlt_le_trans 0 (1 # 8) K).
    - vm_compute. reflexivity.
    - exact HK1. }
  assert (HK0 : Qle 0 K) by (apply Qlt_le_weak; exact HKpos).
  assert (Hinv : Qle 0 ((1 # 2)%Q / K)).
  { apply Qlt_le_weak. apply (Qmult_lt_0_compat (1 # 2) (/ K)).
    - vm_compute. reflexivity.
    - apply Qinv_lt_0_compat. exact HKpos. }
  pose (eps1 := Qmin eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
  assert (Hep1lt : Qlt 0 eps1).
  { apply (Q.min_glb_lt _ _ 0); [exact Hegp' |].
    apply (Q.min_glb_lt _ _ 0); [exact Help' |].
    apply (Q.min_glb_lt _ _ 0).
    - vm_compute. reflexivity.
    - apply (Qmult_lt_0_compat (1 # 2) (/ K)).
      + vm_compute. reflexivity.
      + apply Qinv_lt_0_compat. exact HKpos. }
  assert (Hep1eg : Qle eps1 eg).
  { apply (Q.min_glb_l eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
    apply Qle_refl. }
  assert (Hep1el : Qle eps1 el).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Q.min_glb_l el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                    (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
      apply Qle_refl. }
  assert (Hep1e3 : Qle eps1 (1 # 3)%Q).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Qle_trans _ (Qmin (1 # 3)%Q ((1 # 2)%Q / K)) _).
      + apply (Q.min_glb_r el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                      (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
        apply Qle_refl.
      + apply (Q.min_glb_l (1 # 3)%Q ((1 # 2)%Q / K)
                    (Qmin (1 # 3)%Q ((1 # 2)%Q / K))).
        apply Qle_refl. }
  assert (Hep1inv : Qle eps1 ((1 # 2)%Q / K)).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Qle_trans _ (Qmin (1 # 3)%Q ((1 # 2)%Q / K)) _).
      + apply (Q.min_glb_r el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                      (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
        apply Qle_refl.
      + apply (Q.min_glb_r (1 # 3)%Q ((1 # 2)%Q / K)
                    (Qmin (1 # 3)%Q ((1 # 2)%Q / K))).
        apply Qle_refl. }
  set (WING := (q_fact n_sel * (lw0_Wb b0 q n_sel 0 * (2 # 27))%Q)%Q).
  assert (HWb0 : QltT 0 (lw0_Wb b0 q n_sel 0)) by (apply lw0_Wb_pos; assumption).
  pose proof (QltT_to_Qlt _ _ HWb0) as HWb0'.
  assert (HX : Qlt 0 WING).
  { unfold WING. apply Qmult_lt_0_compat.
    - apply q_fact_pos.
    - apply Qmult_lt_0_compat.
      + exact HWb0'.
      + vm_compute. reflexivity. }
  assert (Hinv2 : Qlt 0 (WING / (2 * K)%Q)).
  { apply (Qmult_lt_0_compat WING (/ (2 * K)%Q)).
    - exact HX.
    - apply Qinv_lt_0_compat. apply (Qlt_le_trans 0 (1 # 8) (2 * K)).
      + vm_compute. reflexivity.
      + lra. }
  pose (eps2 := Qmin eps1 (WING / (2 * K)%Q)).
  assert (Hep2lt : Qlt 0 eps2).
  { apply (Q.min_glb_lt _ _ 0); [exact Hep1lt | exact Hinv2]. }
  assert (Hep2le1 : Qle eps2 eps1).
  { apply (Q.min_glb_l eps1 (WING / (2 * K)%Q) eps2). apply Qle_refl. }
  assert (Hep2leW : Qle eps2 (WING / (2 * K)%Q)).
  { apply (Q.min_glb_r eps1 (WING / (2 * K)%Q) eps2). apply Qle_refl. }
  assert (Hep2e3 : QleT' eps2 (1 # 3)%Q).
  { apply Qle_to_QleT'. apply (Qle_trans eps2 eps1 (1 # 3)); [exact Hep2le1 | exact Hep1e3]. }
  assert (HEp2 : QltT 0 eps2) by (apply Qlt_to_QltT; exact Hep2lt).
  assert (Heps2id : piu1901_eps2 q eg el == eps2) by reflexivity.
  assert (Hep2q8 : Qlt 0 (eps2 * (1 # 8))%Q).
  { apply (Qmult_lt_0_compat eps2 (1 # 8));
      [exact Hep2lt | vm_compute; reflexivity]. }
  assert (Hc0T : QltT 0 (eps2 * (1 # 8))%Q) by (apply Qlt_to_QltT; exact Hep2q8).
  assert (HN0g2 : forall n : nat, NatLe N0g n ->
             QltT eps2 (projT1 (real_const (10 / 3)) n - projT1 real_pi_geom n)).
  { intros n Hn. apply Qlt_to_QltT. apply (Qle_lt_trans eps2 eg _).
    - apply (Qle_trans eps2 eps1 eg Hep2le1 Hep1eg).
    - apply QltT_to_Qlt. exact (HN0g n Hn). }
  assert (Hep1q4 : QltT 0 (eps1 * (1 # 4))%Q) by (apply Qlt_to_QltT; lra).
  destruct (lw0m_vanish_pi (eps1 * (1 # 4))%Q Hep1q4) as [Nv1 HNv1].
  set (N1 := Nat.max 1 (Nat.max Nv1 (Nat.max N3 N0l))).
  assert (HN1b : (Nat.max N3 N0l <= N1)%nat)
    by (apply (Nat.le_trans (Nat.max N3 N0l) (Nat.max Nv1 (Nat.max N3 N0l)) N1);
        [apply Nat.le_max_r | apply Nat.le_max_r]).
  assert (HNN3 : (N3 <= N1)%nat)
    by (apply (Nat.le_trans N3 (Nat.max N3 N0l) N1); [apply Nat.le_max_l | exact HN1b]).
  assert (HNN0l : (N0l <= N1)%nat)
    by (apply (Nat.le_trans N0l (Nat.max N3 N0l) N1); [apply Nat.le_max_r | exact HN1b]).
  assert (HNv1N : QltT (lw0m_e N1) (eps1 * (1 # 4))%Q).
  { apply (HNv1 N1). apply (Nat.max_lub_l Nv1 (Nat.max N3 N0l)). apply Nat.le_max_r. }
  pose proof (QltT_to_Qlt _ _ HNv1N) as HNv1N'.
  assert (HN1 : (1 <= N1)%nat) by apply Nat.le_max_l.
  destruct (leibsep_gate_open q N1 (eps1 * (1 # 8))%Q) eqn:E1.
  - (* 门一真支：eps2 收缩精度位守卫后直接装配 *)
    assert (Hface1 : QltT (lw0m_e N1 + 2 * (eps1 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL N1 - q)%Q)))
      by (apply leibsep_gate_open_true; exact E1).
    assert (Hguard2 : QltT (lw0m_e N1 + 2 * (eps2 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL N1 - q)%Q))).
    { apply Qlt_to_QltT.
      pose proof (QltT_to_Qlt _ _ Hface1) as Hf1.
      lra. }
    destruct (piu1901_dist_assemble q (eps2 * (1 # 8))%Q N1 Hc0T HN1 Hguard2)
      as [Hdist Hwin].
    exists (eps2 * (1 # 8))%Q.
    split; [exact Hc0T |].
    split.
    + apply qeq_imp_qeqT. rewrite Heps2id. reflexivity.
    + split; [exact Hdist | exact Hwin].
  - (* 门一假支：岸定位链与 eps2 收缩，门二再分 *)
    assert (Hwin : QleT' (Qabs ((lw0m_xL N1 - q)%Q))
                         (lw0m_e N1 + 2 * (eps1 * (1 # 8))%Q))
      by (apply leibsep_gate_open_false; exact E1).
    pose proof (QleT'_to_Qle _ _ Hwin) as Hwin'.
    assert (Hx3 : QltT e3 ((lw0m_xL N1 - 3)%Q)).
    { pose proof (HN3 N1 (NatLe_lift _ _ HNN3)) as H0. exact H0. }
    pose proof (QltT_to_Qlt _ _ Hx3) as Hx3'.
    assert (HxL : QltT el ((10 # 3)%Q - lw0m_xL N1)%Q).
    { pose proof (HN0l N1 (NatLe_lift _ _ HNN0l)) as H0. exact H0. }
    pose proof (QltT_to_Qlt _ _ HxL) as HxL'.
    pose proof (leibsep_qabs_le_two (lw0m_xL N1 - q)
                  (lw0m_e N1 + 2 * (eps1 * (1 # 8)))%Q Hwin') as Htwo.
    destruct Htwo as [Hshore1T Hshore2T].
    pose proof (QleT'_to_Qle _ _ Hshore1T) as Hshore1.
    pose proof (QleT'_to_Qle _ _ Hshore2T) as Hshore2.
    assert (Hq0 : Qlt 0 q) by lra.
    assert (HQ103 : Qle q (10 # 3)%Q) by lra.
    assert (HQ103T : QleT' q (10 # 3)%Q) by (apply Qle_to_QleT'; exact HQ103).
    pose proof (leibsep_Wb01_diff_lower b0 q n_sel (lw0_QltT_le b0 Hb0) Hqpos
                  HQ103T Hns2) as HWbd.
    assert (Hep2q4 : QltT 0 (eps2 * (1 # 4))%Q) by (apply Qlt_to_QltT; lra).
    destruct (lw0m_vanish_pi (eps2 * (1 # 4))%Q Hep2q4) as [Nv2 HNv2].
    set (N2 := Nat.max Nv2 1).
    assert (HN21 : (1 <= N2)%nat) by apply Nat.le_max_r.
    destruct (leibsep_gate_open q N2 (eps2 * (1 # 8))%Q) eqn:E2.
    + (* 门二真支：同装配于收缩精度位 *)
      assert (Hguard2 : QltT (lw0m_e N2 + 2 * (eps2 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL N2 - q)%Q)))
        by (apply leibsep_gate_open_true; exact E2).
      destruct (piu1901_dist_assemble q (eps2 * (1 # 8))%Q N2 Hc0T HN21 Hguard2)
        as [Hdist Hwin2].
      exists (eps2 * (1 # 8))%Q.
      split; [exact Hc0T |].
      split.
      * apply qeq_imp_qeqT. rewrite Heps2id. reflexivity.
      * split; [exact Hdist | exact Hwin2].
    + (* 门二假支：caps 链上限合成后矛盾机消去 *)
      destruct (caps_scaled q eps2 N0g Nv2 HEp2 Hep2e3 HN0g2 HNv2 E2)
        as [s [t [M0 [Hs [Ht [Hs0 [Ht0 [Hscap Htcap]]]]]]]].
      assert (HCle : QleT'
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (eps2 * (BF * ((11 # 3)%Q * S973 + (1 # 4))
                         + BFd * (S973 + (1 # 4)) + (1 # 8)))%Q)
        by exact (lw1131_C_le_eps0K q eps2 s t BF BFd n_sel Hs0 Ht0
                    (qleT'_refl BF) (qleT'_refl BFd) Hscap Htcap).
      assert (Hcan : ((1 # 2)%Q / K) * K == (1 # 2)%Q)
        by (apply lw1190_div_mul_cancel; intro Hz; apply (Qlt_not_eq 0 K HKpos);
            apply Qeq_sym; exact Hz).
      assert (HK1' : QleT' (eps2 * K) (1 # 2)%Q).
      { apply Qle_to_QleT'.
        pose proof (lw95_mul_le_compat eps2 ((1 # 2)%Q / K) K K
                      (Qlt_le_weak 0 eps2 Hep2lt)
                      (Qle_trans eps2 eps1 ((1 # 2)%Q / K) Hep2le1 Hep1inv)
                      HK0 (Qle_refl K)) as Hmul.
        rewrite <- Hcan. exact Hmul. }
      assert (HtwoK : Qlt 0 (2 * K)%Q) by lra.
      assert (Hcan2 : (WING / (2 * K)%Q) * K == WING * (1 # 2)%Q)
        by (unfold Qdiv; field; intro Hz; apply (Qlt_not_eq 0 K HKpos);
            apply Qeq_sym; exact Hz).
      assert (HWle : Qle WING (q_fact n_sel * (lw0_Wb b0 q n_sel 0 - lw0_Wb b0 q n_sel 1))).
      { pose proof (QleT'_to_Qle _ _ HWbd) as HWbd'.
        unfold WING.
        rewrite (Qmult_comm (q_fact n_sel)).
        rewrite (Qmult_comm (q_fact n_sel)).
        apply (Qmult_le_compat_r (lw0_Wb b0 q n_sel 0 * (2 # 27))%Q _ (q_fact n_sel)).
        - exact HWbd'.
        - apply Qlt_le_weak. apply q_fact_pos. }
      assert (HP2 : QltT
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (q_fact n_sel * (lw0_Wb b0 q n_sel 0 - lw0_Wb b0 q n_sel 1))).
      { apply Qlt_to_QltT. apply (Qle_lt_trans _ (eps2 * K) _).
        - exact (QleT'_to_Qle _ _ HCle).
        - pose proof (lw95_mul_le_compat eps2 (WING / (2 * K)%Q) K K
                        (Qlt_le_weak 0 eps2 Hep2lt) Hep2leW HK0 (Qle_refl K)) as Hmul2.
          rewrite Hcan2 in Hmul2.
          assert (Hhalf : Qlt (WING * (1 # 2))%Q WING) by lra.
          apply (Qlt_le_trans _ WING _).
          + apply (Qle_lt_trans _ (WING * (1 # 2))%Q _).
            * exact Hmul2.
            * exact Hhalf.
          + exact HWle. }
      assert (HP1 : QleT'
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (1 # 2)%Q).
      { apply (qleT'_trans _ (eps2 * K)%Q).
        - exact HCle.
        - exact HK1'. }
      assert (Hq103c : QleT' q (10 / 3)%Q)
        by exact (leibsep_shore_q_le_ten_thirds q eps2 N0g Nv2 HEp2 HN0g2 HNv2 E2).
      assert (Hjq01 : (1 <= 1)%nat) by lia.
      assert (Hcontra : Id false true).
      { exact (leibsep_false_branch_contra q 0 1 s t M0 (eps2 * (1 # 8))%Q
                 Hqpos Hq103c Hc0T Hjq01 Hs Ht HP1 HP2). }
      discriminate Hcontra || inversion Hcontra.
Qed.

(* 主定理：tdm225 母版语句形的 pi_L 对应件——分离常元以 eps2 链经门槽精度
   (1/8) 钉定（QeqT 项级自反），距离面 real_const c < |pi_L - q| 无条件于
   域守卫之内。 *)
Theorem leibsep_q_kernel_closed :
  forall q : Q,
    QltT 0 q ->
    sigT (fun c : Q =>
      And (QltT 0 c)
        (And (QeqT c (piu1901_eps2 q (projT1 real_pi_geom_lt_ten_thirds)
                                       (projT1 real_pi_leibniz_lt_ten_thirds)
                        * (1 # 8))%Q)
             (real_lt (real_const c)
                (real_metric real_pi_geom (real_const q))))).
Proof.
  intros q Hqpos.
  destruct (piu1901_kernel_closed_core q Hqpos) as [c0 [Hc0 [Hpin [Hdist Hwin]]]].
  exists c0. split; [exact Hc0 |].
  split; [exact Hpin | exact Hdist].
Qed.

(* 伴随定理：内核终 exists 项 2*(eps2 链*(1/8)) 的窗级面——分离常元与
   一致窗级同时显式，供统一窗侧（n0(q) := max 〈N 项〉 (pie_modulus (c 项/10))
   合成）取件。 *)
Theorem leibsep_q_kernel_closed_window :
  forall q : Q,
    QltT 0 q ->
    sigT (fun c : Q =>
      And (QltT 0 c)
        (And (QeqT c (2 * (piu1901_eps2 q (projT1 real_pi_geom_lt_ten_thirds)
                                               (projT1 real_pi_leibniz_lt_ten_thirds)
                                * (1 # 8)))%Q)
             (sigT (fun N : nat => forall m : nat, NatLe N m ->
                QltT c (Qabs ((lw0m_xL m - q)%Q)))))).
Proof.
  intros q Hqpos.
  destruct (piu1901_kernel_closed_core q Hqpos) as [c0 [Hc0 [Hpin [Hdist Hwin]]]].
  exists (2 * c0)%Q.
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat 2 c0);
      [vm_compute; reflexivity | apply QltT_to_Qlt; exact Hc0].
  - split.
    + apply qeq_imp_qeqT.
      pose proof (qeqT_imp_qeq _ _ Hpin) as Heq.
      rewrite Heq. apply Qeq_refl.
    + exact Hwin.
Qed.

Print Assumptions piu1901_dist_assemble.
Print Assumptions piu1901_kernel_closed_core.
Print Assumptions leibsep_q_kernel_closed.
Print Assumptions leibsep_q_kernel_closed_window.
