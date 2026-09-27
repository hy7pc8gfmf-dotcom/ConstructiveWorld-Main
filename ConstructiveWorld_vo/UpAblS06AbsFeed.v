(* ==========================================================================)
   UpAblS06AbsFeed.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：uabS4c_q_abs_ge_l、uabS4c_q_abs_ge_opp、uabS4c_abs_ge_l_b、uabS4c_abs_ge_opp_b、uabS4c_abs_le_b_two_sided、uabS4c_leb_req_left、uabS4c_half、uabS4c_half_eq、uabS4c_half_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
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
Require Import UpAblAbsSumLeB.

(* ================= §1 uabS4c_q_abs_ge_l 族 ================= *)
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.

(* §0 库内接口核对（Check 逐项对照真实签名）                              *)

Check real_le_b.              (* Bishop 形 ≤（可达最强形谓词） *)
Check real_le_to_le_b.        (* Or ⟹ B 单向桥接 *)
Check real_abs.               (* 逐点 Qabs *)
Check real_abs_proj.          (* 逐点投影 *)
Check real_eps_witness.       (* 正性有理见证（内建半量） *)
Check q_abs_lt_two_sided.     (* Q 层双侧夹逼（同核机理） *)
Check Qlt_le_dec.             (* Q 可判定符号/序（非经典） *)
Check real_plus_proj.
Check real_opp_proj.
Check real_mult_proj.
Check real_const_proj.
Check real_eq_of_zero_diff.   (* 逐点零差分 ⟹ real_eq *)
Check RealSetoid.real_eq_plus_compat.
Check real_plus_assoc.
Check real_plus_comm.
Check real_plus_zero.
Check real_plus_opp.
Check real_mult_comm.
Check real_mult_one.
Check RealSetoid.real_lt_le_iff_req.
Check real_le_plus_compat.
Check uabS4_le_add_r.               (* 供体（UpAblAbsSumLeB）正余量右吸收 *)
Check uabS4_abs_diff_triangle_le_eps. (* 供体 A.1 两点核差形逐 eps *)
Check uabS4_abs_diff_triangle_le_B.   (* 供体 A.2 两点核差形 B 形 *)
Check uabS4_abs_sum_le_B_pair.        (* 供体 A.3 两点实例 B 形 *)
Check uabS4_cons_glue.                (* 供体归纳步引理（uabS4_cons_glue） *)
Check uabS4_lt_double_margin_le_half_contr. (* 供体 C.1 倍率 2 不可共存 *)
Check real_list_sum.                  (* list 折叠（X 全称） *)

(* §1 实数层基础引理（点态 B 吸收/双侧夹逼/半分构造/兼容对）               *)

(* A.0 Q 层：u ≤ |u|（Qlt_le_dec 符号判定，Q 侧可判定非经典） *)
Lemma uabS4c_q_abs_ge_l : forall u : Q, Qle u (Qabs u).
Proof.
  intros u. destruct (Qlt_le_dec u 0) as [Hlt | Hge].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hlt).
    rewrite Habs.
    (* 负支：u < 0 时目标 u ≤ −u。num/den 显式分解后以右因子非负的       *)
    (* 乘法单调 Z.mul_le_mono_nonneg_r 化为 nu ≤ −nu，再由                *)
    (* Z.le_trans 取 nu ≤ 0 ≤ −nu 两段构造（右段由反序性                  *)
    (* Z.opp_le_mono 从 nu ≤ 0 转出）                                     *)
    destruct u as [nu du]. unfold Qle, Qopp. cbn [Qnum Qden].
    unfold Qlt in Hlt. cbn [Qnum Qden] in Hlt.
    rewrite Z.mul_1_r, Z.mul_0_l in Hlt.
    apply Z.mul_le_mono_nonneg_r.
    + apply Z.lt_le_incl. apply Pos2Z.is_pos.
    + apply (Z.le_trans nu 0 (- nu)).
      * apply Z.lt_le_incl. exact Hlt.
      * exact (proj1 (Z.opp_le_mono nu 0) (Z.lt_le_incl nu 0 Hlt)).
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; exact Hge).
    rewrite Habs. apply Qle_refl.
Qed.

(* A.1 Q 层：−u ≤ |u| *)
Lemma uabS4c_q_abs_ge_opp : forall u : Q, Qle (- u) (Qabs u).
Proof.
  intros u. destruct (Qlt_le_dec u 0) as [Hlt | Hge].
  - assert (Habs : Qabs u == - u) by (apply Qabs_neg; apply Qlt_le_weak; exact Hlt).
    rewrite Habs. apply Qle_refl.
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; exact Hge).
    rewrite Habs.
    (* 非负支：0 ≤ u 时目标 −u ≤ u。num/den 显式分解后以右因子非负的     *)
    (* 乘法单调 Z.mul_le_mono_nonneg_r 化为 −nu ≤ nu，再由                *)
    (* Z.le_trans 取 −nu ≤ 0 ≤ nu 两段构造（左段由反序性                  *)
    (* Z.opp_le_mono 从 0 ≤ nu 转出）                                     *)
    destruct u as [nu du]. unfold Qle, Qopp. cbn [Qnum Qden].
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    rewrite Z.mul_0_l, Z.mul_1_r in Hge.
    apply Z.mul_le_mono_nonneg_r.
    + apply Z.lt_le_incl. apply Pos2Z.is_pos.
    + apply (Z.le_trans (- nu) 0 nu).
      * exact (proj1 (Z.opp_le_mono 0 nu) Hge).
      * exact Hge.
Qed.

(* A.2 点态 B 吸收（正向）：x ≤_B |x|。逐点 Qabs(u_n) ≥ u_n ＋正性见证内建半量 *)
Lemma uabS4c_abs_ge_l_b : forall x : Real, real_le_b x (real_abs x).
Proof.
  intros x eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  unfold real_lt. exists (eps0 / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite real_abs_proj.
    assert (Hq0 : Qlt (eps0 / 2) (projT1 eps n))
      by (apply QltT_to_Qlt; exact (HN0 n (NatLe_drop _ _ Hn))).
    assert (Hge : Qle (projT1 x n) (Qabs (projT1 x n))) by apply uabS4c_q_abs_ge_l.
    lra.
Qed.

(* A.3 点态 B 吸收（负向）：−x ≤_B |x|。逐点 Qabs(u_n) ≥ −u_n *)
Lemma uabS4c_abs_ge_opp_b : forall x : Real, real_le_b (real_opp x) (real_abs x).
Proof.
  intros x eps Heps.
  destruct (real_eps_witness eps Heps) as [eps0 [Heps0 [N0 HN0]]].
  unfold real_lt. exists (eps0 / 2)%Q. split.
  - apply Qlt_to_QltT. apply Qlt_shift_div_l.
    + reflexivity.
    + simpl. apply QltT_to_Qlt. exact Heps0.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_opp_proj. rewrite real_plus_proj. rewrite real_abs_proj.
    assert (Hq0 : Qlt (eps0 / 2) (projT1 eps n))
      by (apply QltT_to_Qlt; exact (HN0 n (NatLe_drop _ _ Hn))).
    assert (Hge : Qle (- projT1 x n) (Qabs (projT1 x n))) by apply uabS4c_q_abs_ge_opp.
    lra.
Qed.

(* A.4 核心引理：双侧夹逼 ⟹ abs B 形——
   x ≤_B Y 且 −x ≤_B Y ⟹ |x| ≤_B Y。
   构造：逐 eps 取 δ＝min(d1,d2)（Qlt_le_dec 二分），逐点 Qabs 二分符号：
   u_n ≥ 0 支取正向见证 d1，u_n < 0 支取负向见证 d2——双侧信息各承一肢，
   逐点符号二分在 Q 层可判定处完成（构造性保持，无整体符号判定）。 *)
Lemma uabS4c_abs_le_b_two_sided : forall x Y : Real,
  real_le_b x Y -> real_le_b (real_opp x) Y -> real_le_b (real_abs x) Y.
Proof.
  intros x Y H1 H2 eps Heps.
  specialize (H1 eps Heps). specialize (H2 eps Heps).
  unfold real_lt in H1, H2.
  destruct H1 as [d1 [Hd1 [N1 HN1]]]. destruct H2 as [d2 [Hd2 [N2 HN2]]].
  destruct (Qlt_le_dec d1 d2) as [Hd12 | Hd21].
  - exists d1. split. exact Hd1.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite real_plus_proj in Hp2. rewrite real_opp_proj in Hp2.
    rewrite real_plus_proj. rewrite real_abs_proj.
    destruct (Qlt_le_dec (projT1 x n) 0) as [Hx | Hx].
    + assert (Habs : Qabs (projT1 x n) == - projT1 x n)
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hx).
      rewrite Habs. lra.
    + assert (Habs : Qabs (projT1 x n) == projT1 x n) by (apply Qabs_pos; exact Hx).
      rewrite Habs. lra.
  - exists d2. split. exact Hd2.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite real_plus_proj in Hp2. rewrite real_opp_proj in Hp2.
    rewrite real_plus_proj. rewrite real_abs_proj.
    destruct (Qlt_le_dec (projT1 x n) 0) as [Hx | Hx].
    + assert (Habs : Qabs (projT1 x n) == - projT1 x n)
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hx).
      rewrite Habs. lra.
    + assert (Habs : Qabs (projT1 x n) == projT1 x n) by (apply Qabs_pos; exact Hx).
      rewrite Habs. lra.
Qed.

(* A.5 B 形右相等运输：a ≡ b 且 a ≤_B Y ⟹ b ≤_B Y *)
Lemma uabS4c_leb_req_left : forall a b Y : Real,
  real_eq a b -> real_le_b a Y -> real_le_b b Y.
Proof.
  intros a b Y Hab H eps Heps.
  specialize (H eps Heps). unfold real_lt in H.
  destruct H as [d1 [Hd1 [N1 HN1]]].
  assert (Hd1q : Qlt 0 d1) by (apply QltT_to_Qlt; exact Hd1).
  assert (Hhalf : QltT 0 (d1 * (1#2))) by (apply Qlt_to_QltT; lra).
  destruct (Hab (d1 * (1#2))%Q Hhalf) as [N2 HN2].
  exists (d1 * (1#2))%Q. split.
  - exact Hhalf.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !real_plus_proj.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    assert (Hq2 : Qlt (Qabs (projT1 a n - projT1 b n)) (d1 * (1#2)))
      by (apply QltT_to_Qlt; exact (HN2 n Hb)).
    destruct (Qlt_le_dec (projT1 a n - projT1 b n) 0) as [Hwb | Hwb].
    + assert (Habs : Qabs (projT1 a n - projT1 b n) == - (projT1 a n - projT1 b n))
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hwb).
      rewrite Habs in Hq2.
      assert (Hw2 : projT1 b n - projT1 a n == - (projT1 a n - projT1 b n)) by ring.
      rewrite <- Hw2 in Hq2.
      lra.
    + assert (Habs : Qabs (projT1 a n - projT1 b n) == projT1 a n - projT1 b n)
        by (apply Qabs_pos; exact Hwb).
      rewrite Habs in Hq2.
      lra.
Qed.

(* A.6 半分构造：half e ＋ half e ≡ e
   （real_const (1#2) 逐点环恒等式，零 inv2 需求）＋half 正性 *)
Definition uabS4c_half (e : Real) : Real := real_mult e (real_const (1#2)).

Lemma uabS4c_half_eq : forall e : Real,
  real_eq (real_plus (uabS4c_half e) (uabS4c_half e)) e.
Proof.
  intros e. apply real_eq_of_zero_diff. intro n.
  unfold uabS4c_half.
  rewrite real_plus_proj. rewrite real_mult_proj. rewrite real_const_proj.
  unfold Qminus. ring.
Qed.

Lemma uabS4c_half_pos : forall e : Real,
  real_lt real_zero e -> real_lt real_zero (uabS4c_half e).
Proof.
  intros e He.
  destruct (real_eps_witness e He) as [eps0 [Heps0 [N0 HN0]]].
  assert (Hq0 : Qlt 0 eps0) by (apply QltT_to_Qlt; exact Heps0).
  unfold real_lt. exists (eps0 * (1#4))%Q. split.
  - apply Qlt_to_QltT. lra.
  - exists N0. intros n Hn.
    apply Qlt_to_QltT.
    unfold uabS4c_half.
    rewrite real_mult_proj. rewrite real_const_proj.
    assert (Hz : projT1 real_zero n == 0) by (cbn [projT1]; reflexivity).
    rewrite Hz.
    pose proof (HN0 n (NatLe_drop _ _ Hn)) as Hp.
    apply QltT_to_Qlt in Hp.
    assert (Heq2 : eps0 * (1#2) == eps0 / 2) by reflexivity.
    rewrite <- Heq2 in Hp.
    lra.
Qed.

(* A.7 B 形 plus 兼容：a ≤_B c 且 b ≤_B d ⟹ a+b ≤_B c+d。
   半分构造应用处：两侧各取半量余量，Q 层 h_n+h_n ≡ eps_n 逐点重合。 *)
Lemma uabS4c_leb_plus_compat : forall a b c d : Real,
  real_le_b a c -> real_le_b b d -> real_le_b (real_plus a b) (real_plus c d).
Proof.
  intros a b c d H1 H2 eps Heps.
  assert (Hh : real_lt real_zero (uabS4c_half eps)) by (apply uabS4c_half_pos; exact Heps).
  specialize (H1 (uabS4c_half eps) Hh). specialize (H2 (uabS4c_half eps) Hh).
  unfold real_lt in H1, H2.
  destruct H1 as [d1 [Hd1 [N1 HN1]]]. destruct H2 as [d2 [Hd2 [N2 HN2]]].
  assert (Hd1q : Qlt 0 d1) by (apply QltT_to_Qlt; exact Hd1).
  assert (Hd2q : Qlt 0 d2) by (apply QltT_to_Qlt; exact Hd2).
  destruct (Qlt_le_dec d1 d2) as [Hd12 | Hd21].
  - exists d1. split. exact Hd1.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !real_plus_proj.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite real_plus_proj in Hp2.
    assert (Hhp : projT1 (uabS4c_half eps) n + projT1 (uabS4c_half eps) n == projT1 eps n).
    { unfold uabS4c_half. rewrite real_mult_proj. rewrite real_const_proj. ring. }
    rewrite <- Hhp.
    lra.
  - exists d2. split. exact Hd2.
    exists (Nat.max N1 N2). intros n Hn.
    assert (Ha : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Hb : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    rewrite !real_plus_proj.
    pose proof (HN1 n Ha) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Hb) as Hp2. apply QltT_to_Qlt in Hp2.
    rewrite real_plus_proj in Hp2.
    assert (Hhp : projT1 (uabS4c_half eps) n + projT1 (uabS4c_half eps) n == projT1 eps n).
    { unfold uabS4c_half. rewrite real_mult_proj. rewrite real_const_proj. ring. }
    rewrite <- Hhp.
    lra.
Qed.

(* A.8 B 形 opp 反序兼容（反单调）：a ≤_B b ⟹ −b ≤_B −a *)
Lemma uabS4c_leb_opp_anti : forall a b : Real,
  real_le_b a b -> real_le_b (real_opp b) (real_opp a).
Proof.
  intros a b H eps Heps.
  specialize (H eps Heps). unfold real_lt in H.
  destruct H as [d1 [Hd1 [N1 HN1]]].
  exists d1. split. exact Hd1.
  exists N1. intros n Hn.
  apply Qlt_to_QltT.
  rewrite real_plus_proj. rewrite !real_opp_proj.
  pose proof (HN1 n Hn) as Hp1. apply QltT_to_Qlt in Hp1.
  rewrite real_plus_proj in Hp1.
  lra.
Qed.

(* §2 SumOver 抽象接口主件（同 UpReqSampling 的诚实接口形，                 *)
(*   R:=Real 特化；三字段＝显式 Set 层前提；abs_sum_le 字段不设——本件证之）  *)

Section uabS4c_SumOverSlot.

Variable S : Set.
Variable sumf : (S -> Real) -> Real.

(* 前提字段一：外延（逐点 real_eq ⟹ 和 real_eq；对应库形 sum_ext） *)
Variable uabS4c_sum_ext : forall f g : S -> Real,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
(* 前提字段二：加法（逐点和 ≡ 和的和；对应库形 sum_add） *)
Variable uabS4c_sum_add : forall f g : S -> Real,
  real_eq (sumf (fun s : S => real_plus (f s) (g s))) (real_plus (sumf f) (sumf g)).
(* 前提字段三：单调 Bishop 升级形（逐点 real_le_b ⟹ 和 real_le_b；
   库形 Or 字段经 real_le_to_le_b 单步可得，本形严格更弱＝结论更强） *)
Variable uabS4c_sum_le_B : forall f g : S -> Real,
  (forall s : S, real_le_b (f s) (g s)) -> real_le_b (sumf f) (sumf g).

(* B.0 零函数代数：Σ 0 ≡ 0（ext＋add＋消去链自证，零新前提） *)
Lemma uabS4c_sum_zero_eq : real_eq (sumf (fun _ : S => real_zero)) real_zero.
Proof.
  assert (Hid : real_eq (sumf (fun _ : S => real_zero))
                        (real_plus (sumf (fun _ : S => real_zero))
                                   (sumf (fun _ : S => real_zero)))).
  { eapply real_eq_trans.
    - apply (uabS4c_sum_ext (fun _ : S => real_zero)
               (fun _ : S => real_plus real_zero real_zero)).
      intro s. apply real_eq_sym. apply real_plus_zero.
    - apply (uabS4c_sum_add (fun _ : S => real_zero) (fun _ : S => real_zero)). }
  assert (Hkey : real_eq (real_plus (sumf (fun _ : S => real_zero))
                                    (real_opp (sumf (fun _ : S => real_zero))))
                         (sumf (fun _ : S => real_zero))).
  { eapply real_eq_trans.
    - apply RealSetoid.real_eq_plus_compat.
      + exact Hid.
      + apply real_eq_refl.
    - eapply real_eq_trans.
      + apply real_eq_sym. apply real_plus_assoc.
      + eapply real_eq_trans.
        * apply RealSetoid.real_eq_plus_compat.
          -- apply real_eq_refl.
          -- apply real_plus_opp.
        * apply real_plus_zero. }
  eapply real_eq_trans.
  - apply real_eq_sym. exact Hkey.
  - apply real_plus_opp.
Qed.

(* B.1 负函数代数：Σ(−f) ≡ −(Σf)（ext＋add＋B.0 消去链自证，零新前提） *)
Lemma uabS4c_sum_opp_eq : forall f : S -> Real,
  real_eq (sumf (fun s : S => real_opp (f s))) (real_opp (sumf f)).
Proof.
  intros f.
  assert (Hadd : real_eq (sumf (fun s : S => real_plus (f s) (real_opp (f s))))
                         (real_plus (sumf f) (sumf (fun s : S => real_opp (f s)))))
    by apply (uabS4c_sum_add f (fun s : S => real_opp (f s))).
  assert (Hext : real_eq (sumf (fun s : S => real_plus (f s) (real_opp (f s))))
                         (sumf (fun _ : S => real_zero)))
    by (apply (uabS4c_sum_ext (fun s : S => real_plus (f s) (real_opp (f s)))
                (fun _ : S => real_zero)); intro s; apply real_plus_opp).
  assert (Hplus : real_eq (real_plus (sumf f) (sumf (fun s : S => real_opp (f s))))
                          real_zero).
  { eapply real_eq_trans.
    - apply real_eq_sym. exact Hadd.
    - eapply real_eq_trans.
      + exact Hext.
      + apply uabS4c_sum_zero_eq. }
  (* 链：so ≡ 0+so ≡ (sf+(−sf))+so ≡ sf+((−sf)+so) ≡ sf+(so+(−sf))
        ≡ (sf+so)+(−sf) ≡ 0+(−sf) ≡ (−sf)+0 ≡ −sf *)
  assert (Hs1 : real_eq (sumf (fun s : S => real_opp (f s)))
                        (real_plus real_zero (sumf (fun s : S => real_opp (f s))))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_zero.
    - apply real_eq_sym. apply real_plus_comm. }
  assert (Hs2 : real_eq (real_plus real_zero (sumf (fun s : S => real_opp (f s))))
                        (real_plus (real_plus (sumf f) (real_opp (sumf f)))
                                   (sumf (fun s : S => real_opp (f s))))).
  { apply RealSetoid.real_eq_plus_compat.
    - apply real_eq_sym. apply real_plus_opp.
    - apply real_eq_refl. }
  assert (Hs3 : real_eq (real_plus (real_plus (sumf f) (real_opp (sumf f)))
                                   (sumf (fun s : S => real_opp (f s))))
                        (real_plus (sumf f)
                                   (real_plus (real_opp (sumf f))
                                              (sumf (fun s : S => real_opp (f s))))))
    by (apply real_eq_sym; apply real_plus_assoc).
  assert (Hs4 : real_eq (real_plus (sumf f)
                                   (real_plus (real_opp (sumf f))
                                              (sumf (fun s : S => real_opp (f s)))))
                        (real_plus (sumf f)
                                   (real_plus (sumf (fun s : S => real_opp (f s)))
                                              (real_opp (sumf f)))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_plus_comm]).
  assert (Hs5 : real_eq (real_plus (sumf f)
                                   (real_plus (sumf (fun s : S => real_opp (f s)))
                                              (real_opp (sumf f))))
                        (real_plus (real_plus (sumf f)
                                   (sumf (fun s : S => real_opp (f s))))
                                   (real_opp (sumf f))))
    by apply real_plus_assoc.
  assert (Hs6 : real_eq (real_plus (real_plus (sumf f)
                                   (sumf (fun s : S => real_opp (f s))))
                                   (real_opp (sumf f)))
                        (real_plus real_zero (real_opp (sumf f))))
    by (apply RealSetoid.real_eq_plus_compat; [exact Hplus | apply real_eq_refl]).
  assert (Hs7 : real_eq (real_plus real_zero (real_opp (sumf f)))
                        (real_opp (sumf f))).
  { eapply real_eq_trans.
    - apply real_plus_comm.
    - apply real_plus_zero. }
  exact (real_eq_trans _ _ _ Hs1
           (real_eq_trans _ _ _ Hs2
              (real_eq_trans _ _ _ Hs3
                 (real_eq_trans _ _ _ Hs4
                    (real_eq_trans _ _ _ Hs5 (real_eq_trans _ _ _ Hs6 Hs7)))))).
Qed.

(* B.2 主定理（接口本位 B 形）：|Σ sumf f| ≤_B Σ sumf (fun s => |f s|)。
   构造：点态 B 吸收×2（A.2/A.3）应用单调字段得双向和界，负向经 B.1 运输
   （A.5），双侧夹逼核（A.4）收束——三前提各司其职，零归纳。 *)
Theorem uabS4c_abs_sum_le_B_slot : forall f : S -> Real,
  real_le_b (real_abs (sumf f)) (sumf (fun s : S => real_abs (f s))).
Proof.
  intros f.
  assert (H1 : real_le_b (sumf f) (sumf (fun s : S => real_abs (f s)))).
  { apply uabS4c_sum_le_B. intro s. apply uabS4c_abs_ge_l_b. }
  assert (H2 : real_le_b (sumf (fun s : S => real_opp (f s)))
                         (sumf (fun s : S => real_abs (f s)))).
  { apply uabS4c_sum_le_B. intro s. apply uabS4c_abs_ge_opp_b. }
  assert (H3 : real_le_b (real_opp (sumf f))
                         (sumf (fun s : S => real_abs (f s)))).
  { apply (uabS4c_leb_req_left (sumf (fun s : S => real_opp (f s)))
             (real_opp (sumf f))).
    - apply uabS4c_sum_opp_eq.
    - exact H2. }
  exact (uabS4c_abs_le_b_two_sided (sumf f)
           (sumf (fun s : S => real_abs (f s))) H1 H3).
Qed.

(* B.3 逐 eps 形推论（B ⟹ 逐 eps，inl 注入——供体 B.3 对照位） *)
Theorem uabS4c_abs_sum_le_eps_slot : forall (f : S -> Real) (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (sumf f))
          (real_plus (sumf (fun s : S => real_abs (f s))) e).
Proof.
  intros f e He.
  apply (RealSetoid.real_lt_le_iff_req). apply inl.
  exact (uabS4c_abs_sum_le_B_slot f e He).
Qed.

(* B.4 双倍余量矛盾引理：B 形界不可被双倍 margin 越过（构造性：不存在
   这样的见证）。应用供体 C.1（uabS4_lt_double_margin_le_half_contr）＋本件 B.3 逐 eps 形——接口级一致性证书。 *)
Theorem uabS4c_slot_double_kill : forall (f : S -> Real) (e : Real),
  real_lt real_zero e ->
  real_lt (real_plus (sumf (fun s : S => real_abs (f s))) (real_plus e e))
          (real_abs (sumf f)) ->
  Empty_set.
Proof.
  intros f e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr (real_abs (sumf f))
           (sumf (fun s : S => real_abs (f s))) e He Hfar).
  exact (uabS4c_abs_sum_le_eps_slot f e He).
Qed.

End uabS4c_SumOverSlot.

(* §3 接口可满足性实例（bool 两点和形）＋供体对照                            *)

(* C.0 bool 两点接口三字段（外延/加法/单调 Bishop 形） *)
Lemma uabS4c_pair_ext : forall (f g : bool -> Real),
  (forall s : bool, real_eq (f s) (g s)) ->
  real_eq (real_plus (f true) (f false)) (real_plus (g true) (g false)).
Proof.
  intros f g H. apply RealSetoid.real_eq_plus_compat.
  - exact (H true).
  - exact (H false).
Qed.

Lemma uabS4c_pair_add : forall f g : bool -> Real,
  real_eq (real_plus (real_plus (f true) (g true)) (real_plus (f false) (g false)))
          (real_plus (real_plus (f true) (f false)) (real_plus (g true) (g false))).
Proof.
  intros f g.
  assert (Ht1 : real_eq (real_plus (real_plus (f true) (g true)) (real_plus (f false) (g false)))
                        (real_plus (f true) (real_plus (g true) (real_plus (f false) (g false)))))
    by (apply real_eq_sym; apply real_plus_assoc).
  assert (Ht2 : real_eq (real_plus (f true) (real_plus (g true) (real_plus (f false) (g false))))
                        (real_plus (f true) (real_plus (real_plus (g true) (f false)) (g false))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_plus_assoc]).
  assert (Ht3 : real_eq (real_plus (f true) (real_plus (real_plus (g true) (f false)) (g false)))
                        (real_plus (f true) (real_plus (real_plus (f false) (g true)) (g false))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply RealSetoid.real_eq_plus_compat;
          [apply real_plus_comm | apply real_eq_refl]]).
  assert (Ht4 : real_eq (real_plus (f true) (real_plus (real_plus (f false) (g true)) (g false)))
                        (real_plus (f true) (real_plus (f false) (real_plus (g true) (g false)))))
    by (apply RealSetoid.real_eq_plus_compat;
        [apply real_eq_refl | apply real_eq_sym; apply real_plus_assoc]).
  assert (Ht5 : real_eq (real_plus (f true) (real_plus (f false) (real_plus (g true) (g false))))
                        (real_plus (real_plus (f true) (f false)) (real_plus (g true) (g false))))
    by apply real_plus_assoc.
  exact (real_eq_trans _ _ _ Ht1 (real_eq_trans _ _ _ Ht2 (real_eq_trans _ _ _ Ht3 (real_eq_trans _ _ _ Ht4 Ht5)))).
Qed.

Lemma uabS4c_pair_le_B : forall f g : bool -> Real,
  (forall s : bool, real_le_b (f s) (g s)) ->
  real_le_b (real_plus (f true) (f false)) (real_plus (g true) (g false)).
Proof.
  intros f g H. apply uabS4c_leb_plus_compat.
  - exact (H true).
  - exact (H false).
Qed.

Check uabS4c_abs_sum_le_B_slot.

(* C.1 两点和形经抽象接口重导：与供体 A.3（uabS4_abs_sum_le_B_pair）
   同语句——接口通路独立复核（零增量对照，两读并列）。
   附带语义点：A.7 的半分构造在本实例单调字段处被真实使用。 *)
Theorem uabS4c_slot_pair_B : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f.
  exact (uabS4c_abs_sum_le_B_slot bool
           (fun (h : bool -> Real) => real_plus (h true) (h false))
           uabS4c_pair_ext uabS4c_pair_add uabS4c_pair_le_B f).
Qed.

(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设；节变量 End 全称化收纳） *)

Print Assumptions uabS4c_abs_ge_l_b.
Print Assumptions uabS4c_abs_ge_opp_b.
Print Assumptions uabS4c_abs_le_b_two_sided.
Print Assumptions uabS4c_leb_req_left.
Print Assumptions uabS4c_half_eq.
Print Assumptions uabS4c_half_pos.
Print Assumptions uabS4c_leb_plus_compat.
Print Assumptions uabS4c_leb_opp_anti.
Print Assumptions uabS4c_abs_sum_le_B_slot.
Print Assumptions uabS4c_abs_sum_le_eps_slot.
Print Assumptions uabS4c_slot_double_kill.
Print Assumptions uabS4c_slot_pair_B.
(* ================= §2 s6f_q_const_pos 族 ================= *)
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.

(* §0 · 依赖签名核验（标识符漂移即编译期暴露） *)

Check real_le_b.              (* UpRealLeB 的 Bishop 形 ≤（语句面谓词） *)
Check real_eq.                (* 逐 eps 相等（集合层） *)
Check real_abs.               (* 逐点 Qabs（CW 世界） *)
Check real_abs_proj.          (* 逐点投影 *)
Check real_mult.              (* 逐点乘法 *)
Check real_mult_proj.         (* 逐点投影（乘法） *)
Check real_const.             (* 常值实数 *)
Check real_const_proj.        (* 逐点投影（常值） *)
Check real_eq_trans.          (* 等式传递 *)
Check real_eq_refl.           (* 等式自反 *)
Check real_eq_of_zero_diff.   (* 逐点零差分 ⟹ real_eq *)
Check RealSetoid.real_eq_mult_compat. (* 乘法相等兼容 *)
Check uabS4c_abs_sum_le_B_slot. (* 主供给定理（End 后全称化） *)
Check uabS4c_abs_sum_le_eps_slot. (* 逐 eps 形供给（覆盖其二所需语句） *)
Check Qabs_Qmult.             (* Q 层：Qabs (u·v) == Qabs u·Qabs v *)
Check Qabs_pos.               (* Q 层：0 ≤ u ⟹ Qabs u == u *)
Check Qabs_neg.               (* Q 层：0 ≤ −u ⟹ Qabs u == −u *)
Check Qlt_shift_div_l.        (* Q 层半分正性 *)
Check Qlt_to_QltT.
Check QltT_to_Qlt.
Check Qlt_le_dec.             (* Q 可判定符号（非经典） *)
Check Qle_Qabs.               (* Q 层：u ≤ Qabs u *)
Check Qlt_le_trans.
Check NatLe_lift.
Check NatLe_drop.

(* §A · 转换层（点态 abs 改写＋B 形右端相等运输）                       *)

(* A.0 有理正性到实层的桥：0 < e（有理）⟹ real_lt real_zero (real_const e)。
   见证：半量 d := e·½，N := 0，逐点经 real_const_proj 投影即得 e。
   实作注记：lra 对 Q 除法失效，故半量一律写 ·(1#2) 乘法形。 *)
Lemma s6f_q_const_pos : forall e : Q,
  QltT 0 e -> real_lt real_zero (real_const e).
Proof.
  intros e He.
  assert (Hhalfq : Qlt 0 (e * (1#2))).
  { apply QltT_to_Qlt in He. lra. }
  assert (Hhalf : QltT 0 (e * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  exists (e * (1#2))%Q. split.
  - exact Hhalf.
  - exists O. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_const_proj.
    assert (Hz : projT1 real_zero n == 0) by reflexivity.
    rewrite Hz.
    lra.
Qed.

(* A.1 非负实数的 abs 恒等：0 ≤_B q ⟹ |q| ≡ q。
   思路：real_le_b 的预算取半（·(1#2) 乘法形）后取尾部（最终 q_n > −eps/2），
   对尾部二分：q_n < 0 情形 −2·q_n < eps；q_n ≥ 0 情形 Qabs q_n == q_n 零差。 *)
Lemma s6f_abs_nonneg_eq : forall q : Real,
  real_le_b real_zero q -> real_eq (real_abs q) q.
Proof.
  intros q Hq.
  unfold real_eq. intros eps0 Heps0.
  (* 预算取半量（·(1#2) 乘法形）：尾部 q_n > d0 − eps0/2 > −eps0/2，
     二分后 q_n<0 情形 −2·q_n < eps0、q_n≥0 情形零差 *)
  assert (Hhalfq : Qlt 0 (eps0 * (1#2))).
  { apply QltT_to_Qlt in Heps0. lra. }
  assert (Hhalf : QltT 0 (eps0 * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  destruct (Hq (real_const (eps0 * (1#2))) (s6f_q_const_pos (eps0 * (1#2)) Hhalf))
    as [d0 [Hd0 [N0 HN0]]].
  exists N0. intros n Hn.
  apply Qlt_to_QltT.
  rewrite real_abs_proj.
  pose proof (HN0 n Hn) as Hp. apply QltT_to_Qlt in Hp.
  rewrite real_plus_proj in Hp.
  rewrite real_const_proj in Hp.
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz in Hp.
  assert (Hd0q : Qlt 0 d0) by (apply QltT_to_Qlt; exact Hd0).
  destruct (Qlt_le_dec (projT1 q n) 0) as [Hqn | Hqn].
  - assert (Habs : Qabs (projT1 q n) == - projT1 q n)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hqn).
    rewrite Habs.
    assert (Hp2 : Qlt 0 (- projT1 q n - projT1 q n)) by lra.
    assert (Habs2 : Qabs (- projT1 q n - projT1 q n)
                    == - projT1 q n - projT1 q n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hp2).
    rewrite Habs2.
    lra.
  - assert (Habs : Qabs (projT1 q n) == projT1 q n)
      by (apply Qabs_pos; exact Hqn).
    rewrite Habs.
    assert (Hz2 : projT1 q n - projT1 q n == 0) by lra.
    rewrite Hz2.
    assert (Hz3 : Qabs 0 == 0) by reflexivity.
    rewrite Hz3.
    apply QltT_to_Qlt. exact Heps0.
Qed.

(* A.2 双 abs 乘积恒等（无条件）：|x·q| ≡ |x|·|q|。
   由 real_eq_of_zero_diff 化为逐点零差，再以 Qabs_mult 恒等收束（Q 层，无经典逻辑）。 *)
Lemma s6f_abs_abs_mult_eq : forall x q : Real,
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) (real_abs q)).
Proof.
  intros x q. apply real_eq_of_zero_diff. intro n.
  rewrite !real_abs_proj.
  rewrite !real_mult_proj.
  rewrite !real_abs_proj.
  rewrite Qabs_Qmult.
  lra.
Qed.

(* A.3 点态 abs 改写主引理（其一转换层核心）：0 ≤_B q ⟹ |x·q| ≡ |x|·q。
   链：|x·q| ≡ |x|·|q|（A.2）≡ |x|·q（A.1 加 RealSetoid.real_eq_mult_compat）。 *)
Lemma s6f_abs_mult_eq : forall x q : Real,
  real_le_b real_zero q ->
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) q).
Proof.
  intros x q Hq.
  eapply real_eq_trans.
  - apply s6f_abs_abs_mult_eq.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply s6f_abs_nonneg_eq. exact Hq.
Qed.

(* A.4 B 形右端相等运输（uabS4c_leb_req_left 的对偶命题，树内原缺，本件补齐）：
   a ≡ b 且 Y ≤_B a ⟹ Y ≤_B b。
   思路：预算 d 取半（h := d·½）——real_eq 在预算 h 上取 |a_n−b_n| < h 尾部，
   与 Y+a 侧预算 d 按 max 尾对齐，Q 层 lra 收束。 *)
Lemma s6f_leb_req_right : forall a b Y : Real,
  real_eq a b -> real_le_b Y a -> real_le_b Y b.
Proof.
  intros a b Y Hab HYa eps Heps.
  pose proof (HYa eps Heps) as HYa'.
  unfold real_le_b in HYa'. unfold real_lt in HYa'.
  destruct HYa' as [d [Hd [N1 HN1]]].
  (* 半量见证：h := d·½——等式预算恰取半量，于是 d−h = h，max 尾对齐后精确收束 *)
  assert (Hh : Qlt 0 (d * (1#2))).
  { apply QltT_to_Qlt in Hd. lra. }
  assert (HhT : QltT 0 (d * (1#2))) by (apply Qlt_to_QltT; exact Hh).
  destruct (Hab (d * (1#2)) HhT) as [N2 HN2].
  exists (d * (1#2)). split.
  - exact HhT.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Ha1 : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Ha2 : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha1) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Ha2) as Hp2. apply QltT_to_Qlt in Hp2.
    assert (Hge : Qle (projT1 a n - projT1 b n)
                      (Qabs (projT1 a n - projT1 b n)))
      by apply Qle_Qabs.
    assert (Hp2' : Qlt (projT1 a n - projT1 b n) (d * (1#2)))
      by (apply (Qle_lt_trans _ (Qabs (projT1 a n - projT1 b n)) _);
          [exact Hge | exact Hp2]).
    rewrite real_plus_proj.
    lra.
Qed.

(* §B · 其一（abs_kernel_bound 形）的供给：同语句形的 B 层供给              *)
(*   （语句形逐位保持：|Σ f·q| ≤_B Σ |f|·q；载体＝具体 Real；               *)
(*     sumf 抽象＝任意 S:Set 求和算子，三前提＝供体定理前提的显式量化）      *)

Theorem s6f_abs_kernel_bound_slot :
  forall (S : Set) (sumf : (S -> Real) -> Real),
    (forall f g : S -> Real,
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
    (forall f g : S -> Real,
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g))) ->
    (forall f g : S -> Real,
      (forall s : S, real_le_b (f s) (g s)) -> real_le_b (sumf f) (sumf g)) ->
    forall (f q : S -> Real),
      (forall s : S, real_le_b real_zero (q s)) ->
      real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                (sumf (fun s : S => real_mult (real_abs (f s)) (q s))).
Proof.
  intros S sumf Hext Hadd Hleb f q Hq.
  (* 供体 uabS4c_abs_sum_le_B_slot 在 g := f·q 上直接应用：|Σ f·q| ≤_B Σ |f·q| *)
  assert (Hdon : real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                           (sumf (fun s : S => real_abs (real_mult (f s) (q s)))))
    by (apply (uabS4c_abs_sum_le_B_slot S sumf Hext Hadd Hleb)).
  (* 点态转换：|f s·q s| ≡ |f s|·q s（q s ≥_B 0） *)
  assert (Hpt : forall s : S, real_eq (real_abs (real_mult (f s) (q s)))
                                      (real_mult (real_abs (f s)) (q s)))
    by (intro s; apply s6f_abs_mult_eq; exact (Hq s)).
  (* 求和算子外延性运输（前提一 Hext） *)
  assert (Hsum : real_eq (sumf (fun s : S => real_abs (real_mult (f s) (q s))))
                         (sumf (fun s : S => real_mult (real_abs (f s)) (q s))))
    by (apply Hext; exact Hpt).
  (* B 形右端相等运输（本件 A.4） *)
  exact (s6f_leb_req_right _ _ _ Hsum Hdon).
Qed.

(* §C · 其二（eviction_steady_deviation 形）：零新增构造的已证结论          *)
(*   S06 对 abs_sum_le 的使用＝类字段裸应用（零特化：abs_sum_le (fun s' => ...) *)
(*   原样应用），其语句形供给＝uabS4c_abs_sum_le_B_slot 本身（同语句覆盖，§0 已核验）； *)
(*   差分改写/线性提出面＝接口 Id 代数重述（不使用新供给）。不强行特化。      *)

(* 假设审计：六件 Print Assumptions 全 Closed *)
Print Assumptions s6f_q_const_pos.
Print Assumptions s6f_abs_nonneg_eq.
Print Assumptions s6f_abs_abs_mult_eq.
Print Assumptions s6f_abs_mult_eq.
Print Assumptions s6f_leb_req_right.
Print Assumptions s6f_abs_kernel_bound_slot.
