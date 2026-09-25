(* ============================================================
   UpAblAbsSumLeB3 —— 使命行：abstract sumf 接口本位 B 形供给模块
(*                                                                *)
(* 使命：本件形式化 |Σ sumf f| ≤_B Σ sumf (fun s => |f s|)—— *)
(*   在 UpReqSampling 的诚实求和接口形（sum_ext/sum_linear/sum_add/     *)
(*   sum_le/abs_sum_le_h 五接口字段；R:=Real 特化面，                   *)
(*   RealInterfaceEnhancedSetoid 的 Real 实例在场）上，以显式 Set 层    *)
(*   前提供给：单调字段取 Bishop 升级形（逐点 real_le_b；库形 Or 字段    *)
(*   经 real_le_to_le_b 单步升格即得，本前提严格弱于库 Or 字段＝结论     *)
(*   更强）。与 UpAblAbsSumLeB2 的折叠接口相对形（list 索引、            *)
(*   nil/cons 两条方程、归纳机理）不同构：彼为有限折叠，本件为求和接口    *)
(*   本位（任意 S:Set、无 list 结构、接口代数+双侧夹逼机理）——           *)
(*   并列共存，互为对照。                                                *)
(*   Closed 约定＝零公理而非零前提：节变量在 End 时全称化收纳，           *)
(*   非零前提＝三接口字段（外延/加法/单调 Bishop 形）+无其它，            *)
(*   逐条显式量词化在案。                                                *)
(* 依赖：Stdlib List、QArith.Qring、QArith.Qabs、QArith.Qminmax、        *)
(*        Lia、Lqa；CW_ConstructiveWorld_219、UpRealLeB、                 *)
(*        S08_RealMainlineDPO、UpAblAbsSumLeB。                           *)
(* 对标：mathlib abs_sum_le_sum_abs（和的绝对值三角不等式）；             *)
(*        本件为接口本位 Bishop 形的构造性对应物。                        *)
(* 构造性注记：零承认件：无承认词面、无假设参数声明、无经典逻辑、          *)
(*   全件 Qed 闭合；全部语句 Set 层值（real_le/real_lt/real_eq/           *)
(*   real_le_b/Qle/Qlt 均集合层），语句面无裸命题；                       *)
(*   证明全构造（Or 逐支、sigT 见证直接构造、Q 侧 Qlt_le_dec 可判定       *)
(*   符号二分；Q 层吸收引理以显式 Z 序引理链构造：                        *)
(*   乘法单调 Z.mul_le_mono_nonneg_r、反序性 Z.opp_le_mono、              *)
(*   正性见证 Pos2Z.is_pos）。                                            *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB.

(* ============================================================ *)
(* §0 库内接口核对（Check 逐项对照真实签名）                              *)
(* ============================================================ *)

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

(* ============================================================ *)
(* §1 实数层基础引理（点态 B 吸收/双侧夹逼/半分构造/兼容对）               *)
(* ============================================================ *)

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

(* ============================================================ *)
(* §2 SumOver 抽象接口主件（同 UpReqSampling 的诚实接口形，                 *)
(*   R:=Real 特化；三字段＝显式 Set 层前提；abs_sum_le 字段不设——本件证之）  *)
(* ============================================================ *)

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

(* ============================================================ *)
(* §3 接口可满足性实例（bool 两点和形）＋供体对照                            *)
(* ============================================================ *)

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
   同语句——接口通路独立复验（零增量对照，两读并列）。
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

(* ============================================================ *)
(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设；节变量 End 全称化收纳） *)
(* ============================================================ *)

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
