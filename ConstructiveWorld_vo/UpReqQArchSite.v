(* ============================================================
   UpReqQArchSite —— 使命行：Hqarch 前件构造性闭合
   （Bernoulli × Archimedes Q 层站点件）。
(* 使命：闭合主定理 mix_k_select_bishop（R2BishopLogSel.v L330，只读）  *)
(*   的显式前件 Hqarch——「Q 层收缩幂 Archimedean 站点」：               *)
(*     forall (p v b : Q), Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->  *)
(*       sigT (fun j : nat => Qle (mixe_qpow p j * v) b).              *)
(*                                                                    *)
(* 数学路线（全构造，j 显式可计算项，无反证存在性）：                    *)
(*   记 w := 1-p ∈ (0,1]。Bernoulli 锐化（mixe_bern_sharp 直取）：      *)
(*     p^j * (1 + j*w) <= 1。                                          *)
(*   Archimedes 站（mixe_qfloor_lt 直取 ceil 见证，无前提）：            *)
(*     j := S(Z.to_nat(Qfloor(v / (b*w)))) 满足 v/(b*w) < j。          *)
(*   两侧乘 (w*b) > 0：v < j*w*b（除法代数 v/(b*w)*(w*b) == v）。       *)
(*   链：p^j*(1+j*w)*v <= 1*v < j*w*b <= (1+j*w)*b，                    *)
(*   再以 (1+j*w) > 0 右消（Qmult_lt_0_le_reg_r）得 p^j*v <= b。        *)
(*                                                                    *)
(* 复用件（绿盘只读 Require）：UpReqMixLogE——mixe_qpow / mixe_qofnat /  *)
(*   mixe_bern_sharp / mixe_qfloor_lt / mixe_qofnat_nonneg。           *)
(* 红线自检：无承认件/无经典逻辑/无任何外挂假设；j 为 nat 显式项        *)
(*   （stdlib Qfloor + Z.to_nat，Q 层全可判定零墙）；语句面与 Hqarch    *)
(*   契约原形逐字同构（sigT 见证形，projT1 可提取）。                   *)
   ============================================================*)

From Stdlib Require Import QArith.QArith_base.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
Require Import UpReqMixLogE.
Require Import R2BishopLogSel.

Open Scope Q_scope.

(* ============================================================ *)
(* 站点选取器：j := S(Z.to_nat(Qfloor(x/y)))——x/y 的显式上取整 nat 站    *)
(* mixe_qfloor_lt 保证 x/y < mixe_qofnat j（无任何前提，全 Q 可判定）。  *)
(* ============================================================ *)
Definition qarch_ceil (x y : Q) : nat :=
  Datatypes.S (Z.to_nat (Qfloor (Qdiv x y))).

(* 消解件：与 R2BishopLogSel.v L330 主定理前件 Hqarch 逐字同构 *)
Theorem qarch_site : forall (p v b : Q),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  sigT (fun j : nat => Qle (mixe_qpow p j * v) b).
Proof.
  intros p v b Hp0 Hp1 Hv Hb.
  (* 0 < w <= 1，w := 1-p *)
  assert (Hw0s : (0 < 1 - p)%Q) by (exact (proj1 (Qlt_minus_iff p 1) Hp1)).
  assert (Hp0le : (0 <= p)%Q) by (apply (Qlt_le_weak 0%Q p); exact Hp0).
  assert (Hw1 : ((1 - p) <= 1)%Q).
  { pose proof (Qopp_le_compat 0%Q p Hp0le) as H1.
    pose proof (Qplus_le_compat (- p)%Q (- 0)%Q 1%Q 1%Q H1 (Qle_refl 1%Q)) as H2.
    assert (Hr1 : (- p + 1)%Q == (1 - p)%Q) by ring.
    rewrite Hr1 in H2.
    assert (Hr2 : (- 0 + 1)%Q == 1%Q) by ring.
    rewrite Hr2 in H2.
    exact H2. }
  assert (Hw0le : (0 <= 1 - p)%Q) by (apply (Qlt_le_weak 0%Q (1 - p)%Q); exact Hw0s).
  assert (Hb0le : (0 <= v)%Q) by (apply (Qlt_le_weak 0%Q v); exact Hv).
  assert (Hbb0le : (0 <= b)%Q) by (apply (Qlt_le_weak 0%Q b); exact Hb).
  (* b*w > 0 及其非零 *)
  assert (Hbw : (0 < b * (1 - p))%Q)
    by (apply (Qmult_lt_0_compat b (1 - p)%Q Hb Hw0s)).
  assert (Hbwne : ~ ((b * (1 - p)) == 0)%Q).
  { intro Hz.
    apply (Qlt_not_eq 0%Q (b * (1 - p))%Q Hbw).
    exact (Qeq_sym (b * (1 - p))%Q 0%Q Hz). }
  (* Archimedes 站：v/(b*w) < mixe_qofnat j（j 全称显式） *)
  assert (Harch : (Qdiv v (b * (1 - p)) <
                   mixe_qofnat (qarch_ceil v (b * (1 - p))))%Q).
  { exact (mixe_qfloor_lt (Qdiv v (b * (1 - p))%Q)). }
  (* 除法代数：v/(b*w) * (w*b) == v *)
  assert (Hinv1 : (Qinv (b * (1 - p)) * (b * (1 - p)) == 1)%Q).
  { rewrite (Qmult_comm (Qinv (b * (1 - p))) (b * (1 - p))).
    apply (Qmult_inv_r (b * (1 - p))%Q).
    exact Hbwne. }
  assert (HdivA : (Qdiv v (b * (1 - p)) * ((1 - p) * b) == v)%Q).
  { unfold Qdiv.
    rewrite (Qmult_comm (1 - p) b).
    rewrite <- Qmult_assoc.
    rewrite Hinv1.
    apply (Qmult_1_r v). }
  (* 乘 (w*b) > 0 得 v < j*w*b *)
  assert (Hwb0 : (0 < (1 - p) * b)%Q)
    by (apply (Qmult_lt_0_compat (1 - p)%Q b Hw0s Hb)).
  assert (Hvlt : (v < mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p) * b)%Q).
  { pose proof (Qmult_lt_compat_r (Qdiv v (b * (1 - p)))
                  (mixe_qofnat (qarch_ceil v (b * (1 - p))))
                  ((1 - p) * b) Hwb0 Harch) as Hm.
    rewrite HdivA in Hm.
    rewrite Qmult_assoc in Hm.
    exact Hm. }
  (* j*w > 0；1+j*w > 0；Bernoulli 锐化 *)
  assert (Hjw : (0 <= mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q).
  { apply (Qmult_le_0_compat (mixe_qofnat (qarch_ceil v (b * (1 - p)))) (1 - p)%Q).
    - apply mixe_qofnat_nonneg.
    - exact Hw0le. }
  assert (H01 : (0 < 1)%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
  assert (HS0 : (0 < 1 + mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q).
  { apply (Qlt_le_trans 0%Q 1%Q).
    - exact H01.
    - exact (Qplus_le_compat 1%Q 1%Q 0%Q
               (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))
               (Qle_refl 1%Q) Hjw). }
  assert (Hbern : (mixe_qpow p (qarch_ceil v (b * (1 - p))) *
                   (1 + mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p)) <= 1)%Q).
  { exact (rb_bern_sharp' p (qarch_ceil v (b * (1 - p))) Hp0le Hp1). }
  set (S := (1 + mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q).
  (* 链一：(p^j * S) * v <= 1 * v *)
  assert (Hstep1 : ((mixe_qpow p (qarch_ceil v (b * (1 - p))) * S) * v <= 1 * v)%Q).
  { apply (Qmult_le_compat_r (mixe_qpow p (qarch_ceil v (b * (1 - p))) * S) 1%Q v).
    - exact Hbern.
    - exact Hb0le. }
  (* 链二：j*w*b <= S*b（j*w <= 1 + j*w = S 平移，经 0+j*w 中站） *)
  assert (Hstep2 : (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p) * b <= S * b)%Q).
  { apply (Qmult_le_compat_r (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p)) S b).
    - apply (Qle_trans _ (0 + mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q).
      + apply (mixe_qeq_le (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))
                 (0 + mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q).
        * ring.
      + exact (Qplus_le_compat 0%Q 1%Q
                 (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))
                 (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))
                 (Qlt_le_weak 0%Q 1%Q H01)
                 (Qle_refl (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p))%Q)).
    - exact Hbb0le. }
  (* 总链：(p^j * S) * v <= S * b *)
  assert (Hchain : ((mixe_qpow p (qarch_ceil v (b * (1 - p))) * S) * v <= S * b)%Q).
  { apply (Qle_trans _ _ _ Hstep1).
    apply (Qle_trans _ (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p) * b)%Q).
    - rewrite Qmult_1_l.
      apply (Qlt_le_weak v (mixe_qofnat (qarch_ceil v (b * (1 - p))) * (1 - p) * b)%Q).
      exact Hvlt.
    - exact Hstep2. }
  (* S 换位到右因子，再以 S > 0 右消（Qmult_lt_0_le_reg_r） *)
  assert (HeqS : ((mixe_qpow p (qarch_ceil v (b * (1 - p))) * S) * v ==
                  S * (mixe_qpow p (qarch_ceil v (b * (1 - p))) * v))%Q) by ring.
  rewrite HeqS in Hchain.
  rewrite (Qmult_comm S (mixe_qpow p (qarch_ceil v (b * (1 - p))) * v)) in Hchain.
  rewrite (Qmult_comm S b) in Hchain.
  (* 站点见证交付 *)
  exists (qarch_ceil v (b * (1 - p))).
  exact (Qmult_lt_0_le_reg_r (mixe_qpow p (qarch_ceil v (b * (1 - p))) * v) b S HS0 Hchain).
Defined.

(* 提取面封装：j 构造函数（四个 Qlt 前件在提取层擦除，余项纯计算 nat） *)
Definition qarch_site_j (p v b : Q)
  (Hp0 : Qlt 0 p) (Hp1 : Qlt p 1) (Hv : Qlt 0 v) (Hb : Qlt 0 b) : nat :=
  projT1 (qarch_site p v b Hp0 Hp1 Hv Hb).

(* 编译期自证：闭合无外挂假设（输出入编译日志作 G4 旁证） *)
Print Assumptions qarch_site.
Print Assumptions qarch_site_j.
