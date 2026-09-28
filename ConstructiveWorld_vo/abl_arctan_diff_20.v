(* ==========================================================================)
   abl_arctan_diff_20.v — arctan 差公式件续片（斜率合成精确恒等＋小跨度常值判据）
   使命: 接 abl_arctan_diff_19 推进三项：
     其一 斜率合成精确恒等 abl9_slope_id：w:=(u−v)/(1+uv) 的 (u+s) 处增量
     乘 (1+uv)²/((1+u²)(1+v²))（=1/(1+w²)，abl9_wsq_div_id 之逆形）与复合
     斜率替换 s/(1+u²) 之差== s²v/((1+(u+s)v)(1+u²))——phi'(t)=0 的精确
     代数核（O(s²) 小项显式）；分母非零旁支经 abl9_q_pos_sq（1+q² 非零，
     Q 平方非负构造）＋两给定直立。
     其二 常值判据（小跨度版）：abl9_real_tail_bnd（柯西实数的逐点终近
     上界——构造性，cauchy eps=1 单发+abs_shift 三角）＋abl9_const_crit
     （「基点 a 处增量估计对任意 eps/eps' 成立（步长 |s|<delta 一致）→
     real_eq (phi(a+s)) (phi a)」）——real_eq 逐点终近形直拆：尾界 B+
     跨度预算 c:=eps/(8(B+1))，real_le 双分支（real_lt/real_eq）各产逐点
     界（real_eq 分支以 abs_shift 三角收敛），单步 3eps/4<eps。诚实申明：
     本片系小跨度版（|s|<delta）；N 等步链版（跨 [0,h] 多步+Q→nat
     ceiling+min/max 折叠）登记未竟，构造分析随登记。
     其三 主定理 abl9_atan_diff_formula 本片未闭合，登记未竟；装配余项=
     phi 步界件（步界两次应用+斜率桥+三角复合）、arctan 合同
     （b5c_arctan_partial_wd 升 real 层）、端点值 phi(0)==0、W(x+h) 与
     h·inv(1+x(x+h)) 的 real_inv_pos_ext 对齐；内点域缺口一并登记。
     另备 Qeq 在 QltT/Qlt 下传递四助手与 Qabs 合同引理（全片复用）。
   依赖: S01_BaseRing–S11_TP3B5、abl_arctan_diff_19；Stdlib QArith、List、
     Setoid、Lia、Qminmax、GenericMinMax、Extraction。
   构造性: 全件 Qed 闭合（十引理零承认式语句）；Set 层零 Prop 泄露口径；可提取
     （尾 Print Assumptions + Recursive Extraction，判据 Closed + Obj.magic 0）。
   编译配方: export COQLIB="C:/Rocq-Platform~9.1~2026.01/lib/coq"，ROCQLIB
     同值；C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe -q -native-compiler no
     -Q <库树根> "" abl_arctan_diff_20.v（库内就地编译；依赖件 S01–S11 与
     abl_arctan_diff_19 编译产物在位。）
   ========================================================================== *)

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
Require Import abl_arctan_diff_19.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* ③·基建：Qeq 在 QltT/Id(Qlt_bool) 下不可直接改写——本件新坑，         *)
(*   四传递助手全片复用（QltT 版先行，Qlt 版经 Qlt_to_QltT 复用）        *)
(* ============================================================ *)
Lemma abl9_QltT_transfer_l : forall x y z : Q, x == y -> QltT x z -> QltT y z.
Proof.
  intros x y z Hxy Hlt.
  assert (Hx : Qlt x z) by (apply QltT_to_Qlt; exact Hlt).
  apply Qlt_to_QltT. apply (Qle_lt_trans y x z).
  - apply qeq_imp_qle. apply Qeq_sym. exact Hxy.
  - exact Hx.
Qed.

Lemma abl9_QltT_transfer_r : forall x y z : Q, y == z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hlt.
  apply Qlt_to_QltT. apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hlt.
  - apply qeq_imp_qle. exact Hyz.
Qed.

Lemma abl9_Qlt_transfer_l : forall x y z : Q, x == y -> Qlt x z -> Qlt y z.
Proof.
  intros x y z Hxy Hlt.
  apply (Qle_lt_trans y x z).
  - apply qeq_imp_qle. apply Qeq_sym. exact Hxy.
  - exact Hlt.
Qed.

Lemma abl9_Qlt_transfer_r : forall x y z : Q, y == z -> Qlt x y -> Qlt x z.
Proof.
  intros x y z Hyz Hlt.
  apply (Qlt_le_trans x y z).
  - exact Hlt.
  - apply qeq_imp_qle. exact Hyz.
Qed.

(* Qeq 在 Qabs 内的正则化 *)
Lemma abl9_Qabs_wd : forall x y : Q, x == y -> Qabs x == Qabs y.
Proof. intros x y H. apply (Qabs_wd x y). exact H. Qed.

(* ============================================================ *)
(* ②·基建：Q 平方非负 → 1+q² 非零（slope_id 与 Real 桥共用）           *)
(* ============================================================ *)
Lemma abl9_q_pos_sq : forall q : Q, ~ (1 + q * q == 0).
Proof.
  intros q Hp.
  destruct (Qlt_le_dec 0 q) as [Hq | Hq].
  - assert (Hqle : Qle 0 q) by (apply Qlt_le_weak; exact Hq).
    assert (Hs : Qle 0 (q * q)) by (apply Qmult_le_0_compat; exact Hqle).
    assert (H1 : Qle 1 (1 + q * q)).
    { apply (Qle_trans 1 (1 + 0) (1 + q * q)).
      - apply qeq_imp_qle. ring.
      - apply Qplus_le_compat. apply Qle_refl. exact Hs. }
    assert (H2 : Qle (1 + q * q) 0) by (apply qeq_imp_qle; exact Hp).
    assert (H3 : Qle 1 0) by (apply (Qle_trans 1 (1 + q * q) 0); [exact H1 | exact H2]).
    exfalso. unfold Qle in H3. simpl in H3. lia.
  - assert (Hneg : Qle 0 (Qopp q)).
    { apply (Qle_trans 0 (Qopp 0) (Qopp q)).
      - apply qeq_imp_qle. ring.
      - apply Qopp_le_compat. exact Hq. }
    assert (Hs : Qle 0 (Qopp q * Qopp q)) by (apply Qmult_le_0_compat; exact Hneg).
    assert (Hs2 : Qle 0 (q * q)).
    { apply (Qle_trans 0 (Qopp q * Qopp q) (q * q)).
      - exact Hs.
      - apply qeq_imp_qle. ring. }
    assert (H1 : Qle 1 (1 + q * q)).
    { apply (Qle_trans 1 (1 + 0) (1 + q * q)).
      - apply qeq_imp_qle. ring.
      - apply Qplus_le_compat. apply Qle_refl. exact Hs2. }
    assert (H2 : Qle (1 + q * q) 0) by (apply qeq_imp_qle; exact Hp).
    exfalso.
    assert (H3 : Qle 1 0) by (apply (Qle_trans 1 (1 + q * q) 0); [exact H1 | exact H2]).
    unfold Qle in H3. simpl in H3. lia.
Qed.

(* ============================================================ *)
(* ②·斜率合成精确恒等（除法形，phi'(t)=0 的精确代数核）                *)
(* ============================================================ *)
Lemma abl9_slope_id : forall u v s : Q,
  ~ (1 + (u + s) * v == 0) -> ~ (1 + u * v == 0) ->
  s / (1 + u * u)
  - ((u + s - v) / (1 + (u + s) * v) - (u - v) / (1 + u * v))
    * ((1 + u * v) * (1 + u * v) / ((1 + u * u) * (1 + v * v))) ==
  s * s * v / ((1 + (u + s) * v) * (1 + u * u)).
Proof.
  intros u v s H1 H2.
  assert (Hu2 : ~ (1 + u * u == 0)) by apply abl9_q_pos_sq.
  assert (Hv2 : ~ (1 + v * v == 0)) by apply abl9_q_pos_sq.
  field. repeat split; assumption.
Qed.

(* ============================================================ *)
(* ③·辅助：Q 绝对值位移三角（|a| ≤ |a−b|+|b|）                        *)
(* ============================================================ *)
Lemma abl9_abs_shift : forall a b : Q, Qle (Qabs a) (Qabs (a - b) + Qabs b).
Proof.
  intros a b.
  apply (Qle_trans (Qabs a) (Qabs ((a - b) + b)) (Qabs (a - b) + Qabs b)).
  - apply qeq_imp_qle. apply abl9_Qabs_wd. ring.
  - apply Qabs_triangle.
Qed.

(* ============================================================ *)
(* ③·辅助：柯西实数的逐点终近上界（构造性；cauchy eps=1 单发）         *)
(* ============================================================ *)
Lemma abl9_real_tail_bnd : forall x : Real,
  sigT (fun B : Q => And (QltT 0 B)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
       Qle (Qabs (projT1 x n)) B))).
Proof.
  intros x. destruct x as [u Hu].
  assert (H1 : QltT 0 1) by reflexivity.
  destruct (Hu 1 H1) as [N HN].
  exists (Qabs (u N) + 1).
  split.
  - apply Qlt_to_QltT.
    assert (H1le : Qle 1 (Qabs (u N) + 1)).
    { apply (Qle_trans 1 (1 + 0) (Qabs (u N) + 1)).
      - apply qeq_imp_qle. ring.
      - apply (Qle_trans (1 + 0) (1 + Qabs (u N)) (Qabs (u N) + 1)).
        + apply (Qplus_le_compat 1 1 0 (Qabs (u N))).
          * apply Qle_refl.
          * apply Qabs_nonneg.
        + apply qeq_imp_qle. ring. }
    apply (Qlt_le_trans 0 1 (Qabs (u N) + 1)).
    + unfold Qlt. simpl. lia.
    + exact H1le.
  - exists N. intros n Hn.
    cbn [projT1].
    apply (Qle_trans (Qabs (u n)) (Qabs (u n - u N) + Qabs (u N)) (Qabs (u N) + 1)).
    + apply abl9_abs_shift.
    + apply (Qle_trans (Qabs (u n - u N) + Qabs (u N)) (1 + Qabs (u N)) (Qabs (u N) + 1)).
      * apply Qplus_le_compat.
        -- apply Qlt_le_weak. apply QltT_to_Qlt.
           apply (HN n N Hn (NatLe_lift N N (Nat.le_refl N))).
        -- apply Qle_refl.
      * apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* ③·小跨度常值判据：一致增量估计 → real_eq                           *)
(* ============================================================ *)
Lemma abl9_const_crit :
  forall (phi : Real -> Real) (a s delta : Real),
  real_lt real_zero delta ->
  real_lt (real_abs s) delta ->
  (forall (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' ->
     real_le (real_abs (real_plus (phi (real_plus a s)) (real_opp (phi a))))
             (real_plus (real_mult eps (real_abs s)) eps')) ->
  real_eq (phi (real_plus a s)) (phi a).
Proof.
  intros phi a s delta Hdelta Hspan Hstep eps Heps.
  assert (HepsQ : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  destruct (abl9_real_tail_bnd s) as [B [HB0 [Nb HB]]].
  assert (HBQ : Qlt 0 B) by (apply QltT_to_Qlt; exact HB0).
  assert (HB1 : Qlt 0 (B + 1)).
  { apply (Qlt_le_trans 0 B (B + 1)).
    - exact HBQ.
    - apply (Qle_trans B (B + 0) (B + 1)).
      + apply qeq_imp_qle. ring.
      + apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  set (c := (eps / (8 * (B + 1)))%Q).
  assert (Hc0 : Qlt 0 c).
  { unfold c. unfold Qdiv. apply Qmult_lt_0_compat.
    - exact HepsQ.
    - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
      + unfold Qlt. simpl. lia.
      + exact HB1. }
  (* 跨度预算：c·B ≤ eps/8 *)
  assert (HB1le : Qle B (B + 1)).
  { apply (Qle_trans B (B + 0) (B + 1)).
    - apply qeq_imp_qle. ring.
    - apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia. }
  assert (HcB : Qle (c * B) ((1 # 8) * eps)).
  { unfold c.
    apply (Qle_trans (eps / (8 * (B + 1)) * B)
                     ((B + 1) * (eps / (8 * (B + 1)))) ((1 # 8) * eps)).
    - apply (Qle_trans (eps / (8 * (B + 1)) * B)
                       (B * (eps / (8 * (B + 1))))
                       ((B + 1) * (eps / (8 * (B + 1))))).
      + apply qeq_imp_qle. ring.
      + apply Qmult_le_compat_r.
        * exact HB1le.
        * apply Qmult_le_0_compat.
          -- apply Qlt_le_weak. exact HepsQ.
          -- apply Qlt_le_weak. apply Qinv_lt_0_compat.
             apply Qmult_lt_0_compat; [reflexivity | exact HB1].
    - apply qeq_imp_qle. field.
      intro Hz. apply (Qlt_not_eq 0 (B + 1) HB1).
      apply Qeq_sym. exact Hz. }
  assert (Hc' : real_lt real_zero (real_const c))
    by (apply real_const_pos_f1; exact Hc0).
  assert (He2 : real_lt real_zero (real_const (eps / 2))).
  { apply real_const_pos_f1. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hcsn : forall n : nat, NatLe Nb n ->
                 Qle (c * Qabs (projT1 s n)) ((1 # 8) * eps)).
  { intros n Hnnb.
    apply (Qle_trans (c * Qabs (projT1 s n))
                     (Qabs (projT1 s n) * c) ((1 # 8) * eps)).
    - apply qeq_imp_qle. ring.
    - apply (Qle_trans (Qabs (projT1 s n) * c) (B * c) ((1 # 8) * eps)).
      + apply Qmult_le_compat_r.
        * exact (HB n Hnnb).
        * apply Qmult_le_0_compat.
          -- apply Qlt_le_weak. exact HepsQ.
          -- apply Qlt_le_weak. apply Qinv_lt_0_compat.
             apply Qmult_lt_0_compat; [reflexivity | exact HB1].
      + apply (Qle_trans (B * c) (c * B) ((1 # 8) * eps)).
        * apply qeq_imp_qle. ring.
        * exact HcB. }
  destruct (Hstep (real_const c) (real_const (eps / 2)) Hc' He2) as [Hr | Hr].
  - (* real_lt 分支：∃q>0, ∃M: ∀n≥M: q < bound_n − |Δ_n| *)
    destruct Hr as [q [Hq0 [M Hq]]].
    exists (Nat.max Nb M).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hm : (M <= n)%nat) by lia.
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    assert (Hqn : Qlt q (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
    { apply (Qlt_le_trans q
        (projT1 (real_plus (real_mult (real_const c) (real_abs s))
                           (real_const (eps / 2))) n
         - projT1 (real_abs (real_plus (phi (real_plus a s))
                                        (real_opp (phi a)))) n)
        (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an))).
      - apply QltT_to_Qlt. apply (Hq n). apply NatLe_lift. exact Hm.
      - apply qeq_imp_qle.
        rewrite (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n).
        rewrite (real_mult_proj (real_const c) (real_abs s) n).
        rewrite (real_const_proj c n).
        rewrite (real_abs_proj s n).
        rewrite (real_abs_proj (real_plus (phi (real_plus a s)) (real_opp (phi a))) n).
        rewrite (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n).
        rewrite (real_opp_proj (phi a) n).
        cbn [projT1 real_const real_zero].
        unfold dn, an, Qminus. ring. }
    assert (Hqn2 : Qlt 0 ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
    { apply (abl9_Qlt_transfer_r 0
               ((c * Qabs (projT1 s n) + eps / 2) - Qabs (dn - an) - q)
               ((c * Qabs (projT1 s n) + eps / 2 - q) - Qabs (dn - an))).
      - ring.
      - apply (proj1 (Qlt_minus_iff q
                 (c * Qabs (projT1 s n) + eps / 2 - Qabs (dn - an)))).
        exact Hqn. }
    assert (Hd1 : Qlt (Qabs (dn - an)) (c * Qabs (projT1 s n) + eps / 2)).
    { apply (Qlt_trans (Qabs (dn - an))
             (c * Qabs (projT1 s n) + eps / 2 - q)
             (c * Qabs (projT1 s n) + eps / 2)).
      - apply (proj2 (Qlt_minus_iff (Qabs (dn - an))
                 (c * Qabs (projT1 s n) + eps / 2 - q))). exact Hqn2.
      - apply (proj2 (Qlt_minus_iff (c * Qabs (projT1 s n) + eps / 2 - q)
                 (c * Qabs (projT1 s n) + eps / 2))).
        apply QltT_to_Qlt.
        apply (abl9_QltT_transfer_r 0 q
                 ((c * Qabs (projT1 s n) + eps / 2)
                  - (c * Qabs (projT1 s n) + eps / 2 - q))).
        + apply Qeq_sym.
          assert (Heqq : (c * Qabs (projT1 s n) + eps / 2)
                         - (c * Qabs (projT1 s n) + eps / 2 - q) == q) by ring.
          exact Heqq.
        + exact Hq0. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (Qabs (dn - an))
                        (c * Qabs (projT1 s n) + eps / 2) eps).
    + exact Hd1.
    + apply (Qle_trans (c * Qabs (projT1 s n) + eps / 2)
                       ((1 # 8) * eps + (1 # 2) * eps) eps).
      * apply Qplus_le_compat.
        -- apply (Hcsn n (NatLe_lift Nb n Hnb)).
        -- apply qeq_imp_qle. apply Qmult_comm.
      * apply (Qle_trans ((1 # 8) * eps + (1 # 2) * eps) ((5 # 8) * eps) eps).
        -- apply qeq_imp_qle. ring.
        -- apply (Qle_trans ((5 # 8) * eps) (1 * eps) eps).
           ++ apply Qmult_le_compat_r.
              ** unfold Qle. simpl. lia.
              ** apply Qlt_le_weak. exact HepsQ.
           ++ apply qeq_imp_qle. ring.
  - (* real_eq 分支：| |Δ_n| − bound_n | < eps/8 终近；三角+预算配平 *)
    assert (He8q : QltT 0 (eps / 8)).
    { apply Qlt_to_QltT. apply Qlt_shift_div_l.
      - reflexivity.
      - simpl. apply QltT_to_Qlt. exact Heps. }
    destruct (Hr (eps / 8) He8q) as [N2 H2].
    exists (Nat.max Nb N2).
    intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hnb : (Nb <= n)%nat) by lia.
    assert (Hn2 : (N2 <= n)%nat) by lia.
    set (dn := projT1 (phi (real_plus a s)) n).
    set (an := projT1 (phi a) n).
    set (MID := (c * Qabs (projT1 s n) + eps / 2)%Q).
    set (AB := Qabs (Qabs (dn - an) - MID)%Q).
    assert (H2' : QltT AB (eps / 8)).
    { apply (abl9_QltT_transfer_l
        (Qabs (projT1 (real_abs (real_plus (phi (real_plus a s))
                          (real_opp (phi a)))) n
               - projT1 (real_plus (real_mult (real_const c) (real_abs s))
                                   (real_const (eps / 2))) n))).
      - rewrite (real_abs_proj (real_plus (phi (real_plus a s))
                                  (real_opp (phi a))) n).
        rewrite (real_plus_proj (phi (real_plus a s)) (real_opp (phi a)) n).
        rewrite (real_opp_proj (phi a) n).
        rewrite (real_plus_proj (real_mult (real_const c) (real_abs s))
                   (real_const (eps / 2)) n).
        rewrite (real_mult_proj (real_const c) (real_abs s) n).
        rewrite (real_const_proj c n).
        rewrite (real_abs_proj s n).
        cbn [projT1 real_const real_zero].
        unfold AB. unfold MID, dn, an, Qminus. ring.
      - exact (H2 n (NatLe_lift _ _ Hn2)). }
    assert (HY0 : Qle 0 MID).
    { unfold MID.
      apply (Qplus_le_compat 0 (c * Qabs (projT1 s n)) 0 (eps / 2)).
      - apply Qmult_le_0_compat.
        + apply Qlt_le_weak. exact Hc0.
        + apply Qabs_nonneg.
      - apply Qmult_le_0_compat.
        + apply Qlt_le_weak. exact HepsQ.
        + apply Qlt_le_weak. apply Qinv_lt_0_compat. reflexivity. }
    assert (Htri : Qle (Qabs (dn - an)) (AB + MID)).
    { unfold AB.
      assert (HM : Qabs (c * Qabs (projT1 s n) + eps / 2)
                   == c * Qabs (projT1 s n) + eps / 2).
      { apply Qabs_pos. exact HY0. }
      apply (Qle_trans (Qabs (dn - an)) (Qabs (Qabs (dn - an)))
             (Qabs (Qabs (dn - an) - (c * Qabs (projT1 s n) + eps / 2))
              + (c * Qabs (projT1 s n) + eps / 2))).
      - apply qeq_imp_qle. apply Qeq_sym.
        apply Qabs_pos. apply Qabs_nonneg.
      - apply (Qle_trans (Qabs (Qabs (dn - an)))
               (Qabs (Qabs (dn - an) - (c * Qabs (projT1 s n) + eps / 2))
                + Qabs (c * Qabs (projT1 s n) + eps / 2))).
        + apply abl9_abs_shift.
        + apply qeq_imp_qle. rewrite HM. apply Qeq_refl. }
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (dn - an)) (AB + MID) eps).
    + exact Htri.
    + (* AB + MID < eps/8 + MID（经 Qlt_minus_iff 原语），再预算 ≤ eps *)
      assert (Hstep1 : Qlt (AB + MID) (eps / 8 + MID)).
      { apply (proj2 (Qlt_minus_iff (AB + MID) (eps / 8 + MID))).
        apply (abl9_Qlt_transfer_r 0 (eps / 8 - AB) ((eps / 8 + MID) - (AB + MID))).
        - ring.
        - apply (proj1 (Qlt_minus_iff AB (eps / 8))).
          apply QltT_to_Qlt. exact H2'. }
      apply (Qlt_le_trans (AB + MID) (eps / 8 + MID) eps).
      * exact Hstep1.
      * apply (Qle_trans (eps / 8 + MID)
                         (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)) eps).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply Qplus_le_compat.
              ** unfold MID. apply (Hcsn n (NatLe_lift Nb n Hnb)).
              ** apply qeq_imp_qle. apply Qmult_comm.
        -- apply (Qle_trans (eps / 8 + ((1 # 8) * eps + (1 # 2) * eps))
                            ((3 # 4) * eps) eps).
           ++ apply qeq_imp_qle.
              assert (Heq : eps / 8 + ((1 # 8) * eps + (1 # 2) * eps)
                            == (3 # 4) * eps) by field.
              exact Heq.
           ++ apply (Qle_trans ((3 # 4) * eps) (1 * eps)).
              ** apply Qmult_le_compat_r.
                 --- unfold Qle. simpl. lia.
                 --- apply Qlt_le_weak. exact HepsQ.
              ** apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取面                                              *)
(*   对账：Lemma 名清单 10 = Qed 计数 10；Print Assumptions 覆盖主链     *)
(*   8 引理（abl9_Qabs_wd、abl9_abs_shift 经调用面与提取覆盖）。        *)
(* ============================================================ *)
Print Assumptions abl9_QltT_transfer_l.
Print Assumptions abl9_QltT_transfer_r.
Print Assumptions abl9_Qlt_transfer_l.
Print Assumptions abl9_Qlt_transfer_r.
Print Assumptions abl9_q_pos_sq.
Print Assumptions abl9_slope_id.
Print Assumptions abl9_real_tail_bnd.
Print Assumptions abl9_const_crit.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_q_pos_sq abl9_slope_id abl9_real_tail_bnd.
