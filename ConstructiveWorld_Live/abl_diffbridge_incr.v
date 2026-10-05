(* ==========================================================================)
   abl_diffbridge_incr.v — HasIncr ↔ RealDifferentiable 互译桥（AI 脸归一系列 ①-B）
   使命: 双可微谓词互译——增量形（HasIncr，abl_arctan_diff_16 的 eps-线性
     近似形，总函数面）与记录形（RealDifferentiable，S08，rdf+rdf_correct
     eps 形，正性前提部分函数面）的双向互译桥，谓词归一防再分裂。
     五件陈述：
       0. HasIncrPos——带前提变体（对齐件）：与 rdf_correct 逐字同构
          （多出 Hx : 0<x 谓词索引与 Hxh : 0<x+h 域前提槽），两侧锚点共用面。
       1. dbi_realdiff_hasincrpos——记录→增量供给（rdf_correct 直取）。
       2. dbi_hasincrpos_realdiff——增量供给→记录构造（projT1 逐点
          sigT 选择，Set 层合法；Record 无 ext 槽，粘合无外延性障碍）。
       3. dbi_hasincr_incrpos / dbi_incrpos_hasincr——总函数面 HasIncr 与
          带前提面互接（前者弃 Hxh 直通；后者 δ 取 real_min δ₀ (x/2)
          域核算保 x+h 正，Q 层逐点会计）。
       4. dbi_realdiff_hasincr / dbi_hasincr_realdiff——两端到端组合
          （正域逐点增量供给 ⟺ 正域化记录）。
   依赖: S01_BaseRing–S11_TP3B5；abl_arctan_diff_16（HasIncr 定义＋
     abl9_qscale_pos/abl9_min_lt_l/abl9_min_lt_r 骨架件，Require-only 零改动）；
     S08 RealDifferentiable Record；S03 real_abs_proj；S07 real_min_pos；
     S10 real_le_eq_l；Stdlib QArith、List、Setoid、Lia。
   构造性: 纯构造性（全链 Qed 真构造，零承认式语句）；Set 层零 Prop 泄露
     （HasIncrPos 全由 real_lt/real_le/sigT/And 组装；斜率选择走 projT1
     逐点 sigT 投影，非经典选择）；非平凡（dbi_abs_lt_half_add_pos 为
     Q 层逐点会计真构造：半点域界 −|h_n| ≤ h_n、半·x_n ≤ x_n 装配）；
     可提取（尾 Print Assumptions，判据 Closed）。
   工艺红线: Qeq 换形全数以 qeq_le 桥＋== 目标内 rewrite 闭合，Qeq
     rewrite 零离开 == 目标；real_eq 侧 term-mode 显式实参；零 not/~/<> 书写。
   编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit
     -s 65532 && nice -19 rocq c -native-compiler no -Q <缓存根> "" 本件（池内执行）。
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
Require Import abl_arctan_diff_16.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.

(* ============================================================ *)
(* 0. 带前提增量谓词（对齐件）——与 S08 rdf_correct 逐字同构：      *)
(*    谓词索引 Hx（部分函数面）＋域前提 Hxh（0<x+h）；误差项斜率    *)
(*    乘序从 HasIncr（h·a）不从 rdf_correct（a·h），换形由         *)
(*    dbi_err_eq_comm 承担。全 Set 层。                            *)
(* ============================================================ *)
Definition HasIncrPos (f : forall x : Real, real_lt real_zero x -> Real)
           (x a : Real) (Hx : real_lt real_zero x) : Set :=
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun d : Real =>
    And (real_lt real_zero d)
        (forall (h : Real), real_lt (real_abs h) d ->
          forall (Hxh : real_lt real_zero (real_plus x h)),
          forall (eps' : Real), real_lt real_zero eps' ->
          real_le (real_abs (real_plus (f (real_plus x h) Hxh)
                     (real_opp (real_plus (f x Hx) (real_mult h a)))))
                  (real_plus (real_mult eps (real_abs h)) eps'))).

(* ============================================================ *)
(* 1. Q 小件三枚（dbi_abs_lt_half_add_pos 的逐点会计基座）          *)
(* ============================================================ *)
Lemma dbi_qplus_le_r : forall a b c : Q, Qle a b -> Qle (a + c) (b + c).
Proof.
  intros a b c H.
  apply (Qplus_le_compat a b c c).
  - exact H.
  - apply Qle_refl.
Qed.

Lemma dbi_qplus_le_l : forall a b c : Q, Qle a b -> Qle (c + a) (c + b).
Proof.
  intros a b c H.
  apply (Qplus_le_compat c c a b).
  - apply Qle_refl.
  - exact H.
Qed.

(* −|a| ≤ a（Qabs_case 两支，P 已剥 Qabs：0≤a 支 Qopp 非增 ＋ 0 桥；      *)
(*   a≤0 支 Qopp_involutive 归 Qeq；全程零 rewrite） *)
Lemma dbi_q_opp_abs_le : forall a : Q, Qle (Qopp (Qabs a)) a.
Proof.
  intros a.
  apply (Qabs_case a (fun t => Qle (Qopp t) a)).
  - intros H0a.
    apply (Qle_trans (Qopp a) 0%Q a).
    + apply (Qopp_le_compat 0%Q a). exact H0a.
    + exact H0a.
  - intros Hb0.
    apply qeq_le. apply Qopp_involutive.
Qed.

(* ============================================================ *)
(* 2. 误差换形辅助：斜率乘序交换（h·a ↔ a·h）在增量误差形的          *)
(*    real_eq 换形——方向一与总形接驳共用的唯一非定义换形。           *)
(* ============================================================ *)
Lemma dbi_err_eq_comm :
  forall (f : forall x : Real, real_lt real_zero x -> Real)
         (x a : Real) (Hx : real_lt real_zero x) (h : Real)
         (Hxh : real_lt real_zero (real_plus x h)),
  real_eq (real_abs (real_plus (f (real_plus x h) Hxh)
             (real_opp (real_plus (f x Hx) (real_mult h a)))))
          (real_abs (real_plus (f (real_plus x h) Hxh)
             (real_opp (real_plus (f x Hx) (real_mult a h))))).
Proof.
  intros f x a Hx h Hxh.
  apply real_abs_eq_compat.
  apply (RealSetoid.real_eq_plus_compat (f (real_plus x h) Hxh)
           (real_opp (real_plus (f x Hx) (real_mult h a)))
           (f (real_plus x h) Hxh)
           (real_opp (real_plus (f x Hx) (real_mult a h)))).
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (f x Hx) (real_mult h a))
             (real_plus (f x Hx) (real_mult a h))).
    apply (RealSetoid.real_eq_plus_compat (f x Hx) (real_mult h a)
             (f x Hx) (real_mult a h)).
    + apply real_eq_refl.
    + apply (real_mult_comm h a).
Qed.

(* ============================================================ *)
(* 3. 方向一（记录 → 增量供给）：RealDifferentiable 的 rdf_correct   *)
(*    于点 x 的实例即 HasIncrPos 本体——斜率取 rdf x Hx，delta 直取； *)
(*    唯一会计＝h·a ↔ a·h 乘序换形（dbi_err_eq_comm + real_le_eq_l）。*)
(* ============================================================ *)
Theorem dbi_realdiff_hasincrpos :
  forall (f : forall x : Real, real_lt real_zero x -> Real)
         (Hf : RealDifferentiable f) (x : Real) (Hx : real_lt real_zero x),
  HasIncrPos f x (rdf f Hf x Hx) Hx.
Proof.
  intros f Hf x Hx eps Heps.
  destruct (rdf_correct f Hf x Hx eps Heps) as [delta [Hd Hstep]].
  exists delta. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_eq_l
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx)
                   (real_mult h (rdf f Hf x Hx))))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx)
                   (real_mult (rdf f Hf x Hx) h)))))).
    + exact (dbi_err_eq_comm f x (rdf f Hf x Hx) Hx h Hxh).
    + exact (Hstep h Hh Hxh eps' Heps').
Qed.

(* ============================================================ *)
(* 4. 方向二（增量供给 → 记录构造）：逐点 sigT 供给经 projT1 投影     *)
(*    成斜率函数（Set 层合法选择，非经典）；rdf_correct 槽由供给的    *)
(*    HasIncrPos 实例直填。                                           *)
(* ============================================================ *)
Theorem dbi_hasincrpos_realdiff :
  forall (f : forall x : Real, real_lt real_zero x -> Real),
  (forall (x : Real) (Hx : real_lt real_zero x),
     sigT (fun a : Real => HasIncrPos f x a Hx)) ->
  RealDifferentiable f.
Proof.
  intros f Hsup.
  exists (fun x Hx => projT1 (Hsup x Hx)).
  cbv beta.
  intros x Hx eps Heps.
  destruct (Hsup x Hx) as [a Ha].
  destruct (Ha eps Heps) as [delta [Hd Hstep]].
  exists delta. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_eq_l
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx) (real_mult a h)))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                (real_opp (real_plus (f x Hx) (real_mult h a)))))).
    + apply real_eq_sym. exact (dbi_err_eq_comm f x a Hx h Hxh).
    + exact (Hstep h Hh Hxh eps' Heps').
Qed.

(* ============================================================ *)
(* 5. 域核算小件：半点域界（δ 取 x/2 保 x+h 正的逐点会计）            *)
(* ============================================================ *)
Lemma dbi_halfx_pos : forall x : Real,
  real_lt real_zero x ->
  real_lt real_zero (real_mult (real_const (1#2)) x).
Proof.
  intros x Hx. apply (abl9_qscale_pos (1#2) x).
  - unfold Qlt. simpl. lia.
  - exact Hx.
Qed.

(* |h| < x/2 且 0 < x ⟹ 0 < x + h（逐点 Q 账：严支 e0 < 半·x_n−|h_n|  *)
(*   原项直通（QltT→Qlt→Qlt_le_trans），字面弱链以 qeq_le 桥装配：      *)
(*   Mn−An ≤ 半·x_n−|h_n| ≤ x_n−|h_n| ≤ x_n+h_n == 右端投影差）         *)
Lemma dbi_abs_lt_half_add_pos : forall (x h : Real),
  real_lt real_zero x ->
  real_lt (real_abs h) (real_mult (real_const (1#2)) x) ->
  real_lt real_zero (real_plus x h).
Proof.
  intros x h Hx Hhl.
  destruct Hhl as [e0 [He0 [N0 HN0]]].
  destruct Hx as [ex [Hex [Nx HNx]]].
  exists e0. split.
  - exact He0.
  - exists (Nat.max N0 Nx). intros n Hn.
    assert (Hn0 : NatLe N0 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 Nx).
      - apply Nat.le_max_l.
      - apply (NatLe_drop _ _ Hn). }
    assert (Hnx : NatLe Nx n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N0 Nx).
      - apply Nat.le_max_r.
      - apply (NatLe_drop _ _ Hn). }
    (* 投影恒等四件 *)
    assert (Hz : projT1 real_zero n == 0%Q) by (cbn [projT1]; reflexivity).
    assert (Hplus : projT1 (real_plus x h) n == (projT1 x n + projT1 h n)%Q)
      by (apply real_plus_proj).
    assert (Habs : projT1 (real_abs h) n == Qabs (projT1 h n))
      by (apply real_abs_proj).
    assert (Hmul : projT1 (real_mult (real_const (1#2)) x) n
                   == ((1#2) * projT1 x n)%Q).
    { rewrite (real_mult_proj (real_const (1#2)) x n).
      rewrite (real_const_proj (1#2) n). reflexivity. }
    (* Q 账：0 < ex ≤ x_n−0 == x_n 与 0 < 半·x_n ≤ x_n 与 −|h_n| ≤ h_n *)
    assert (Hexlt : Qlt 0 ex) by (apply QltT_to_Qlt; exact Hex).
    assert (Hsub : (projT1 x n - projT1 real_zero n == projT1 x n)%Q)
      by (rewrite Hz; ring).
    assert (Hxnlt0 : Qlt 0 (projT1 x n)).
    { apply (Qlt_le_trans 0%Q ex).
      - exact Hexlt.
      - apply (Qle_trans ex (projT1 x n - projT1 real_zero n)%Q (projT1 x n)).
        + exact (Qlt_le_weak ex (projT1 x n - projT1 real_zero n)%Q
                   (QltT_to_Qlt ex (projT1 x n - projT1 real_zero n)%Q
                      (HNx n Hnx))).
        + apply qeq_le. exact Hsub. }
    assert (Hhalf0 : Qlt 0 ((1#2) * projT1 x n)%Q).
    { apply (Qmult_lt_0_compat (1#2) (projT1 x n)).
      - unfold Qlt. simpl. lia.
      - exact Hxnlt0. }
    assert (Hhalfle : Qle ((1#2) * projT1 x n) (projT1 x n)).
    { assert (Hsplit : ((1#2) * projT1 x n + (1#2) * projT1 x n
                        == projT1 x n)%Q) by ring.
      assert (H1 : Qle (0 + (1#2) * projT1 x n)%Q
                       ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q).
      { apply (Qplus_le_compat 0%Q ((1#2) * projT1 x n)%Q
                               ((1#2) * projT1 x n)%Q ((1#2) * projT1 x n)%Q).
        - apply (Qlt_le_weak 0%Q). exact Hhalf0.
        - apply Qle_refl. }
      apply (Qle_trans ((1#2) * projT1 x n)
              ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q (projT1 x n)).
      - apply (Qle_trans ((1#2) * projT1 x n) (0 + (1#2) * projT1 x n)%Q
                 ((1#2) * projT1 x n + (1#2) * projT1 x n)%Q).
        + apply qeq_le. ring.
        + exact H1.
      - apply qeq_le. exact Hsplit. }
    assert (Hneg : Qle (Qopp (Qabs (projT1 h n))) (projT1 h n))
      by (apply dbi_q_opp_abs_le).
    (* 字面弱链装配（四步三桥） *)
    assert (Heq1 : (projT1 (real_mult (real_const (1#2)) x) n
                    - projT1 (real_abs h) n
                    == ((1#2) * projT1 x n - Qabs (projT1 h n)))%Q).
    { rewrite Hmul. rewrite Habs. reflexivity. }
    assert (Hb1 : Qle (projT1 (real_mult (real_const (1#2)) x) n
                       - projT1 (real_abs h) n)%Q
                      ((1#2) * projT1 x n - Qabs (projT1 h n))%Q)
      by (apply qeq_le; exact Heq1).
    assert (Hleg1 : Qle ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
                         (projT1 x n - Qabs (projT1 h n))%Q).
    { apply (dbi_qplus_le_r ((1#2) * projT1 x n) (projT1 x n)
                            (Qopp (Qabs (projT1 h n)))).
      exact Hhalfle. }
    assert (Hleg2 : Qle (projT1 x n - Qabs (projT1 h n))%Q
                         (projT1 x n + projT1 h n)).
    { apply (dbi_qplus_le_l (Qopp (Qabs (projT1 h n))) (projT1 h n)
                            (projT1 x n)).
      exact Hneg. }
    assert (Hrhs : (projT1 (real_plus x h) n - projT1 real_zero n
                    == projT1 x n + projT1 h n)%Q)
      by (rewrite Hplus; rewrite Hz; ring).
    assert (Hb2 : Qle (projT1 x n + projT1 h n)
                      (projT1 (real_plus x h) n - projT1 real_zero n)%Q)
      by (apply qeq_le; apply Qeq_sym; exact Hrhs).
    (* 严支原项直通 ＋ 弱链合流 *)
    apply Qlt_to_QltT.
    apply (Qlt_le_trans e0 (projT1 (real_mult (real_const (1#2)) x) n
                              - projT1 (real_abs h) n)%Q).
    + exact (QltT_to_Qlt e0
               (projT1 (real_mult (real_const (1#2)) x) n
                - projT1 (real_abs h) n)%Q (HN0 n Hn0)).
    + exact (Qle_trans
               (projT1 (real_mult (real_const (1#2)) x) n
                - projT1 (real_abs h) n)%Q
               ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
               (projT1 (real_plus x h) n - projT1 real_zero n)%Q
               Hb1
               (Qle_trans
                  ((1#2) * projT1 x n - Qabs (projT1 h n))%Q
                  (projT1 x n - Qabs (projT1 h n))%Q
                  (projT1 (real_plus x h) n - projT1 real_zero n)%Q
                  Hleg1
                  (Qle_trans
                     (projT1 x n - Qabs (projT1 h n))%Q
                     (projT1 x n + projT1 h n)
                     (projT1 (real_plus x h) n - projT1 real_zero n)%Q
                     Hleg2 Hb2))).
Qed.

(* ============================================================ *)
(* 6. 总函数面 ↔ 带前提面接驳                                        *)
(*    6a. HasIncr ⟹ HasIncrPos（总化函数）：Hxh 槽弃用直通。          *)
(* ============================================================ *)
Lemma dbi_hasincr_incrpos :
  forall (f : Real -> Real) (x a : Real) (Hx : real_lt real_zero x),
  HasIncr f x a ->
  HasIncrPos (fun (y : Real) (_ : real_lt real_zero y) => f y) x a Hx.
Proof.
  intros f x a Hx H eps Heps.
  destruct (H eps Heps) as [d [Hd Hstep]].
  exists d. split.
  - exact Hd.
  - intros h Hh Hxh eps' Heps'.
    exact (Hstep h Hh eps' Heps').
Qed.

(* 6b. HasIncrPos（总化函数）⟹ HasIncr：δ 取 real_min δ₀ (x/2)——     *)
(*     |h|<x/2 保 x+h 正（域核算），x/2 由 dbi_halfx_pos +            *)
(*     dbi_abs_lt_half_add_pos 承担。                                  *)
Lemma dbi_incrpos_hasincr :
  forall (f : Real -> Real) (x a : Real) (Hx : real_lt real_zero x),
  HasIncrPos (fun (y : Real) (_ : real_lt real_zero y) => f y) x a Hx ->
  HasIncr f x a.
Proof.
  intros f x a Hx H eps Heps.
  destruct (H eps Heps) as [d0 [Hd0 Hstep0]].
  assert (Hhx : real_lt real_zero (real_mult (real_const (1#2)) x))
    by (apply dbi_halfx_pos; exact Hx).
  exists (real_min d0 (real_mult (real_const (1#2)) x)). split.
  - apply real_min_pos.
    + exact Hd0.
    + exact Hhx.
  - intros h Hh eps' Heps'.
    assert (Hhd0 : real_lt (real_abs h) d0).
    { apply (abl9_min_lt_l d0 (real_mult (real_const (1#2)) x) (real_abs h)).
      exact Hh. }
    assert (Hhhalf : real_lt (real_abs h) (real_mult (real_const (1#2)) x)).
    { apply (abl9_min_lt_r d0 (real_mult (real_const (1#2)) x) (real_abs h)).
      exact Hh. }
    assert (Hxh : real_lt real_zero (real_plus x h))
      by (apply (dbi_abs_lt_half_add_pos x h Hx); exact Hhhalf).
    exact (Hstep0 h Hhd0 Hxh eps' Heps').
Qed.

(* ============================================================ *)
(* 7. 两端到端组合（正域逐点增量供给 ⟺ 正域化记录）                   *)
(* ============================================================ *)
Theorem dbi_realdiff_hasincr :
  forall (f : Real -> Real)
         (Hf : RealDifferentiable (fun (y : Real) (_ : real_lt real_zero y) => f y))
         (x : Real),
  real_lt real_zero x ->
  sigT (fun a : Real => HasIncr f x a).
Proof.
  intros f Hf x Hx.
  exists (rdf (fun (y : Real) (_ : real_lt real_zero y) => f y) Hf x Hx).
  apply (dbi_incrpos_hasincr f x _ Hx).
  apply (dbi_realdiff_hasincrpos
           (fun (y : Real) (_ : real_lt real_zero y) => f y) Hf x Hx).
Qed.

Theorem dbi_hasincr_realdiff :
  forall (f : Real -> Real),
  (forall (x : Real), real_lt real_zero x ->
     sigT (fun a : Real => HasIncr f x a)) ->
  RealDifferentiable (fun (y : Real) (_ : real_lt real_zero y) => f y).
Proof.
  intros f Hsup.
  apply (dbi_hasincrpos_realdiff
           (fun (y : Real) (_ : real_lt real_zero y) => f y)).
  intros x Hx.
  destruct (Hsup x Hx) as [a Ha].
  exists a. exact (dbi_hasincr_incrpos f x a Hx Ha).
Qed.

(* ============================================================ *)
(* 终验 · 承认面（对账三联：定理名清单 12 = Qed 计数 12 = PA 语句 12） *)
(* ============================================================ *)
Print Assumptions dbi_qplus_le_r.
Print Assumptions dbi_qplus_le_l.
Print Assumptions dbi_q_opp_abs_le.
Print Assumptions dbi_err_eq_comm.
Print Assumptions dbi_realdiff_hasincrpos.
Print Assumptions dbi_hasincrpos_realdiff.
Print Assumptions dbi_halfx_pos.
Print Assumptions dbi_abs_lt_half_add_pos.
Print Assumptions dbi_hasincr_incrpos.
Print Assumptions dbi_incrpos_hasincr.
Print Assumptions dbi_realdiff_hasincr.
Print Assumptions dbi_hasincr_realdiff.
