(* ==========================================================================)
   abl_arctan_smallincr_15.v — arctan 小增量精化件（9a-甲）
   使命: 闭域（逐点 |g_n| ≤ 1）：|arctan(g) − g| ≤ eps·|g| + eps'，delta 以 sigT ∃delta（0<delta）形给出，与 9b 装配形态兼容。
   配方: b3rr_real_arctan_deriv_linear（S11:L5521，|x|≤r<1）取 r:=0、
     x:=real_const 0 基点实例化（基点 0 不受 r<1 卡口限制）+ b5c_arctan_const0
     （S11:L8295）零传输。
   实名勘正（对源计划的登记）：
     ① 源计划所记 real_plus_0_l/real_mult_0_l 系 Setoid 件在带内无此名：
       实名为 real_plus_zero（S02:L2348）/ real_mult_zero（S02:L2378）/
       real_mult_one（S02:L2373）/ real_plus_comm（S02:L2336）/
       real_eq_of_zero_diff（S02:L2317），本件按实名取用。
     ② S11 带内无 arctan 的 real_eq-外延件（grep arctan_wd 于 S11 零命中），
       最近邻 b5m_arctan_wd（S12:L7358）触发提取器硬限制「The informative
       inductive type prod has a Prop instance」，全锥 Recursive Extraction
       不可成件。本件处置：arctan 平移以 arctan_real_proj（S11，值只依
       projT1 逐点位）＋ b5c_arctan_partial_wd（S11:L8270）逐点自证特例，
       Require 链退回 S11 单链。
     ③ inv 证书差桥取 real_inv_pos_ext（S07:L6757）+ real_inv_one
       （S08:L3359）：b3rr 结论内嵌 h·inv(1+0·0)[b3r 证书] ≡ g 的实值传输。
     ④ 隔离池单提实录：b3rr 与 S11 锥十四件逐一 EXIT=0/magic=0；b5m_arctan_wd
       单提报 prod-Prop 错（上游只读池，不触碰）。
   依赖: S01_BaseRing–S11_TP3B5；Stdlib QArith、List、Setoid、Lia、Extraction。
   构造性: 纯构造性（全链 Qed 真构造，零承认式语句）；Set 层零 Prop 泄露
     （QleT'=Id(Qle_bool)true 形态，sigT/And/real_lt/real_le 全 Type/Set）；
     非平凡（基点实例化＋五步实值传输＋real_le 左侧传输闭合，非转发）；
     可提取（尾 Print Assumptions + Recursive Extraction，判据 Closed + Obj.magic 计 0）。
   编译配方: source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x15pool "" abl_arctan_smallincr_15.v
     （隔离池 /tmp/x15pool，92M 现势链含 S11/S12 .vo。）
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
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 主件：arctan 小增量精化（9a-甲目标）                          *)
(* ============================================================ *)
Lemma abl_atan_small_incr :
  forall (eps : Real), real_lt real_zero eps ->
  sigT (fun delta : Real => And (real_lt real_zero delta)
    (forall (g : Real), real_lt (real_abs g) delta ->
      forall (Hg : forall n : nat, QleT' (Qabs (projT1 g n)) 1),
      forall (eps' : Real), real_lt real_zero eps' ->
      real_le (real_abs (real_plus (cauchy_real_arctan g Hg) (real_opp g)))
              (real_plus (real_mult eps (real_abs g)) eps'))).
Proof.
  intros eps Heps.
  (* —— 0. 零传输预置件（全部现成 real_eq 件组装） —— *)
  assert (Hc0z : real_eq (real_const 0) real_zero).
  { apply real_eq_of_zero_diff. intro n. simpl. ring. }
  assert (Hp0l : forall x : Real, real_eq (real_plus real_zero x) x).
  { intros x. apply real_eq_of_zero_diff. intro n.
    rewrite (real_plus_proj real_zero x n). simpl. ring. }
  assert (Hzz : real_eq (real_mult (real_const 0) (real_const 0)) real_zero).
  { apply (real_eq_trans _ (real_mult real_zero real_zero)).
    - apply (RealSetoid.real_eq_mult_compat (real_const 0) real_zero (real_const 0) real_zero
                                 Hc0z Hc0z).
    - apply real_mult_zero. }
  assert (Hone : real_eq (real_plus real_one (real_mult (real_const 0) (real_const 0)))
                         real_one).
  { apply (real_eq_trans _ (real_plus real_one real_zero)).
    - apply (RealSetoid.real_eq_plus_compat real_one (real_mult (real_const 0) (real_const 0))
                                 real_one real_zero (real_eq_refl real_one) Hzz).
    - apply real_plus_zero. }
  assert (Hinv : real_eq (real_inv_pos (real_plus real_one
                                          (real_mult (real_const 0) (real_const 0)))
                                        (b3r_one_sq_real_pos (real_const 0)))
                         real_one).
  { apply (real_eq_trans _ (real_inv_pos real_one real_lt_zero_one)).
    - apply (real_inv_pos_ext _ _ (b3r_one_sq_real_pos (real_const 0))
                                 real_lt_zero_one Hone).
    - apply real_inv_one. }
  assert (Hgz : forall g : Real,
    real_eq (real_mult g (real_inv_pos (real_plus real_one
                                         (real_mult (real_const 0) (real_const 0)))
                                       (b3r_one_sq_real_pos (real_const 0)))) g).
  { intros g. apply (real_eq_trans _ (real_mult g real_one)).
    - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | exact Hinv].
    - apply real_mult_one. }
  (* —— 1. b3rr 主件基点实例化：r := 0、x := real_const 0 —— *)
  assert (Hxb0 : forall n : nat, QleT' (Qabs (projT1 (real_const 0) n)) 0).
  { intro n. apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs 0)).
    - apply qeq_imp_qle. rewrite (real_const_proj 0 n). reflexivity.
    - unfold Qle. simpl. lia. }
  assert (Hr01 : Qlt 0 1) by (unfold Qlt; simpl; lia).
  destruct (b3rr_real_arctan_deriv_linear 0 (Qle_refl 0) Hr01 (real_const 0) Hxb0
             eps Heps) as [delta [Hdpos Hstep]].
  exists delta. split.
  - exact Hdpos.
  - intros g Hglt Hg eps' Heps'.
    (* —— 2. 基点左零：0+g ≡ g 实值与逐点域证书传输 —— *)
    assert (Hp0g : real_eq (real_plus (real_const 0) g) g).
    { apply real_eq_of_zero_diff. intro n.
      rewrite (real_plus_proj (real_const 0) g n).
      rewrite (real_const_proj 0 n).
      ring. }
    assert (Hdom : forall n : nat, QleT' (Qabs (projT1 (real_plus (real_const 0) g) n)) 1).
    { intro n. apply Qle_to_QleT'.
      apply (Qle_trans _ (Qabs (projT1 g n))).
      - apply qeq_imp_qle.
        rewrite (real_plus_proj (real_const 0) g n).
        rewrite (real_const_proj 0 n).
        rewrite Qplus_0_l. reflexivity.
      - exact (QleT'_to_Qle _ _ (Hg n)). }
    specialize (Hstep g Hglt Hdom eps' Heps').
    (* —— 3. 误差实值传输：b3rr 结论 LHS ≡ |arctan(g) − g| —— *)
    assert (Hshift : real_eq (cauchy_real_arctan (real_plus (real_const 0) g) Hdom)
                             (cauchy_real_arctan g Hg)).
      { (* 逐点自证：arctan 值只依 projT1 逐点位（arctan_real_proj），
         0+g 与 g 逐点 Qeq（Hp0g 同款点位链），部分和 wd 闭合。 *)
      apply real_eq_of_zero_diff. intro n.
      rewrite (arctan_real_proj _ Hdom n).
      rewrite (arctan_real_proj _ Hg n).
      assert (Hpt : projT1 (real_plus (real_const 0) g) n == projT1 g n).
      { rewrite (real_plus_proj (real_const 0) g n).
        rewrite (real_const_proj 0 n).
        rewrite Qplus_0_l. reflexivity. }
      apply (b5c_arctan_partial_wd n) in Hpt.
      rewrite Hpt. ring. }
    assert (Hat0 : real_eq (cauchy_real_arctan (real_const 0)
                                 (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
                           real_zero).
    { apply (b5c_arctan_const0 (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01)). }
    assert (Hinner : real_eq (real_plus
                                (cauchy_real_arctan (real_const 0)
                                   (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
                                (real_mult g (real_inv_pos
                                   (real_plus real_one
                                      (real_mult (real_const 0) (real_const 0)))
                                   (b3r_one_sq_real_pos (real_const 0)))))
                             g).
    { apply (real_eq_trans _ (real_plus real_zero g)).
      - apply RealSetoid.real_eq_plus_compat; [exact Hat0 | apply (Hgz g)].
      - apply (Hp0l g). }
    assert (HAeq : real_eq
      (real_abs (real_plus
        (cauchy_real_arctan (real_plus (real_const 0) g) Hdom)
        (real_opp (real_plus
          (cauchy_real_arctan (real_const 0) (b3rr_dom_r1 (real_const 0) 0 Hxb0 Hr01))
          (real_mult g (real_inv_pos
             (real_plus real_one (real_mult (real_const 0) (real_const 0)))
             (b3r_one_sq_real_pos (real_const 0))))))))
      (real_abs (real_plus (cauchy_real_arctan g Hg) (real_opp g)))).
    { apply real_abs_eq_compat.
      apply (RealSetoid.real_eq_plus_compat _ _ _ _ Hshift).
      apply (RealSetoid.real_eq_opp_compat _ _ Hinner). }
    (* —— 4. real_le 左侧传输闭合 —— *)
    eapply real_le_eq_l.
    + apply real_eq_sym. exact HAeq.
    + exact Hstep.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                       *)
(*   对账三联：定理名清单 1 = Qed 计数 1 = PA 语句 1，零差。       *)
(* ============================================================ *)
Print Assumptions abl_atan_small_incr.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl_atan_small_incr.
