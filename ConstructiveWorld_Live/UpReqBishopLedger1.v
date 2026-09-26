(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(*   1) rb_le_b_mult_r：<=_B 右乘保序（Bishop 组合器家族增员）            *)
(*   2) rb_valid_up：klc 向上谱系（使用 klc_closed_powb_mono）            *)
(* 使用已云认证 .vo（库树只读禁改）；路线全为机检非猜想。                 *)
(* 红线自检：零公理/零承认件/零经典逻辑/语句面全 Set 层（real_le_b/     *)
(*   real_lt/real_le/NatLe 均本项目 Set 版，Or := A + B）/Real 层零序分支  *)
(*   （real_le 0 c 的两支为 Set-sum 构造消去，非经典分裂）/可提取。       *)
(* ============================================================ *)

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
Require Import R2BishopLogSel.

Open Scope nat_scope.

(* ============================================================ *)
(* Part A：rb_le_b_mult_r —— <=_B 右乘保序                               *)
(*   前件 real_le 0 c（Set-sum）两支：                                    *)
(*   strict 支：证人 e' := eps·inv(c)（正性由 real_mult_positive 链），   *)
(*     real_mult_lt_compat 右乘 + rb_mult_plus_distr_r 分配 +            *)
(*     klst_r_pqx_eq_q（c·(eps·cinv)==eps 经 real_mult_comm 回环）换形。  *)
(*   eq 支：c==0 两侧归零（real_eq_mult_compat + rb_mult_zero_r），       *)
(*     0 < y·c+eps 由 real_eq_lt_lt 沿 y·c==0 运输 real_lt_plus_r_zero。  *)
(* ============================================================ *)

Lemma rb_le_b_mult_r : forall (x y c : Real),
  real_le_b x y -> real_le real_zero c ->
  real_le_b (real_mult x c) (real_mult y c).
Proof.
  intros x y c Hxy Hc.
  unfold real_le_b in Hxy. unfold real_le_b.
  intros eps Heps.
  destruct Hc as [Hcpos | Hceq].
  - (* strict 支：0 < c *)
    assert (Hcinvpos : real_lt real_zero (real_inv_pos c Hcpos))
      by exact (real_inv_pos_pos c Hcpos).
    assert (Hepos : real_lt real_zero
             (real_mult eps (real_inv_pos c Hcpos)))
      by exact (real_mult_positive eps (real_inv_pos c Hcpos) Heps Hcinvpos).
    pose proof (Hxy (real_mult eps (real_inv_pos c Hcpos)) Hepos) as Hlt.
    assert (Hmeps : real_eq
             (real_mult (real_mult eps (real_inv_pos c Hcpos)) c) eps).
    { apply (real_eq_trans
              (real_mult (real_mult eps (real_inv_pos c Hcpos)) c)
              (real_mult c (real_mult eps (real_inv_pos c Hcpos))) eps).
      - apply real_mult_comm.
      - exact (klst_r_pqx_eq_q c eps Hcpos). }
    apply (real_lt_eq_lt
            (real_mult x c)
            (real_plus (real_mult y c)
              (real_mult (real_mult eps (real_inv_pos c Hcpos)) c))
            (real_plus (real_mult y c) eps)).
    + apply (real_lt_eq_lt
              (real_mult x c)
              (real_mult (real_plus y (real_mult eps (real_inv_pos c Hcpos))) c)
              (real_plus (real_mult y c)
                (real_mult (real_mult eps (real_inv_pos c Hcpos)) c))).
      * apply (real_mult_lt_compat
                 x (real_plus y (real_mult eps (real_inv_pos c Hcpos))) c
                 Hlt Hcpos).
      * exact (rb_mult_plus_distr_r y (real_mult eps (real_inv_pos c Hcpos)) c).
    + apply (RealSetoid.real_eq_plus_compat (real_mult y c)
              (real_mult (real_mult eps (real_inv_pos c Hcpos)) c)
              (real_mult y c) eps).
      * apply real_eq_refl.
      * exact Hmeps.
  - (* eq 支：c == 0 *)
    assert (Hxz : real_eq (real_mult x c) real_zero).
    { apply (real_eq_trans (real_mult x c) (real_mult x real_zero) real_zero).
      - exact (RealSetoid.real_eq_mult_compat x c x real_zero (real_eq_refl x)
                (real_eq_sym real_zero c Hceq)).
      - exact (rb_mult_zero_r x). }
    assert (Hyz : real_eq (real_mult y c) real_zero).
    { apply (real_eq_trans (real_mult y c) (real_mult y real_zero) real_zero).
      - exact (RealSetoid.real_eq_mult_compat y c y real_zero (real_eq_refl y)
                (real_eq_sym real_zero c Hceq)).
      - exact (rb_mult_zero_r y). }
    assert (Hple : real_lt real_zero (real_plus (real_mult y c) eps)).
    { apply (real_eq_lt_lt real_zero (real_mult y c)
              (real_plus (real_mult y c) eps)).
      - apply real_eq_sym. exact Hyz.
      - exact (real_lt_plus_r_zero (real_mult y c) eps Heps). }
    apply (real_eq_lt_lt (real_mult x c) real_zero
            (real_plus (real_mult y c) eps)).
    + exact Hxz.
    + exact Hple.
Qed.

(* ============================================================ *)
(* Part B：rb_valid_up —— klc 向上谱系（有效站向上闭合）                  *)
(*   klc_closed_powb_mono 给 (1-k)^{j''} <=_B (1-k)^j（0<=k<=1 全域，     *)
(*   免序判定），rb_le_b_mult_r 右乘 TV0 后 real_le_b_trans 串联有效站。  *)
(* ============================================================ *)

Definition rb_valid_at (kappa TV0 budget : Real) (k : nat) : Set :=
  real_le_b (rb_gval kappa TV0 k) budget.

Lemma rb_valid_up : forall (kappa TV0 budget : Real) (j j'' : nat),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  NatLe j j'' -> real_le real_zero TV0 ->
  rb_valid_at kappa TV0 budget j -> rb_valid_at kappa TV0 budget j''.
Proof.
  intros kappa TV0 budget j j'' Hk0 Hk1 Hjj HTV0 Hvalid.
  unfold rb_valid_at in Hvalid |- *.
  pose proof (klc_closed_powb_mono kappa j j'' (inl Hk0) (inl Hk1) Hjj) as Hmono.
  exact (real_le_b_trans (rb_gval kappa TV0 j'') (rb_gval kappa TV0 j) budget
          (rb_le_b_mult_r (powb_pow (rb_delta0 kappa) j'')
                          (powb_pow (rb_delta0 kappa) j) TV0 Hmono HTV0)
          Hvalid).
Qed.

(* G3 提取检验：终末构造面 Separate Extraction，Obj.magic 计数=0 为绿 *)
Separate Extraction rb_valid_up rb_le_b_mult_r.
