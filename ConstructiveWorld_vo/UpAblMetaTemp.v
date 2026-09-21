(* UpAblMetaTemp.v —— M2R 席：亚稳标度线·上界侧打包主件
   温度-δ* 链（件①）与 温度-模量发散定理（件②·见证形），mtp_ 前缀，裸 Real 层。
   零承认件：本文件无任何承认式声明，全部构造性证明，Set 层见证（sigT/And）。
   承重消费件（Require 直用，零重造）：
     UpAblMetaEngine：mte_nat_to_R / mte_rpow / mte_nat_const_eq /
       mte_nat_to_R_S_pos / mte_lt_plus_one / mte_exp_pow_iter / mte_exp_divergence
     S03：real_inv_pos / real_inv_pos_correct / real_inv_pos_pos
     S07：cauchy_real_exp 族（pos/zero/plus/wd/gt_one/mono）+ real_arch
   布景：Δ>0 能障、V=TV₀ 初值整体变差、b=budget 预算、T>0 温度。
     lo(T)  := e^(−Δ/T)          （exp_neg 语义）
     δ*(T)  := lo(T)·lo(T) = e^(−2Δ/T)
     anchor(T) := V·inv(δ*(T)·b)  （mix_pow_budget 式混合模量锚值·实量形）
   主件（温度趋零发散·显式模量）：∀M:nat, ∃T₀>0, ∀T∈(0,T₀), M < anchor(T)。
   路线（任务书骨架 rigorous 化，代数排布修正见交付报告）：
     T<T₀ ⟹ inv T₀ < inv T ⟹ 2Δ/T₀ < 2Δ/T ⟹ E₀:=e^{2Δ/T₀} < E(T):=e^{2Δ/T}；
     选 T₀ := inv(n̄_{S N}) 使 w·invV < E₀（real_arch 选 n₀、mte_exp_divergence
     于 a2=Δ+Δ 选 N，w := M·b）；δ*(T)=inv(E(T)) < inv(E₀) ⟹ w·inv(E(T)) <
     w·inv(E₀) < V ⟹ M·(δ*(T)·b) < V ⟹ M < anchor(T)。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpAblMetaEngine.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ---------- 帮件：逆元唯一性与倒数反序 ---------- *)

(* 逆元唯一性：x·u == 1 ⟹ u == inv(x)（纯等式代数） *)
Lemma mtp_inv_unique : forall (x : Real) (Hx : real_lt real_zero x) (u : Real),
  real_eq (real_mult x u) real_one -> real_eq u (real_inv_pos x Hx).
Proof.
  intros x Hx u Hu.
  apply (real_eq_trans u (real_mult real_one (real_inv_pos x Hx)) (real_inv_pos x Hx)).
  - (* u == 壹·inv x *)
    apply (real_eq_trans _ (real_mult u real_one)).
    + exact (real_eq_sym (real_mult u real_one) u (real_mult_one u)).
    + apply (real_eq_trans _ (real_mult u (real_mult x (real_inv_pos x Hx)))).
      * exact (RealSetoid.real_eq_mult_compat u real_one u
                 (real_mult x (real_inv_pos x Hx))
                 (real_eq_refl u)
                 (real_eq_sym (real_mult x (real_inv_pos x Hx)) real_one
                    (real_inv_pos_correct x Hx))).
      * apply (real_eq_trans _
                 (real_mult (real_mult u x) (real_inv_pos x Hx))).
        -- exact (real_mult_assoc u x (real_inv_pos x Hx)).
        -- apply (real_eq_trans _
                     (real_mult (real_mult x u) (real_inv_pos x Hx))).
           ++ exact (RealSetoid.real_eq_mult_compat (real_mult u x)
                        (real_inv_pos x Hx) (real_mult x u) (real_inv_pos x Hx)
                        (real_mult_comm u x) (real_eq_refl (real_inv_pos x Hx))).
           ++ exact (RealSetoid.real_eq_mult_compat (real_mult x u)
                        (real_inv_pos x Hx) real_one (real_inv_pos x Hx)
                        Hu (real_eq_refl (real_inv_pos x Hx))).
  - (* 壹·inv x == inv x *)
    apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) real_one)).
    + exact (real_mult_comm real_one (real_inv_pos x Hx)).
    + exact (real_mult_one (real_inv_pos x Hx)).
Qed.

(* 双逆：inv(inv x) == x *)
Lemma mtp_inv_inv : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_inv_pos (real_inv_pos x Hx) (real_inv_pos_pos x Hx)) x.
Proof.
  intros x Hx.
  exact (real_eq_sym x
           (real_inv_pos (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
           (mtp_inv_unique (real_inv_pos x Hx) (real_inv_pos_pos x Hx) x
              (real_eq_trans (real_mult (real_inv_pos x Hx) x)
                             (real_mult x (real_inv_pos x Hx)) real_one
                             (real_mult_comm (real_inv_pos x Hx) x)
                             (real_inv_pos_correct x Hx)))).
Qed.

(* 倒数反序：0<T<T₀ ⟹ inv T₀ < inv T *)
Lemma mtp_inv_antitone : forall (T T0 : Real) (HT : real_lt real_zero T)
    (HT0 : real_lt real_zero T0),
  real_lt T T0 -> real_lt (real_inv_pos T0 HT0) (real_inv_pos T HT).
Proof.
  intros T T0 HT HT0 Hlt.
  assert (HinvT : real_lt real_zero (real_inv_pos T HT))
    by exact (real_inv_pos_pos T HT).
  assert (HinvT0 : real_lt real_zero (real_inv_pos T0 HT0))
    by exact (real_inv_pos_pos T0 HT0).
  assert (H1 : real_lt (real_mult T (real_inv_pos T0 HT0))
                       (real_mult T0 (real_inv_pos T0 HT0)))
    by (exact (real_mult_lt_compat T T0 (real_inv_pos T0 HT0) Hlt HinvT0)).
  assert (H2 : real_lt (real_mult T (real_inv_pos T0 HT0)) real_one)
    by (exact (real_lt_eq_lt (real_mult T (real_inv_pos T0 HT0))
                 (real_mult T0 (real_inv_pos T0 HT0)) real_one H1
                 (real_inv_pos_correct T0 HT0))).
  (* inv T₀ == (T·inv T₀)·inv T *)
  assert (E2 : real_eq (real_inv_pos T0 HT0)
                 (real_mult (real_mult T (real_inv_pos T0 HT0))
                            (real_inv_pos T HT))).
  { apply (real_eq_trans _ (real_mult (real_inv_pos T0 HT0) real_one)).
    - exact (real_eq_sym (real_mult (real_inv_pos T0 HT0) real_one)
               (real_inv_pos T0 HT0) (real_mult_one (real_inv_pos T0 HT0))).
    - apply (real_eq_trans _
               (real_mult (real_inv_pos T0 HT0)
                          (real_mult T (real_inv_pos T HT)))).
      + exact (RealSetoid.real_eq_mult_compat (real_inv_pos T0 HT0) real_one
                 (real_inv_pos T0 HT0) (real_mult T (real_inv_pos T HT))
                 (real_eq_refl (real_inv_pos T0 HT0))
                 (real_eq_sym (real_mult T (real_inv_pos T HT)) real_one
                    (real_inv_pos_correct T HT))).
      + apply (real_eq_trans _
                 (real_mult (real_mult (real_inv_pos T0 HT0) T)
                            (real_inv_pos T HT))).
        * exact (real_mult_assoc (real_inv_pos T0 HT0) T (real_inv_pos T HT)).
        * exact (RealSetoid.real_eq_mult_compat
                   (real_mult (real_inv_pos T0 HT0) T) (real_inv_pos T HT)
                   (real_mult T (real_inv_pos T0 HT0)) (real_inv_pos T HT)
                   (real_mult_comm (real_inv_pos T0 HT0) T)
                   (real_eq_refl (real_inv_pos T HT))).
  }
  apply (real_lt_eq_lt (real_inv_pos T0 HT0)
           (real_mult real_one (real_inv_pos T HT))).
  - exact (real_eq_lt_lt (real_inv_pos T0 HT0)
             (real_mult (real_mult T (real_inv_pos T0 HT0)) (real_inv_pos T HT))
             (real_mult real_one (real_inv_pos T HT)) E2
             (real_mult_lt_compat (real_mult T (real_inv_pos T0 HT0)) real_one
                (real_inv_pos T HT) H2 HinvT)).
  - apply (real_eq_trans _ (real_mult (real_inv_pos T HT) real_one)).
    + exact (real_mult_comm real_one (real_inv_pos T HT)).
    + exact (real_mult_one (real_inv_pos T HT)).
Qed.

(* 乘倒数扳手·前向：0<w, u·w < v ⟹ u < v·inv(w) *)
Lemma mtp_mult_inv_fwd : forall (u v w : Real) (Hw : real_lt real_zero w),
  real_lt (real_mult u w) v -> real_lt u (real_mult v (real_inv_pos w Hw)).
Proof.
  intros u v w Hw Hlt.
  assert (Hinv : real_lt real_zero (real_inv_pos w Hw))
    by exact (real_inv_pos_pos w Hw).
  apply (real_eq_lt_lt u
           (real_mult (real_mult u w) (real_inv_pos w Hw))
           (real_mult v (real_inv_pos w Hw))).
  - exact (real_eq_sym (real_mult (real_mult u w) (real_inv_pos w Hw)) u
             (real_eq_trans (real_mult (real_mult u w) (real_inv_pos w Hw))
                (real_mult u (real_mult w (real_inv_pos w Hw))) u
                (real_eq_sym _ _ (real_mult_assoc u w (real_inv_pos w Hw)))
                (real_eq_trans (real_mult u (real_mult w (real_inv_pos w Hw)))
                   (real_mult u real_one) u
                   (RealSetoid.real_eq_mult_compat u
                      (real_mult w (real_inv_pos w Hw)) u real_one
                      (real_eq_refl u)
                      (real_inv_pos_correct w Hw))
                   (real_mult_one u)))).
  - exact (real_mult_lt_compat (real_mult u w) v (real_inv_pos w Hw) Hlt Hinv).
Qed.

(* 乘倒数扳手·后向：0<w, u < v·w ⟹ u·inv(w) < v *)
Lemma mtp_lt_inv_rw : forall (u v w : Real) (Hw : real_lt real_zero w),
  real_lt u (real_mult v w) -> real_lt (real_mult u (real_inv_pos w Hw)) v.
Proof.
  intros u v w Hw Hlt.
  assert (Hinv : real_lt real_zero (real_inv_pos w Hw))
    by exact (real_inv_pos_pos w Hw).
  apply (real_lt_eq_lt (real_mult u (real_inv_pos w Hw))
           (real_mult (real_mult v w) (real_inv_pos w Hw))).
  - exact (real_mult_lt_compat u (real_mult v w) (real_inv_pos w Hw) Hlt Hinv).
  - exact (real_eq_trans (real_mult (real_mult v w) (real_inv_pos w Hw))
             (real_mult v (real_mult w (real_inv_pos w Hw))) v
             (real_eq_sym _ _ (real_mult_assoc v w (real_inv_pos w Hw)))
             (real_eq_trans (real_mult v (real_mult w (real_inv_pos w Hw)))
                (real_mult v real_one) v
                (RealSetoid.real_eq_mult_compat v (real_mult w (real_inv_pos w Hw))
                   v real_one (real_eq_refl v)
                   (real_inv_pos_correct w Hw))
                (real_mult_one v))).
Qed.

(* ---------- 件①：温度-δ* 链 ---------- *)

(* 低玻尔兹曼因子 lo(T) := e^(−Δ/T)（exp_neg 语义 = cauchy_real_exp 于负指数） *)
Definition mtp_lo (delta T : Real) (Hd : real_lt real_zero delta)
  (HT : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (real_mult delta (real_inv_pos T HT))).

(* δ*(T) := lo(T)·lo(T) = e^(−2Δ/T) *)
Definition mtp_delta_star (delta T : Real) (Hd : real_lt real_zero delta)
  (HT : real_lt real_zero T) : Real :=
  real_mult (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT).

(* lo·e^{Δ/T} == 1（互逆恒等） *)
Lemma mtp_lo_mult_cancel : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  real_eq (real_mult (mtp_lo delta T Hd HT)
                     (cauchy_real_exp (real_mult delta (real_inv_pos T HT))))
          real_one.
Proof.
  intros delta T Hd HT.
  apply (real_eq_trans _
           (cauchy_real_exp (real_plus (real_opp (real_mult delta (real_inv_pos T HT)))
                                       (real_mult delta (real_inv_pos T HT))))).
  - exact (real_eq_sym _ _
             (cauchy_real_exp_plus (real_opp (real_mult delta (real_inv_pos T HT)))
                                   (real_mult delta (real_inv_pos T HT)))).
  - apply (real_eq_trans _ (cauchy_real_exp real_zero)).
    + apply cauchy_real_exp_wd.
      apply (real_eq_trans _
               (real_plus (real_mult delta (real_inv_pos T HT))
                          (real_opp (real_mult delta (real_inv_pos T HT))))).
      * exact (real_plus_comm (real_opp (real_mult delta (real_inv_pos T HT)))
                              (real_mult delta (real_inv_pos T HT))).
      * exact (real_plus_opp (real_mult delta (real_inv_pos T HT))).
    + exact cauchy_real_exp_zero.
Qed.

(* lo(T) > 0 *)
Lemma mtp_lo_pos : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  real_lt real_zero (mtp_lo delta T Hd HT).
Proof.
  intros delta T Hd HT. apply cauchy_real_exp_pos.
Qed.

(* δ*(T) > 0 *)
Lemma mtp_ds_pos : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  real_lt real_zero (mtp_delta_star delta T Hd HT).
Proof.
  intros delta T Hd HT. unfold mtp_delta_star.
  apply real_mult_pos_compat.
  - exact (mtp_lo_pos delta T Hd HT).
  - exact (mtp_lo_pos delta T Hd HT).
Qed.

(* lo(T) < 1（e^(−x)<1 当 x>0：M1 ②b 链反向，经 cauchy_real_exp_gt_one） *)
Lemma mtp_lo_lt_one : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  real_lt (mtp_lo delta T Hd HT) real_one.
Proof.
  intros delta T Hd HT.
  assert (Hx : real_lt real_zero (real_mult delta (real_inv_pos T HT)))
    by (exact (real_mult_pos_compat delta (real_inv_pos T HT) Hd
                 (real_inv_pos_pos T HT))).
  assert (Hb : real_lt real_one (cauchy_real_exp (real_mult delta (real_inv_pos T HT))))
    by (exact (cauchy_real_exp_gt_one (real_mult delta (real_inv_pos T HT)) Hx)).
  assert (Hlo : real_lt real_zero (mtp_lo delta T Hd HT))
    by exact (mtp_lo_pos delta T Hd HT).
  apply (real_lt_eq_lt (mtp_lo delta T Hd HT)
           (real_mult (mtp_lo delta T Hd HT)
                      (cauchy_real_exp (real_mult delta (real_inv_pos T HT))))).
  - exact (real_eq_lt_lt (mtp_lo delta T Hd HT)
             (real_mult (mtp_lo delta T Hd HT) real_one)
             (real_mult (mtp_lo delta T Hd HT)
                        (cauchy_real_exp (real_mult delta (real_inv_pos T HT))))
             (real_eq_sym (real_mult (mtp_lo delta T Hd HT) real_one)
                (mtp_lo delta T Hd HT) (real_mult_one (mtp_lo delta T Hd HT)))
             (real_mult_lt_compat_l real_one
                (cauchy_real_exp (real_mult delta (real_inv_pos T HT)))
                (mtp_lo delta T Hd HT) Hb Hlo)).
  - exact (mtp_lo_mult_cancel delta T Hd HT).
Qed.

(* δ*(T) < 1 *)
Lemma mtp_ds_lt_one : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  real_lt (mtp_delta_star delta T Hd HT) real_one.
Proof.
  intros delta T Hd HT. unfold mtp_delta_star.
  assert (Hlo1 : real_lt (mtp_lo delta T Hd HT) real_one)
    by exact (mtp_lo_lt_one delta T Hd HT).
  assert (Hlo0 : real_lt real_zero (mtp_lo delta T Hd HT))
    by exact (mtp_lo_pos delta T Hd HT).
  apply (real_lt_trans (real_mult (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT))
           (mtp_lo delta T Hd HT)).
  - apply (real_lt_eq_lt _ (real_mult real_one (mtp_lo delta T Hd HT))).
    + exact (real_mult_lt_compat (mtp_lo delta T Hd HT) real_one
               (mtp_lo delta T Hd HT) Hlo1 Hlo0).
    + exact (real_eq_trans (real_mult real_one (mtp_lo delta T Hd HT))
               (real_mult (mtp_lo delta T Hd HT) real_one)
               (mtp_lo delta T Hd HT)
               (real_mult_comm real_one (mtp_lo delta T Hd HT))
               (real_mult_one (mtp_lo delta T Hd HT))).
  - exact Hlo1.
Qed.

(* 件① 主件：0 < δ*(T) < 1（合取见证形，Set 层） *)
Theorem mtp_ds_temp : forall (delta T : Real) (Hd : real_lt real_zero delta)
    (HT : real_lt real_zero T),
  And (real_lt real_zero (mtp_delta_star delta T Hd HT))
      (real_lt (mtp_delta_star delta T Hd HT) real_one).
Proof.
  intros delta T Hd HT. split.
  - exact (mtp_ds_pos delta T Hd HT).
  - exact (mtp_ds_lt_one delta T Hd HT).
Qed.

(* ---------- 件②：温度-模量发散定理（见证形） ---------- *)

(* anchor(T) := V·inv(δ*(T)·b) —— mix_pow_budget 式混合模量锚值（实量形） *)
Definition mtp_anchor (delta V b : Real) (Hd : real_lt real_zero delta)
  (HV : real_lt real_zero V) (Hb : real_lt real_zero b)
  (T : Real) (HT : real_lt real_zero T) : Real :=
  real_mult V (real_inv_pos (real_mult (mtp_delta_star delta T Hd HT) b)
    (real_mult_pos_compat (mtp_delta_star delta T Hd HT) b
       (mtp_ds_pos delta T Hd HT) Hb)).

Theorem mtp_anchor_divergence :
  forall (delta V b : Real) (Hd : real_lt real_zero delta)
         (HV : real_lt real_zero V) (Hb : real_lt real_zero b) (M : nat),
  sigT (fun T0 => And (real_lt real_zero T0)
         (forall (T : Real) (HT : real_lt real_zero T), real_lt T T0 ->
            real_lt (mte_nat_to_R M)
                    (mtp_anchor delta V b Hd HV Hb T HT))).
Proof.
  intros delta V b Hd HV Hb M.
  (* 大指数生成元 a2 := Δ+Δ > 0 *)
  assert (Ha2 : real_lt real_zero (real_plus delta delta)).
  { exact (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
             (real_plus delta delta)
             (real_eq_sym _ _ (real_plus_zero real_zero))
             (real_lt_plus_compat real_zero delta real_zero delta Hd Hd)). }
  assert (HVinv : real_lt real_zero (real_inv_pos V HV))
    by exact (real_inv_pos_pos V HV).
  destruct M as [| M].
  - (* M = 0：anchor 恒正，任取 T₀ := 壹 *)
    exists real_one. split.
    + exact real_lt_zero_one.
    + intros T HT HT0. unfold mtp_anchor.
      apply (real_eq_lt_lt real_zero (mte_nat_to_R 0)
               (real_mult V
                  (real_inv_pos (real_mult (mtp_delta_star delta T Hd HT) b)
                     (real_mult_pos_compat (mtp_delta_star delta T Hd HT) b
                        (mtp_ds_pos delta T Hd HT) Hb)))).
      * exact (real_eq_refl real_zero).
      * exact (real_mult_pos_compat V
                  (real_inv_pos (real_mult (mtp_delta_star delta T Hd HT) b)
                     (real_mult_pos_compat (mtp_delta_star delta T Hd HT) b
                        (mtp_ds_pos delta T Hd HT) Hb))
                  HV
                  (real_inv_pos_pos (real_mult (mtp_delta_star delta T Hd HT) b)
                     (real_mult_pos_compat (mtp_delta_star delta T Hd HT) b
                        (mtp_ds_pos delta T Hd HT) Hb))).
  - (* M ≥ 1：主链 *)
    assert (HMpos : real_lt real_zero (mte_nat_to_R (Datatypes.S M)))
      by exact (mte_nat_to_R_S_pos M).
    assert (Hwpos : real_lt real_zero
                      (real_mult (mte_nat_to_R (Datatypes.S M)) b))
      by (exact (real_mult_pos_compat (mte_nat_to_R (Datatypes.S M)) b HMpos Hb)).
    (* w·invV < n̄₀（real_arch + mte_nat_const_eq 运输） *)
    destruct (real_arch (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                   (real_inv_pos V HV))) as [n0 [_ HBlt]].
    assert (HB2 : real_lt (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                (real_inv_pos V HV))
                          (mte_nat_to_R n0))
      by (exact (real_lt_eq_lt _
                   (real_const (Z.of_nat n0 # 1)%Q) _
                   HBlt
                   (real_eq_sym (mte_nat_to_R n0)
                      (real_const (Z.of_nat n0 # 1)%Q)
                      (mte_nat_const_eq n0)))).
    assert (Hnlt : real_lt (mte_nat_to_R n0) (mte_nat_to_R (Datatypes.S n0)))
      by exact (mte_lt_plus_one (mte_nat_to_R n0)).
    (* e^{a2·n̄_k} 发散：选 N 使 n̄_{S n₀} < (e^{a2})^{S N} *)
    destruct (mte_exp_divergence (real_plus delta delta) Ha2
                (Datatypes.S n0)) as [N Hpow].
    assert (Hk : Nat.le N (Datatypes.S N)) by apply Nat.le_succ_diag_r.
    assert (Hpowk : real_lt (mte_nat_to_R (Datatypes.S n0))
                            (mte_rpow (cauchy_real_exp (real_plus delta delta))
                                      (Datatypes.S N)))
      by (exact (Hpow (Datatypes.S N) Hk)).
    assert (Hkpos : real_lt real_zero (mte_nat_to_R (Datatypes.S N)))
      by exact (mte_nat_to_R_S_pos N).
    exists (real_inv_pos (mte_nat_to_R (Datatypes.S N)) Hkpos). split.
    + exact (real_inv_pos_pos (mte_nat_to_R (Datatypes.S N)) Hkpos).
    + intros T HT HT0.
      set (iT0 := real_inv_pos (real_inv_pos (mte_nat_to_R (Datatypes.S N)) Hkpos)
                  (real_inv_pos_pos (mte_nat_to_R (Datatypes.S N)) Hkpos)).
      set (iT := real_inv_pos T HT).
      set (xT0 := real_mult delta iT0).
      set (xT := real_mult delta iT).
      set (E0x := cauchy_real_exp (real_plus xT0 xT0)).
      set (ETx := cauchy_real_exp (real_plus xT xT)).
      (* inv T₀ == n̄_{S N}（双逆） *)
      assert (ET0 : real_eq iT0 (mte_nat_to_R (Datatypes.S N)))
        by exact (mtp_inv_inv (mte_nat_to_R (Datatypes.S N)) Hkpos).
      (* E₀ == e^{a2·n̄_{S N}} == (e^{a2})^{S N} *)
      assert (Eexp0 : real_eq (real_plus xT0 xT0)
                        (real_mult (real_plus delta delta)
                                   (mte_nat_to_R (Datatypes.S N)))).
      { assert (ExT0 : real_eq xT0 (real_mult delta (mte_nat_to_R (Datatypes.S N))))
          by (exact (RealSetoid.real_eq_mult_compat delta iT0 delta
                       (mte_nat_to_R (Datatypes.S N))
                       (real_eq_refl delta) ET0)).
        assert (Fdist : real_eq (real_mult (real_plus delta delta)
                                  (mte_nat_to_R (Datatypes.S N)))
                           (real_plus (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                                      (real_mult delta (mte_nat_to_R (Datatypes.S N))))).
        { apply (real_eq_trans _
                   (real_mult (mte_nat_to_R (Datatypes.S N)) (real_plus delta delta))).
          - exact (real_mult_comm (real_plus delta delta)
                     (mte_nat_to_R (Datatypes.S N))).
          - apply (real_eq_trans _
                     (real_plus (real_mult (mte_nat_to_R (Datatypes.S N)) delta)
                                (real_mult (mte_nat_to_R (Datatypes.S N)) delta))).
            + exact (real_distrib (mte_nat_to_R (Datatypes.S N)) delta delta).
            + exact (RealSetoid.real_eq_plus_compat
                       (real_mult (mte_nat_to_R (Datatypes.S N)) delta)
                       (real_mult (mte_nat_to_R (Datatypes.S N)) delta)
                       (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                       (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                       (real_mult_comm (mte_nat_to_R (Datatypes.S N)) delta)
                       (real_mult_comm (mte_nat_to_R (Datatypes.S N)) delta)). }
        exact (real_eq_trans (real_plus xT0 xT0)
                 (real_plus (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                            (real_mult delta (mte_nat_to_R (Datatypes.S N))))
                 (real_mult (real_plus delta delta)
                            (mte_nat_to_R (Datatypes.S N)))
                 (RealSetoid.real_eq_plus_compat xT0 xT0
                    (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                    (real_mult delta (mte_nat_to_R (Datatypes.S N))) ExT0 ExT0)
                 (real_eq_sym
                    (real_mult (real_plus delta delta)
                       (mte_nat_to_R (Datatypes.S N)))
                    (real_plus (real_mult delta (mte_nat_to_R (Datatypes.S N)))
                               (real_mult delta (mte_nat_to_R (Datatypes.S N))))
                    Fdist)). }
      assert (HE0pow : real_eq E0x
                        (mte_rpow (cauchy_real_exp (real_plus delta delta))
                                  (Datatypes.S N)))
        by (exact (real_eq_trans E0x
                     (cauchy_real_exp (real_mult (real_plus delta delta)
                                (mte_nat_to_R (Datatypes.S N))))
                     (mte_rpow (cauchy_real_exp (real_plus delta delta))
                        (Datatypes.S N))
                     (cauchy_real_exp_wd _ _ Eexp0)
                     (mte_exp_pow_iter (real_plus delta delta)
                        (Datatypes.S N)))).
      (* 窗序：E₀ < E(T)（倒数反序 + 乘正元 + exp 严格单调） *)
      assert (HiT0T : real_lt iT0 iT)
        by (exact (mtp_inv_antitone T (real_inv_pos (mte_nat_to_R (Datatypes.S N)) Hkpos)
                     HT (real_inv_pos_pos (mte_nat_to_R (Datatypes.S N)) Hkpos) HT0)).
      assert (Hxx : real_lt (real_plus xT0 xT0) (real_plus xT xT))
        by (exact (real_lt_plus_compat xT0 xT xT0 xT
                     (real_mult_lt_compat_l iT0 iT delta HiT0T Hd)
                     (real_mult_lt_compat_l iT0 iT delta HiT0T Hd))).
      assert (HE : real_lt E0x ETx) by exact (cauchy_real_exp_mono _ _ Hxx).
      (* δ*(T) == inv(E(T))：E·δ* == 1 + 逆元唯一性 *)
      assert (HdsInv : real_eq (mtp_delta_star delta T Hd HT)
                         (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT)))).
      { assert (Eal : real_eq (real_mult (cauchy_real_exp xT)
                                 (mtp_lo delta T Hd HT)) real_one)
          by (exact (real_eq_trans
                       (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT))
                       (real_mult (mtp_lo delta T Hd HT) (cauchy_real_exp xT))
                       real_one
                       (real_mult_comm (cauchy_real_exp xT) (mtp_lo delta T Hd HT))
                       (mtp_lo_mult_cancel delta T Hd HT))).
        unfold mtp_delta_star.
        apply (mtp_inv_unique ETx (cauchy_real_exp_pos (real_plus xT xT))
                 (real_mult (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT))).
        apply (real_eq_trans _
                 (real_mult (real_mult (cauchy_real_exp xT) (cauchy_real_exp xT))
                            (real_mult (mtp_lo delta T Hd HT)
                                       (mtp_lo delta T Hd HT)))).
        - exact (RealSetoid.real_eq_mult_compat ETx
                   (real_mult (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT))
                   (real_mult (cauchy_real_exp xT) (cauchy_real_exp xT))
                   (real_mult (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT))
                   (cauchy_real_exp_plus xT xT)
                   (real_eq_refl (real_mult (mtp_lo delta T Hd HT)
                                       (mtp_lo delta T Hd HT)))).
        - apply (real_eq_trans _
                   (real_mult (real_mult (real_mult (cauchy_real_exp xT)
                                            (cauchy_real_exp xT))
                                       (mtp_lo delta T Hd HT))
                              (mtp_lo delta T Hd HT))).
          + exact (real_mult_assoc
                     (real_mult (cauchy_real_exp xT) (cauchy_real_exp xT))
                     (mtp_lo delta T Hd HT) (mtp_lo delta T Hd HT)).
          + apply (real_eq_trans _
                     (real_mult (real_mult (cauchy_real_exp xT)
                                  (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT)))
                                (mtp_lo delta T Hd HT))).
            * exact (RealSetoid.real_eq_mult_compat
                       (real_mult (real_mult (cauchy_real_exp xT) (cauchy_real_exp xT))
                          (mtp_lo delta T Hd HT))
                       (mtp_lo delta T Hd HT)
                       (real_mult (cauchy_real_exp xT)
                          (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT)))
                       (mtp_lo delta T Hd HT)
                       (real_eq_sym _ _
                          (real_mult_assoc (cauchy_real_exp xT) (cauchy_real_exp xT)
                             (mtp_lo delta T Hd HT)))
                       (real_eq_refl (mtp_lo delta T Hd HT))).
            * apply (real_eq_trans _
                       (real_mult (real_mult (cauchy_real_exp xT) real_one)
                                  (mtp_lo delta T Hd HT))).
              -- exact (RealSetoid.real_eq_mult_compat
                           (real_mult (cauchy_real_exp xT)
                              (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT)))
                           (mtp_lo delta T Hd HT)
                           (real_mult (cauchy_real_exp xT) real_one)
                           (mtp_lo delta T Hd HT)
                           (RealSetoid.real_eq_mult_compat (cauchy_real_exp xT)
                              (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT))
                              (cauchy_real_exp xT) real_one
                              (real_eq_refl (cauchy_real_exp xT)) Eal)
                           (real_eq_refl (mtp_lo delta T Hd HT))).
              -- apply (real_eq_trans _
                           (real_mult (cauchy_real_exp xT) (mtp_lo delta T Hd HT))).
                 ++ exact (RealSetoid.real_eq_mult_compat
                              (real_mult (cauchy_real_exp xT) real_one)
                              (mtp_lo delta T Hd HT)
                              (cauchy_real_exp xT) (mtp_lo delta T Hd HT)
                              (real_mult_one (cauchy_real_exp xT))
                              (real_eq_refl (mtp_lo delta T Hd HT))).
                 ++ exact Eal.
      }
      (* 终局代数：w·invV < E₀ ⟹ w < V·E₀ ⟹ w·inv(E₀) < V ⟹ 链收口 *)
      assert (HA : real_lt (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                  (real_inv_pos V HV))
                          (mte_rpow (cauchy_real_exp (real_plus delta delta))
                                    (Datatypes.S N)))
        by (exact (real_lt_trans
                     (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                        (real_inv_pos V HV))
                     (mte_nat_to_R n0)
                     (mte_rpow (cauchy_real_exp (real_plus delta delta))
                        (Datatypes.S N))
                     HB2
                     (real_lt_trans (mte_nat_to_R n0)
                        (mte_nat_to_R (Datatypes.S n0))
                        (mte_rpow (cauchy_real_exp (real_plus delta delta))
                           (Datatypes.S N)) Hnlt Hpowk))).
      assert (HA2 : real_lt (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                  (real_inv_pos V HV)) E0x)
        by (exact (real_lt_eq_lt _
                     (mte_rpow (cauchy_real_exp (real_plus delta delta))
                               (Datatypes.S N)) _ HA
                     (real_eq_sym E0x
                        (mte_rpow (cauchy_real_exp (real_plus delta delta))
                           (Datatypes.S N)) HE0pow))).
      assert (HwVE0 : real_lt (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                              (real_mult V E0x)).
      { assert (Hlt1 : real_lt (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                 (real_mult E0x
                                    (real_inv_pos (real_inv_pos V HV)
                                       (real_inv_pos_pos V HV))))
          by (exact (mtp_mult_inv_fwd (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                        E0x (real_inv_pos V HV) (real_inv_pos_pos V HV) HA2)).
        exact (real_lt_eq_lt (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                 (real_mult E0x (real_inv_pos (real_inv_pos V HV)
                            (real_inv_pos_pos V HV)))
                 (real_mult V E0x) Hlt1
                 (real_eq_trans
                    (real_mult E0x (real_inv_pos (real_inv_pos V HV)
                               (real_inv_pos_pos V HV)))
                    (real_mult E0x V)
                    (real_mult V E0x)
                    (RealSetoid.real_eq_mult_compat E0x
                       (real_inv_pos (real_inv_pos V HV) (real_inv_pos_pos V HV))
                       E0x V
                       (real_eq_refl E0x)
                       (mtp_inv_inv V HV))
                    (real_mult_comm E0x V))). }
      assert (Hc : real_lt (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                                  (real_inv_pos E0x
                                     (cauchy_real_exp_pos (real_plus xT0 xT0))))
                          V)
        by (exact (mtp_lt_inv_rw (real_mult (mte_nat_to_R (Datatypes.S M)) b) V E0x
                     (cauchy_real_exp_pos (real_plus xT0 xT0)) HwVE0)).
      (* 总装 *)
      unfold mtp_anchor.
      apply (mtp_mult_inv_fwd (mte_nat_to_R (Datatypes.S M)) V
               (real_mult (mtp_delta_star delta T Hd HT) b)
               (real_mult_pos_compat (mtp_delta_star delta T Hd HT) b
                  (mtp_ds_pos delta T Hd HT) Hb)).
      apply (real_eq_lt_lt
               (real_mult (mte_nat_to_R (Datatypes.S M))
                          (real_mult (mtp_delta_star delta T Hd HT) b))
               (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                          (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT))))
               V).
      * exact (real_eq_trans
                 (real_mult (mte_nat_to_R (Datatypes.S M))
                            (real_mult (mtp_delta_star delta T Hd HT) b))
                 (real_mult (mte_nat_to_R (Datatypes.S M))
                            (real_mult b (mtp_delta_star delta T Hd HT)))
                 (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                            (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT))))
                 (RealSetoid.real_eq_mult_compat
                    (mte_nat_to_R (Datatypes.S M))
                    (real_mult (mtp_delta_star delta T Hd HT) b)
                    (mte_nat_to_R (Datatypes.S M))
                    (real_mult b (mtp_delta_star delta T Hd HT))
                    (real_eq_refl (mte_nat_to_R (Datatypes.S M)))
                    (real_mult_comm (mtp_delta_star delta T Hd HT) b))
                 (real_eq_trans
                    (real_mult (mte_nat_to_R (Datatypes.S M))
                               (real_mult b (mtp_delta_star delta T Hd HT)))
                    (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                               (mtp_delta_star delta T Hd HT))
                    (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                               (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT))))
                    (real_mult_assoc (mte_nat_to_R (Datatypes.S M)) b
                       (mtp_delta_star delta T Hd HT))
                    (RealSetoid.real_eq_mult_compat
                       (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                       (mtp_delta_star delta T Hd HT)
                       (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                       (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT)))
                       (real_eq_refl (real_mult (mte_nat_to_R (Datatypes.S M)) b))
                       HdsInv))).
      * exact (real_lt_trans
                 (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                            (real_inv_pos ETx (cauchy_real_exp_pos (real_plus xT xT))))
                 (real_mult (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                            (real_inv_pos E0x (cauchy_real_exp_pos (real_plus xT0 xT0))))
                 V
                 (real_mult_lt_compat_l (real_inv_pos ETx
                                            (cauchy_real_exp_pos (real_plus xT xT)))
                    (real_inv_pos E0x (cauchy_real_exp_pos (real_plus xT0 xT0)))
                    (real_mult (mte_nat_to_R (Datatypes.S M)) b)
                    (mtp_inv_antitone E0x ETx
                       (cauchy_real_exp_pos (real_plus xT0 xT0))
                       (cauchy_real_exp_pos (real_plus xT xT)) HE)
                    Hwpos)
                 Hc).
Qed.

(* ---------- 验证打印：全件零公理面（G2 关卡证据） ---------- *)
Print Assumptions mtp_inv_unique.
Print Assumptions mtp_inv_inv.
Print Assumptions mtp_inv_antitone.
Print Assumptions mtp_mult_inv_fwd.
Print Assumptions mtp_lt_inv_rw.
Print Assumptions mtp_lo_mult_cancel.
Print Assumptions mtp_lo_pos.
Print Assumptions mtp_lo_lt_one.
Print Assumptions mtp_ds_pos.
Print Assumptions mtp_ds_lt_one.
Print Assumptions mtp_ds_temp.
Print Assumptions mtp_anchor_divergence.
