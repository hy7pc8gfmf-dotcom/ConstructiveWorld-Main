(* ==========================================================================)
   RealKLDecomp.v — 实数层 KL 分解恒等式的完全闭合
   使命: rkd_kl_decomp_full：KL(p‖q) = E_p[−log q/p] − (−H) 的实数层分解（能量-熵两项），含分划版本 rkd_kl_decomp_full_partition；支撑件 rkd_log_pB/rkd_kl_point/rkd_energy_horse/rkd_boltzmann_normalized。
   依赖: QArith.Qring、CW_ConstructiveWorld_219、RealEnergyTempMono。
   对标: KL 分解恒等式（自由能 = 熵 + 能量，统计力学/信息论标准结果）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.Qring.
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
Require Import RealEnergyTempMono.

(* 原子级代数闭合：加/乘/负/原子项上的 real_eq 一步 ring（retm_alg 同款； *)
(*   限纯原子代数——含 one/zero 字面与 log/inv 桥位改走具名引理链）       *)
Ltac rkd_alg :=
  apply real_eq_of_zero_diff; intro n;
  repeat first [ rewrite real_plus_proj | rewrite real_mult_proj | rewrite real_opp_proj ];
  ring.

(* ============================================================ *)
(* Part 0：代数基元                                                  *)
(* ============================================================ *)

(* (−1)·x == −x（comm + mult_opp_l + mult_one 三步具名链） *)
Lemma rkd_mult_opp_r : forall x : Real,
  real_eq (real_mult (real_opp real_one) x) (real_opp x).
Proof.
  intro x.
  apply (real_eq_trans
           (real_mult (real_opp real_one) x)
           (real_mult x (real_opp real_one))
           (real_opp x)).
  - exact (real_mult_comm (real_opp real_one) x).
  - apply (real_eq_trans
             (real_mult x (real_opp real_one))
             (real_opp (real_mult x real_one))
             (real_opp x)).
    + exact (real_mult_opp_l x real_one).
    + exact (RealSetoid.real_eq_opp_compat (real_mult x real_one) x (real_mult_one x)).
Qed.

(* inv 吸收核：x·(inv x · y) == y（inv_pos_correct 桥，Bishop 类不走 rkd_alg） *)
Lemma rkd_inv_absorb : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x (real_mult (real_inv_pos x Hx) y)) y.
Proof.
  intros x y Hx.
  apply (real_eq_trans
           (real_mult x (real_mult (real_inv_pos x Hx) y))
           (real_mult (real_mult x (real_inv_pos x Hx)) y)
           y).
  - exact (real_mult_assoc x (real_inv_pos x Hx) y).
  - apply (real_eq_trans
             (real_mult (real_mult x (real_inv_pos x Hx)) y)
             (real_mult real_one y)
             y).
    + exact (RealSetoid.real_eq_mult_compat_adapt
               (real_mult x (real_inv_pos x Hx)) real_one y y
               (real_inv_pos_correct x Hx) (real_eq_refl y)).
    + apply (real_eq_trans
               (real_mult real_one y)
               (real_mult y real_one)
               y).
      * exact (real_mult_comm real_one y).
      * exact (real_mult_one y).
Qed.

(* 右消去：a == b + c ⟹ b == a + (−c)（原子代数链） *)
Lemma rkd_eq_cancel_r : forall a b c : Real,
  real_eq a (real_plus b c) -> real_eq b (real_plus a (real_opp c)).
Proof.
  intros a b c H.
  apply (real_eq_trans b (real_plus b real_zero) (real_plus a (real_opp c))).
  - apply real_eq_sym. exact (real_plus_zero b).
  - apply (real_eq_trans
             (real_plus b real_zero)
             (real_plus b (real_plus c (real_opp c)))
             (real_plus a (real_opp c))).
    + exact (RealSetoid.real_eq_plus_compat_adapt b b real_zero
               (real_plus c (real_opp c))
               (real_eq_refl b)
               (real_eq_sym (real_plus c (real_opp c)) real_zero (real_plus_opp c))).
    + apply (real_eq_trans
               (real_plus b (real_plus c (real_opp c)))
               (real_plus (real_plus b c) (real_opp c))
               (real_plus a (real_opp c))).
      * exact (real_plus_assoc b c (real_opp c)).
      * exact (RealSetoid.real_eq_plus_compat_adapt (real_plus b c) a
                 (real_opp c) (real_opp c) (real_eq_sym _ _ H)
                 (real_eq_refl (real_opp c))).
Qed.

(* ============================================================ *)
(* Part 1：逐点 log / kl 桥（零求和前提）                             *)
(* ============================================================ *)

(* log p_b(s) == −(e(s)/D + log Z)（零前提直证；rfep 件5a 同位重证，    *)
(*   log(inv Z) 肢依存 retm_log_inv_pos_gen 引擎）                      *)
Lemma rkd_log_pB : forall (S : Type) (real_base_loss : S -> Real)
  (D : Real) (D_pos : real_lt real_zero D) (Z : Real) (Z_pos : real_lt real_zero Z) (s : S)
  (Hpb : real_lt real_zero (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)),
  real_eq (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hpb)
          (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                               (real_log Z Z_pos))).
Proof.
  intros S real_base_loss D D_pos Z Z_pos s Hpb.
  set (Hcanon := real_mult_positive
                   (real_inv_pos Z Z_pos)
                   (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                   (real_inv_pos_pos Z Z_pos)
                   (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
  apply (real_eq_trans
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hpb)
           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hcanon)
           (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z Z_pos)))).
  - exact (real_log_wd
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
             Hpb Hcanon
             (real_eq_refl (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s))).
  - apply (real_eq_trans
             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s) Hcanon)
             (real_plus (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                        (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                  (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
             (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                  (real_log Z Z_pos)))).
    + exact (real_log_mult
               (real_inv_pos Z Z_pos)
               (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
               (real_inv_pos_pos Z Z_pos)
               (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
    + apply (real_eq_trans
               (real_plus (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                          (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                    (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_plus (real_opp (real_log Z Z_pos))
                          (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
               (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                    (real_log Z Z_pos)))).
      * exact (RealSetoid.real_eq_plus_compat_adapt
                 (real_log (real_inv_pos Z Z_pos) (real_inv_pos_pos Z Z_pos))
                 (real_opp (real_log Z Z_pos))
                 (real_log (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                           (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                 (retm_log_inv_pos_gen Z Z_pos)
                 (real_log_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * apply (real_eq_trans
                 (real_plus (real_opp (real_log Z Z_pos))
                            (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 (real_plus (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                            (real_opp (real_log Z Z_pos)))
                 (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                      (real_log Z Z_pos)))).
        -- exact (real_plus_comm (real_opp (real_log Z Z_pos))
                    (real_opp (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
        -- apply real_eq_sym.
           exact (real_opp_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s))
                                (real_log Z Z_pos)).
Qed.

(* kl_term 逐点展开：real_kl_term p q == p·(log p − log q) *)
Lemma rkd_kl_point : forall (p q : Real) (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_eq (real_kl_term p q Hp Hq)
          (real_mult p (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
Proof.
  intros p q Hp Hq. unfold real_kl_term.
  assert (Hinner : real_eq
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
  { apply (real_eq_trans
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
             (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
    - exact (RealSetoid.real_eq_opp_compat
               (real_log (real_mult q (real_inv_pos p Hp))
                         (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
               (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
               (real_eq_trans
                  (real_log (real_mult q (real_inv_pos p Hp))
                            (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp)))
                  (real_plus (real_log q Hq)
                             (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp)))
                  (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
                  (real_log_mult q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))
                  (RealSetoid.real_eq_plus_compat_adapt
                     (real_log q Hq) (real_log q Hq)
                     (real_log (real_inv_pos p Hp) (real_inv_pos_pos p Hp))
                     (real_opp (real_log p Hp))
                     (real_eq_refl (real_log q Hq))
                     (retm_log_inv_pos_gen p Hp)))).
    - apply (real_eq_trans
               (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
               (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
               (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
      + exact (real_opp_plus (real_log q Hq) (real_opp (real_log p Hp))).
      + apply (real_eq_trans
                 (real_plus (real_opp (real_log q Hq)) (real_opp (real_opp (real_log p Hp))))
                 (real_plus (real_opp (real_log q Hq)) (real_log p Hp))
                 (real_plus (real_log p Hp) (real_opp (real_log q Hq)))).
        * exact (RealSetoid.real_eq_plus_compat_adapt
                   (real_opp (real_log q Hq)) (real_opp (real_log q Hq))
                   (real_opp (real_opp (real_log p Hp))) (real_log p Hp)
                   (real_eq_refl (real_opp (real_log q Hq)))
                   (real_opp_opp (real_log p Hp))).
        * exact (real_plus_comm (real_opp (real_log q Hq)) (real_log p Hp)). }
  exact (RealSetoid.real_eq_mult_compat_adapt p p
           (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                               (real_mult_positive q (real_inv_pos p Hp) Hq (real_inv_pos_pos p Hp))))
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
           (real_eq_refl p) Hinner).
Qed.

(* ============================================================ *)
(* Part 2：求和层基元                                                 *)
(* ============================================================ *)

(* Σ (−f) == −(Σ f)（ext 点态 + linear 两步组装，rfep P0 同位） *)
Lemma rkd_sum_opp : forall (S : Type) (sumf : (S -> Real) -> Real)
  (sumf_ext : forall (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
  (sumf_linear : forall (a : Real) (f : S -> Real),
    real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
  (f : S -> Real),
  real_eq (sumf (fun s : S => real_opp (f s))) (real_opp (sumf f)).
Proof.
  intros S sumf sumf_ext sumf_linear f.
  apply (real_eq_trans
           (sumf (fun s : S => real_opp (f s)))
           (real_mult (real_opp real_one) (sumf f))
           (real_opp (sumf f))).
  - apply (real_eq_trans
             (sumf (fun s : S => real_opp (f s)))
             (sumf (fun s : S => real_mult (real_opp real_one) (f s)))
             (real_mult (real_opp real_one) (sumf f))).
    + apply real_eq_sym. apply sumf_ext. intro s.
      exact (rkd_mult_opp_r (f s)).
    + exact (sumf_linear (real_opp real_one) f).
  - exact (rkd_mult_opp_r (sumf f)).
Qed.

(* ============================================================ *)
(* Part 3：能量期望辅助引理（plus 形，任意正分布 q）                     *)
(*   Σ q·e + D·Σ q·log p_b == −D·log Z（归一化 Σ q == 1 入槽）         *)
(* ============================================================ *)
Lemma rkd_energy_horse :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (q : S -> Real) (Hq : forall s : S, real_lt real_zero (q s))
    (Hnormq : real_eq (sumf q) real_one),
  real_eq
    (real_plus
       (sumf (fun s : S => real_mult (q s) (real_base_loss s)))
       (real_mult D
          (sumf (fun s : S => real_mult (q s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
    (real_opp (real_mult D (real_log Z Z_pos))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos q Hq Hnormq.
  set (LZ := real_log Z Z_pos).
  set (Spe := sumf (fun s : S => real_mult (q s) (real_base_loss s))).
  set (SLB := sumf (fun s : S => real_mult (q s)
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  (* 点态：e s == −D·log p_b(s) + −D·log Z *)
  assert (Hpt : forall s : S,
    real_eq (real_base_loss s)
            (real_plus
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_opp (real_mult D LZ)))).
  {
    intro s.
    assert (HL1 := rkd_log_pB S real_base_loss D D_pos Z Z_pos s
                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)).
    (* D·log p_b(s) == −(e s + D·log Z) *)
    assert (HDL : real_eq
               (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
               (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
    { apply (real_eq_trans
               (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
               (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
               (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
      - exact (RealSetoid.real_eq_mult_compat_adapt D D _ _
                 (real_eq_refl D) HL1).
      - apply (real_eq_trans
                 (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                 (real_opp (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                      (real_mult D LZ)))
                 (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))).
        + exact (real_eq_trans
                   (real_mult D (real_opp (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                   (real_opp (real_mult D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ)))
                   (real_opp (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                        (real_mult D LZ)))
                   (real_mult_opp_l D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))
                   (RealSetoid.real_eq_opp_compat
                      (real_mult D (real_plus (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))
                      (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                                 (real_mult D LZ))
                      (real_distrib D (real_mult (real_inv_pos D D_pos) (real_base_loss s)) LZ))).
        + exact (RealSetoid.real_eq_opp_compat
                   (real_plus (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                              (real_mult D LZ))
                   (real_plus (real_base_loss s) (real_mult D LZ))
                   (RealSetoid.real_eq_plus_compat_adapt
                      (real_mult D (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
                      (real_base_loss s)
                      (real_mult D LZ) (real_mult D LZ)
                      (rkd_inv_absorb D (real_base_loss s) D_pos)
                      (real_eq_refl (real_mult D LZ)))).
    }
    (* opp(D·log p_b) == e s + D·log Z，再右消去 *)
    assert (H4 : real_eq
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_plus (real_base_loss s) (real_mult D LZ))).
    { apply (real_eq_trans
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
               (real_opp (real_opp (real_plus (real_base_loss s) (real_mult D LZ))))
               (real_plus (real_base_loss s) (real_mult D LZ))).
      - exact (RealSetoid.real_eq_opp_compat
                 (real_mult D
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
                 (real_opp (real_plus (real_base_loss s) (real_mult D LZ)))
                 HDL).
      - exact (real_opp_opp (real_plus (real_base_loss s) (real_mult D LZ))). }
    exact (rkd_eq_cancel_r
             (real_opp (real_mult D
                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
             (real_base_loss s) (real_mult D LZ) H4).
  }
  (* ext：Σ q·e == Σ q·(−D·log p_b + −D·log Z) *)
  assert (Hext : real_eq Spe
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))).
  { apply sumf_ext. intro w.
    exact (RealSetoid.real_eq_mult_compat_adapt (q w) (q w) _ _
             (real_eq_refl (q w)) (Hpt w)). }
  (* distrib 点态 + add：拆两个合取肢 *)
  assert (Hsplit : real_eq
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s)
                      (real_plus
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                         (real_opp (real_mult D LZ)))))
             (sumf (fun s : S => real_plus
                       (real_mult (q s)
                          (real_opp (real_mult D
                             (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                       (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
                       (real_mult (q s) (real_opp (real_mult D LZ)))))
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))).
    - apply sumf_ext. intro w.
      exact (real_distrib (q w)
               (real_opp (real_mult D
                  (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))))
               (real_opp (real_mult D LZ))).
    - exact (sumf_add
               (fun s : S => real_mult (q s)
                  (real_opp (real_mult D
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
               (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))). }
  (* 肢1：Σ q·(−D·Lb) == −(D·SLB) *)
  assert (HT1 : real_eq
             (sumf (fun s : S => real_mult (q s)
                      (real_opp (real_mult D
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (real_mult D SLB))).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s)
                      (real_opp (real_mult D
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (sumf (fun s : S => real_mult D
                         (real_mult (q s)
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_opp (real_mult D SLB))).
    - apply (real_eq_trans
               (sumf (fun s : S => real_mult (q s)
                        (real_opp (real_mult D
                           (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                     (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
               (sumf (fun s : S => real_opp (real_mult D
                         (real_mult (q s)
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
               (real_opp (sumf (fun s : S => real_mult D
                           (real_mult (q s)
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
      + apply sumf_ext. intro w. rkd_alg.
      + exact (rkd_sum_opp S sumf sumf_ext sumf_linear
                 (fun s : S => real_mult D
                    (real_mult (q s)
                       (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                 (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
    - exact (RealSetoid.real_eq_opp_compat
               (sumf (fun s : S => real_mult D
                  (real_mult (q s)
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
               (real_mult D SLB)
               (sumf_linear D
                  (fun s : S => real_mult (q s)
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))). }
  (* 肢2：Σ q·(−D·log Z) == (−D)·log Z·Σ q，归一化闭合 *)
  assert (HT2 : real_eq
             (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ))))
             (real_mult (real_opp D) LZ)).
  { apply (real_eq_trans
             (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ))))
             (sumf (fun s : S => real_mult (real_mult (real_opp D) LZ) (q s)))
             (real_mult (real_opp D) LZ)).
    - apply sumf_ext. intro w. rkd_alg.
    - apply (real_eq_trans
               (sumf (fun s : S => real_mult (real_mult (real_opp D) LZ) (q s)))
               (real_mult (real_mult (real_opp D) LZ) (sumf q))
               (real_mult (real_opp D) LZ)).
      + exact (sumf_linear (real_mult (real_opp D) LZ) q).
      + exact (real_eq_trans
                 (real_mult (real_mult (real_opp D) LZ) (sumf q))
                 (real_mult (real_mult (real_opp D) LZ) real_one)
                 (real_mult (real_opp D) LZ)
                 (RealSetoid.real_eq_mult_compat_adapt
                    (real_mult (real_opp D) LZ) (real_mult (real_opp D) LZ)
                    (sumf q) real_one
                    (real_eq_refl (real_mult (real_opp D) LZ)) Hnormq)
                 (real_mult_one (real_mult (real_opp D) LZ))). }
  (* 组装：Spe == −D·SLB + (−D)·log Z *)
  assert (Hmain : real_eq Spe (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))).
  { exact (real_eq_trans Spe
             (real_plus
                (sumf (fun s : S => real_mult (q s)
                         (real_opp (real_mult D
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))
             (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))
             (real_eq_trans Spe
                (sumf (fun s : S => real_mult (q s)
                         (real_plus
                            (real_opp (real_mult D
                               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                            (real_opp (real_mult D LZ)))))
                (real_plus
                   (sumf (fun s : S => real_mult (q s)
                            (real_opp (real_mult D
                               (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                         (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
                   (sumf (fun s : S => real_mult (q s) (real_opp (real_mult D LZ)))))
                Hext Hsplit)
             (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ HT1 HT2)). }
  apply (real_eq_trans
           (real_plus Spe (real_mult D SLB))
           (real_plus (real_plus (real_opp (real_mult D SLB)) (real_mult (real_opp D) LZ))
                      (real_mult D SLB))
           (real_opp (real_mult D LZ))).
  - exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _ Hmain
             (real_eq_refl (real_mult D SLB))).
  - rkd_alg.
Qed.

(* ============================================================ *)
(* Part 4：Σ 层 kl 桥 + Boltzmann 归一化                              *)
(* ============================================================ *)

(* Σ kl_term(p, p_b) == Σ p·log p − Σ p·log p_b（逐点 rkd_kl_point    *)
(*   + distrib + add + sum_opp 四步机组）                             *)
Lemma rkd_kl_sum_bridge :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq
    (sumf (fun s : S => real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
    (real_plus
       (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
       (real_opp
          (sumf (fun s : S => real_mult (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos p Hp.
  apply (real_eq_trans
           (sumf (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
           (real_plus
              (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
              (sumf (fun s : S => real_mult (p s)
                       (real_opp
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
           (real_plus
              (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
              (real_opp
                 (sumf (fun s : S => real_mult (p s)
                          (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
  - apply (real_eq_trans
             (sumf (fun s : S => real_kl_term (p s)
                        (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                        (Hp s)
                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))
             (sumf (fun s : S => real_plus
                        (real_mult (p s) (real_log (p s) (Hp s)))
                        (real_mult (p s)
                           (real_opp
                              (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                        (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))
             (real_plus
                (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
                (sumf (fun s : S => real_mult (p s)
                         (real_opp
                            (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))))).
    + apply sumf_ext. intro w.
      exact (real_eq_trans
               (real_kl_term (p w)
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                  (Hp w)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))
               (real_mult (p w)
                  (real_plus (real_log (p w) (Hp w))
                             (real_opp
                                (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                                          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w)))))
               (real_plus
                  (real_mult (p w) (real_log (p w) (Hp w)))
                  (real_mult (p w)
                     (real_opp
                        (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w)))))
               (rkd_kl_point (p w)
                  (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                  (Hp w)
                  (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))
               (real_distrib (p w) (real_log (p w) (Hp w))
                  (real_opp
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos w)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos w))))).
    + exact (sumf_add
               (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))
               (fun s : S => real_mult (p s)
                  (real_opp
                     (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
  - apply (RealSetoid.real_eq_plus_compat_adapt
             (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
             (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s))))
             (sumf (fun s : S => real_mult (p s)
                      (real_opp
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_opp
                (sumf (fun s : S => real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_eq_refl (sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))))).
    exact (real_eq_trans
             (sumf (fun s : S => real_mult (p s)
                      (real_opp
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (sumf (fun s : S => real_opp
                      (real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (real_opp
                (sumf (fun s : S => real_mult (p s)
                         (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                   (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))))
             (sumf_ext
                (fun s : S => real_mult (p s)
                   (real_opp
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                (fun s : S => real_opp
                   (real_mult (p s)
                      (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
                (fun s : S => real_mult_opp_l (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))
             (rkd_sum_opp S sumf sumf_ext sumf_linear
                (fun s : S => real_mult (p s)
                   (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
Qed.

(* 归一化：partition 条件 Σ exp(−e/D) == Z ⟹ Σ p_b == 1                *)
(*   （linear + inv_pos_correct 两步归一化，rfep 件5b 同位）            *)
Lemma rkd_boltzmann_normalized :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (Hpart : real_eq
               (sumf (fun s : S => real_exp_neg
                                 (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
               Z),
  real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one.
Proof.
  intros S sumf sumf_ext sumf_linear real_base_loss D D_pos Z Z_pos Hpart.
  apply (real_eq_trans
           (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos))
           (real_mult (real_inv_pos Z Z_pos) Z)
           real_one).
  - apply (real_eq_trans
             (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos))
             (sumf (fun s : S => real_mult (real_inv_pos Z Z_pos)
                       (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
             (real_mult (real_inv_pos Z Z_pos) Z)).
    + apply sumf_ext. intro s. exact (real_eq_refl _).
    + apply (real_eq_trans
               (sumf (fun s : S => real_mult (real_inv_pos Z Z_pos)
                         (real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z Z_pos)
                  (sumf (fun s : S => real_exp_neg
                           (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))
               (real_mult (real_inv_pos Z Z_pos) Z)).
      * exact (sumf_linear (real_inv_pos Z Z_pos)
                  (fun s : S => real_exp_neg
                                   (real_mult (real_inv_pos D D_pos) (real_base_loss s)))).
      * exact (RealSetoid.real_eq_mult_compat_adapt
                 (real_inv_pos Z Z_pos) (real_inv_pos Z Z_pos)
                 (sumf (fun s : S => real_exp_neg
                          (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
                 Z
                 (real_eq_refl (real_inv_pos Z Z_pos)) Hpart).
  - apply (real_eq_trans
             (real_mult (real_inv_pos Z Z_pos) Z)
             (real_mult Z (real_inv_pos Z Z_pos))
             real_one).
    + exact (real_mult_comm (real_inv_pos Z Z_pos) Z).
    + exact (real_inv_pos_correct Z Z_pos).
Qed.

(* ============================================================ *)
(* Part 5：主件——real_kl_decomp_full 槽实例化消解件                          *)
(* ============================================================ *)

(* 主件1（一般 Z 条件件）：结论面与 UpRealLeB L218 / S08 L2516 槽      *)
(*   逐字同构；前提面 = 槽 (Hp, Hnormp) + 结构增量 ext/add/linear +    *)
(*   残留数学前提 Hnormb（Σ p_b == 1，诚实申报）。                     *)
Theorem rkd_kl_decomp_full :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one),
  real_eq
    (real_free_energy S sumf real_base_loss D p Hp)
    (real_plus
       (real_free_energy S sumf real_base_loss D
          (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos))
       (real_mult D
          (sumf (fun s : S =>
             real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb.
  unfold real_free_energy.
  set (LZ := real_log Z Z_pos).
  set (A := sumf (fun s : S => real_mult (p s) (real_base_loss s))).
  set (B := sumf (fun s : S => real_mult (p s) (real_log (p s) (Hp s)))).
  set (C := sumf (fun s : S => real_mult (p s)
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  set (E := sumf (fun s : S => real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (real_base_loss s))).
  set (G := sumf (fun s : S => real_mult (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (real_log (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                              (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
  set (K := sumf (fun s : S => real_kl_term (p s)
                    (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
                    (Hp s)
                    (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s))).
  assert (H1 : real_eq (real_plus A (real_mult D C)) (real_opp (real_mult D LZ))).
  { exact (rkd_energy_horse S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos p Hp Hnormp). }
  assert (H2 : real_eq (real_plus E (real_mult D G)) (real_opp (real_mult D LZ))).
  { exact (rkd_energy_horse S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos) Hnormb). }
  assert (H3 : real_eq K (real_plus B (real_opp C))).
  { exact (rkd_kl_sum_bridge S sumf sumf_ext sumf_add sumf_linear
             real_base_loss D D_pos Z Z_pos p Hp). }
  apply (real_eq_trans
           (real_plus A (real_mult D B))
           (real_plus (real_plus E (real_mult D G)) (real_mult D (real_plus B (real_opp C))))
           (real_plus (real_plus E (real_mult D G)) (real_mult D K))).
  - apply (real_eq_trans
             (real_plus A (real_mult D B))
             (real_plus (real_plus A (real_mult D C)) (real_mult D (real_plus B (real_opp C))))
             (real_plus (real_plus E (real_mult D G)) (real_mult D (real_plus B (real_opp C))))).
    + rkd_alg.
    + exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _
               (real_eq_trans (real_plus A (real_mult D C)) (real_opp (real_mult D LZ))
                              (real_plus E (real_mult D G)) H1 (real_eq_sym _ _ H2))
               (real_eq_refl (real_mult D (real_plus B (real_opp C))))).
  - exact (RealSetoid.real_eq_plus_compat_adapt _ _ _ _
             (real_eq_refl (real_plus E (real_mult D G)))
             (RealSetoid.real_eq_mult_compat_adapt D D
                (real_plus B (real_opp C)) K
                (real_eq_refl D) (real_eq_sym _ _ H3))).
Qed.

(* 主件2（定义 Z 无条件形）：Z := Σ exp(−e/D) 内联定义，正性证书为     *)
(*   唯一额外前提（与槽节内 Z_align_r_pos 同类），Hnormb 由             *)
(*   rkd_boltzmann_normalized + partition 定义等式（real_eq_refl）内证  *)
(*   消去——零残留数学前提的「无条件定理」交付形。                       *)
Theorem rkd_kl_decomp_full_partition :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Zp : real_lt real_zero
            (sumf (fun s : S => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (real_base_loss s))))),
  real_eq
    (real_free_energy S sumf real_base_loss D p Hp)
    (real_plus
       (real_free_energy S sumf real_base_loss D
          (real_boltzmann_dist_r S real_base_loss D D_pos
             (sumf (fun s : S => real_exp_neg
                       (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp)
          (real_boltzmann_dist_r_pos S real_base_loss D D_pos
             (sumf (fun s : S => real_exp_neg
                       (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp))
       (real_mult D
          (sumf (fun s : S =>
             real_kl_term (p s)
               (real_boltzmann_dist_r S real_base_loss D D_pos
                  (sumf (fun s : S => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp s)
               (Hp s)
               (real_boltzmann_dist_r_pos S real_base_loss D D_pos
                  (sumf (fun s : S => real_exp_neg
                            (real_mult (real_inv_pos D D_pos) (real_base_loss s)))) Zp s))))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos p Hp Hnormp Zp.
  apply (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear           real_base_loss D D_pos           (sumf (fun s : S => real_exp_neg                     (real_mult (real_inv_pos D D_pos) (real_base_loss s))))           Zp p Hp Hnormp).
  exact (rkd_boltzmann_normalized S sumf sumf_ext sumf_linear           real_base_loss D D_pos           (sumf (fun s : S => real_exp_neg                     (real_mult (real_inv_pos D D_pos) (real_base_loss s))))           Zp (real_eq_refl _)).
Qed.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设                                         *)
(* ============================================================ *)
Print Assumptions rkd_mult_opp_r.
Print Assumptions rkd_inv_absorb.
Print Assumptions rkd_eq_cancel_r.
Print Assumptions rkd_log_pB.
Print Assumptions rkd_kl_point.
Print Assumptions rkd_sum_opp.
Print Assumptions rkd_energy_horse.
Print Assumptions rkd_kl_sum_bridge.
Print Assumptions rkd_boltzmann_normalized.
Print Assumptions rkd_kl_decomp_full.
Print Assumptions rkd_kl_decomp_full_partition.
