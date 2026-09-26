(* ==========================================================================)
   AttnSqrt.v — 构造性平方根存在性与一般维数推广
   使命: real_sqrt_exists（正元平方根存在性 sigT 见证形）、sqrt_witness_sq/nat_sq（k² 维数一般化）、nat_to_R 嵌入三件、scale_dual_sq_k/nat_sq_k 温度缩放实例化。
   依赖: CW_ConstructiveWorld_219；Stdlib List、QArith、Setoid、Morphisms。
   对标: 实平方根存在性（Bishop 构造性分析；正性由指数给出，无二分分支）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
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

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 0：Real 层逐点工具（½x + ½x == x，逐点 Q 环恒等）        *)
(* ============================================================ *)

(* 逐点：projT1 (real_mult (real_const ½) x) n == ½·x_n（组装投影引理） *)
Lemma sqrt_half_proj : forall (x : Real) (n : nat),
  projT1 (real_mult (real_const (1#2)) x) n == (1#2) * projT1 x n.
Proof.
  intros x n.
  rewrite (real_mult_const_proj (1#2) x n).
  rewrite (real_const_proj (1#2) n).
  reflexivity.
Qed.

(* ½·x + ½·x == x（real_eq 逐点；Q 层恒等 ½q + ½q == q 由 ring 判定） *)
Lemma sqrt_real_plus_half_half : forall x : Real,
  real_eq (real_plus (real_mult (real_const (1#2)) x)
                     (real_mult (real_const (1#2)) x))
          x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  (* 差的逐点化简：½x_n + ½x_n − x_n == 0 *)
  assert (Hd : projT1 (real_plus (real_mult (real_const (1#2)) x)
                                 (real_mult (real_const (1#2)) x)) n
                - projT1 x n == 0%Q).
  { rewrite (real_plus_proj (real_mult (real_const (1#2)) x)
                            (real_mult (real_const (1#2)) x) n).
    rewrite (sqrt_half_proj x n).
    ring. }
  (* Qabs(差) == Qabs 0 == 0，逐点界 |0| < eps *)
  assert (Habs0 : Qabs (projT1 (real_plus (real_mult (real_const (1#2)) x)
                                          (real_mult (real_const (1#2)) x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* Part 1（G2）：Real 层构造性平方根存在性                       *)
(* ============================================================ *)

Theorem real_sqrt_exists : forall d : Real, real_le real_zero d ->
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) d)).
Proof.
  intros d Hd.
  destruct Hd as [Hdlt | Hdeq].
  - 
    exists (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))).
    split.
    + (* r > 0：exp 恒正（real_le 左支 = real_lt） *)
      exact (inl (cauchy_real_exp_pos
              (real_mult (real_const (1#2)) (cw_log d Hdlt)))).
    + 
      apply (real_eq_trans
              (real_mult (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt)))
                         (cauchy_real_exp (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                          (real_mult (real_const (1#2)) (cw_log d Hdlt))))
              d).
      * (* 反向用 exp 加法性：exp(x)·exp(y) == exp(x+y) *)
        apply real_eq_sym. apply cauchy_real_exp_plus.
      * apply (real_eq_trans
                (cauchy_real_exp (real_plus (real_mult (real_const (1#2)) (cw_log d Hdlt))
                                            (real_mult (real_const (1#2)) (cw_log d Hdlt))))
                (cauchy_real_exp (cw_log d Hdlt)) d).
        -- 
           apply cauchy_real_exp_wd.
           apply sqrt_real_plus_half_half.
        -- 
           apply cw_log_exp_right.
  - (* 情形②：d ≡ 0（real_eq 证书 Hdeq）。r := real_zero。 *)
    exists real_zero.
    split.
    + (* 0 ≥ 0：real_le 右支 = real_eq 0 0（自反） *)
      exact (inr (real_eq_refl real_zero)).
    + (* 0·0 == 0 == d *)
      apply (real_eq_trans (real_mult real_zero real_zero) real_zero d).
      * apply real_mult_zero.
      * exact Hdeq.
Qed.

(* 具体实例（机器可提取的健全性检查）：1 的平方根可构造。        *)
(*   r := exp(½·log 1)，r ≥ 0 且 r·r == 1——G2 主定理的 d=1 实例。 *)

Lemma real_one_pos_local : real_lt real_zero real_one.
Proof.
  exists (1#2).
  split.
  - reflexivity.
  - exists 0%nat. intros n Hn. reflexivity.
Qed.

Lemma real_sqrt_one :
  sigT (fun r : Real => And (real_le real_zero r)
                            (real_eq (real_mult r r) real_one)).
Proof.
  exact (real_sqrt_exists real_one (inl real_one_pos_local)).
Qed.

(* ============================================================ *)
(* Part 2（G1）：一般平方维数见证（抽象 R 层，接口泛型）          *)
(*   库内机器检查实例此前仅 d=4（sq_witness_4）；本节给出一般    *)
(*   k² 维数的 sqrt_witness 见证族与对偶实例。                   *)
(* ============================================================ *)

Section SqrtWitnessGeneral.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* nat → R 嵌入复用库内 nat_to_R（RI 隐式实例参数）。           *)

(* 加法同态：nat_to_R (m+n) == nat_to_R m + nat_to_R n          *)
Lemma nat_to_R_plus_hom : forall m n : nat,
  Id (nat_to_R (m + n)%nat) (plus (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (plus_comm zero (nat_to_R n))
                            (plus_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (id_cong (fun t => plus one t) IH)
                    (plus_assoc one (nat_to_R m) (nat_to_R n))).
Qed.

(* 乘法同态：nat_to_R (m·n) == nat_to_R m · nat_to_R n          *)
Lemma nat_to_R_mult_hom : forall m n : nat,
  Id (nat_to_R (m * n)%nat) (mult (nat_to_R m) (nat_to_R n)).
Proof.
  intros m n. induction m as [| m IH].
  - simpl.
    exact (id_sym (id_trans (mult_comm zero (nat_to_R n))
                            (mult_zero (nat_to_R n)))).
  - simpl.
    exact (id_trans (nat_to_R_plus_hom n (m * n)%nat)
           (id_trans (id_cong (fun t => plus (nat_to_R n) t) IH)
           (id_trans (id_cong (fun t => plus t (mult (nat_to_R m) (nat_to_R n)))
                              (id_sym (mult_one (nat_to_R n))))
           (id_trans (id_cong (fun t => plus (mult (nat_to_R n) one) t)
                              (mult_comm (nat_to_R m) (nat_to_R n)))
           (id_trans (id_sym (distrib (nat_to_R n) one (nat_to_R m)))
                     (mult_comm (nat_to_R n) (plus one (nat_to_R m)))))))).
Qed.

(* nat_to_R 的严格正性：k ≥ 1 ⟹ 0 < nat_to_R k                 *)
Lemma nat_to_R_pos : forall k : nat, lt zero (nat_to_R (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - simpl.
    exact (lt_id_r zero one (plus one zero)
                   (id_sym (plus_zero one)) one_pos).
  - simpl. exact (plus_positive one (nat_to_R (Datatypes.S k)) one_pos IH).
Qed.

(* 见证（字面形式）：d := r·r（Id 自反；即「r 即 √(r²)」的命名式） *)
Lemma sqrt_witness_sq : forall k : nat,
  sqrt_witness (mult (nat_to_R k) (nat_to_R k)) (nat_to_R k).
Proof. intro k. exact (@id_refl _ (mult (nat_to_R k) (nat_to_R k))). Qed.

(* 见证（非平凡形式）：d := nat_to_R (k·k) == nat_to_R k · nat_to_R k
   （由乘法同态 nat_to_R_mult_hom 给出——k² 维数的真见证）      *)
Lemma sqrt_witness_nat_sq : forall k : nat,
  sqrt_witness (nat_to_R (k * k)%nat) (nat_to_R k).
Proof. intro k. exact (id_sym (nat_to_R_mult_hom k k)). Qed.

(* k² 维数对偶实例：1/(S k) 缩放 == 温度 (S k)
   （scale_sqrt_witness_dual 在 d := nat_to_R (S k) · nat_to_R (S k)、
     r := nat_to_R (S k) 的实例化；k ≥ 0 ⟹ 温度 ≥ 1 > 0）       *)
Lemma scale_dual_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (mult (nat_to_R (Datatypes.S k)) (nat_to_R (Datatypes.S k)))           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_sq (Datatypes.S k)) z s).
Qed.

(* 对偶实例（nat 平方形式，d := nat_to_R ((S k)·(S k))）         *)
Lemma scale_dual_nat_sq_k :
  forall (SS : StateSpace RI) (SO : SumOver RI SS)
         (spp : forall f : @S RI SS -> @R RI,
                (forall s : @S RI SS, lt zero (f s)) ->
                lt zero (@sum_over_S RI SS SO f))
         (k : nat) (z : @logits RI SS) (s : @S RI SS),
    Id (@softmax_scaled RI SS SO spp
          (@inv_pos RI (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)) z s)
       (@softmax_temp_param RI SS SO spp
          (nat_to_R (Datatypes.S k)) (nat_to_R_pos k) z s).
Proof.
  intros SS SO spp k z s.
  exact (scale_sqrt_witness_dual spp           (nat_to_R ((Datatypes.S k) * (Datatypes.S k))%nat)           (nat_to_R (Datatypes.S k)) (nat_to_R_pos k)           (sqrt_witness_nat_sq (Datatypes.S k)) z s).
Qed.

End SqrtWitnessGeneral.
