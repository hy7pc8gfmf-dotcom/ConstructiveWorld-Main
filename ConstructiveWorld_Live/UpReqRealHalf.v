(* ==========================================================================)
   UpReqRealHalf.v — 实数半运算与指数平方恒等
   使命: upreq_half（½·x）定义、upreq_half_proj（逐点投影）、upreq_half_plus（½x+½x == x）、upreq_half_opp 与 upreq_exp_half_sq/upreq_exp_neg_half_sq（exp x == exp(x/2)^2）。
   依赖: CW_ConstructiveWorld_219、AttnSqrt；Stdlib QArith、Setoid、Morphisms
   对标: 实数域的半运算与指数函数平方恒等式 exp(x) = exp(x/2)^2（S02 半件直拼）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
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
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import AttnSqrt.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Morphisms.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 件 0（主件函数形）：Real 层半元函数                              *)
(*   upreq_half x := ½·x（常值序列 ½ 的乘法包装；逐项即 v_n=u_n/2）。 *)
(* ============================================================ *)
Definition upreq_half (x : Real) : Real := real_mult (real_const (1#2)) x.

(* ============================================================ *)
(* 件 1：逐点投影 projT1 (upreq_half x) n == ½·x_n                  *)
(*   （S02 三投影件直拼；供后续 ε 预算/界估计论证依存的独立锚）     *)
(* ============================================================ *)
Lemma upreq_half_proj : forall (x : Real) (n : nat),
  projT1 (upreq_half x) n == (1#2) * projT1 x n.
Proof.
  intros x n.
  unfold upreq_half.
  rewrite (real_mult_const_proj (1#2) x n).
  rewrite (real_const_proj (1#2) n).
  exact (Qeq_refl ((1#2) * projT1 x n)).
Qed.

(* ============================================================ *)
(* 件 2（主定理）：加倍恒等 half x + half x == x                    *)
(*   依存 AttnSqrt sqrt_real_plus_half_half 一跳 exact（函数定义    *)
(*   delta 可折换）；证态为 real_eq 逐 eps 形，N:=0 全域生效。      *)
(* ============================================================ *)
Theorem upreq_half_plus : forall x : Real,
  real_eq (real_plus (upreq_half x) (upreq_half x)) x.
Proof.
  intro x.
  exact (sqrt_real_plus_half_half x).
Qed.

(* ============================================================ *)
(* 件 3：half 与 real_opp 交换：half(−x) == −(half x)               *)
(*   逐点：½·(−x_n) − (−½·x_n) == 0，ring 判定；N:=0 全域生效。     *)
(* ============================================================ *)
Lemma upreq_half_opp : forall x : Real,
  real_eq (upreq_half (real_opp x)) (real_opp (upreq_half x)).
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hd : projT1 (upreq_half (real_opp x)) n
               - projT1 (real_opp (upreq_half x)) n == 0%Q).
  { rewrite (upreq_half_proj (real_opp x) n).
    rewrite (real_opp_proj (upreq_half x) n).
    rewrite (real_opp_proj x n).
    rewrite (upreq_half_proj x n).
    ring. }
  assert (Habs0 : Qabs (projT1 (upreq_half (real_opp x)) n
                        - projT1 (real_opp (upreq_half x)) n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - exact (Qeq_refl 0%Q). }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* 件 4：双重取反消去 real_opp (real_opp x) == x（库内缺位补建）    *)
(*   逐点：−(−x_n) − x_n == 0，ring 判定；N:=0 全域生效。           *)
(*   （eˣ 原生形 real_exp_neg (real_opp x) 与加餐件级联的运输基础模块）  *)
(* ============================================================ *)
Lemma upreq_real_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof.
  intros x eps Heps.
  exists 0%nat.
  intros n Hn.
  assert (Hd : projT1 (real_opp (real_opp x)) n - projT1 x n == 0%Q).
  { rewrite (real_opp_proj (real_opp x) n).
    rewrite (real_opp_proj x n).
    ring. }
  assert (Habs0 : Qabs (projT1 (real_opp (real_opp x)) n
                        - projT1 x n) == 0%Q).
  { apply Qeq_trans with (Qabs 0%Q).
    - apply Qabs_wd. exact Hd.
    - exact (Qeq_refl 0%Q). }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* 件 5（加餐·一般形，等式面）：eᶻ == (eᶻᐟ²)²                       *)
(*   链：exp z == exp(zᐟ²+zᐟ²)（外延 wd 于件 2）                    *)
(*        == exp(zᐟ²)·exp(zᐟ²)（exp 加法性直连，无 sym）。           *)
(*   注：纯 real_eq 等式链，零 Or/序面触碰。                        *)
(* ============================================================ *)
Theorem upreq_exp_half_sq : forall x : Real,
  real_eq (cauchy_real_exp x)
          (real_mult (cauchy_real_exp (upreq_half x))
                     (cauchy_real_exp (upreq_half x))).
Proof.
  intro x.
  apply (real_eq_trans
          (cauchy_real_exp x)
          (cauchy_real_exp (real_plus (upreq_half x) (upreq_half x)))
          (real_mult (cauchy_real_exp (upreq_half x))
                     (cauchy_real_exp (upreq_half x)))).
  - exact (cauchy_real_exp_wd x (real_plus (upreq_half x) (upreq_half x))
             (real_eq_sym (real_plus (upreq_half x) (upreq_half x)) x
                (upreq_half_plus x))).
  - exact (cauchy_real_exp_plus (upreq_half x) (upreq_half x)).
Qed.

(* ============================================================ *)
(* 件 6（加餐·real_exp_neg 形，等式面）：e⁻ˣ == (e⁻ˣᐟ²)²             *)
(*   链：e⁻ˣ = exp(−x) == (exp(−xᐟ²))²（件 5 于 real_opp x 实例化，  *)
(*   LHS 经 real_exp_neg 定义 delta 折换）；右因子换位 exp(−xᐟ²) ==  *)
(*   e^{−(xᐟ²)}（wd 于件 3），双因子经 real_eq_mult_compat 合流。    *)
(*   五步链步骤3 依存位：eˣ := real_exp_neg (real_opp x) 项，再经    *)
(*   件 4 于参位 x 级联即得 eˣ == (eˣᐟ²)² 原生形（本件不代做，       *)
(* ============================================================ *)
Theorem upreq_exp_neg_half_sq : forall x : Real,
  real_eq (real_exp_neg x)
          (real_mult (real_exp_neg (upreq_half x))
                     (real_exp_neg (upreq_half x))).
Proof.
  intro x.
  apply (real_eq_trans
          (real_exp_neg x)
          (real_mult (cauchy_real_exp (upreq_half (real_opp x)))
                     (cauchy_real_exp (upreq_half (real_opp x))))
          (real_mult (real_exp_neg (upreq_half x))
                     (real_exp_neg (upreq_half x)))).
  - exact (upreq_exp_half_sq (real_opp x)).
  - apply (RealSetoid.real_eq_mult_compat
             (cauchy_real_exp (upreq_half (real_opp x)))
             (cauchy_real_exp (upreq_half (real_opp x)))
             (real_exp_neg (upreq_half x))
             (real_exp_neg (upreq_half x))).
    + exact (cauchy_real_exp_wd (upreq_half (real_opp x))
               (real_opp (upreq_half x)) (upreq_half_opp x)).
    + exact (cauchy_real_exp_wd (upreq_half (real_opp x))
               (real_opp (upreq_half x)) (upreq_half_opp x)).
Qed.

Print Assumptions upreq_half_plus.
