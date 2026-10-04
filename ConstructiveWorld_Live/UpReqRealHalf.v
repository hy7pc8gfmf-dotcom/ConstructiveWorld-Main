(* ============================================================
   UpReqRealHalf.v —— Real 层 halving 基建件（前缀 upreq_half 系）。
   ── 使命：eˣ>0 五步链步骤3（eˣ=(eˣᐟ²)²）的缺位补建——Real 层半元
   函数形。UpReqExpPos.v 头注步骤3 标注「halving 件库内缺位」，本件
   补建；步骤4（平方≥0 的 Or 形）属 LPO 等价面，本件零触碰：只做
   等式面（real_eq），不做 real_lt/real_le 面的平方非负陈述。
   ── 主定理：upreq_half_plus : forall x : Real,
   real_eq (real_plus (upreq_half x) (upreq_half x)) x。
   ── 路线：upreq_half x := real_mult (real_const (1#2)) x——
   real_mult 对 cauchy 序列封闭（S02 real_mult Defined 级收敛装配），
   良定义性直接继承；逐点投影 projT1 (upreq_half x) n == (1#2)·x_n；
   与原 Real 相等（real_eq 逐 eps）即主定理，取用 AttnSqrt 现成件
   sqrt_real_plus_half_half 一跳 exact（逐点 ½x_n+½x_n−x_n==0 经
   ring 判定，N:=0 全域生效）。库内另有 S08 real_half_plus_half
   （inv2 形），与本件 const(½) 形互为换位，不重复取用。
   ── 加餐（等式面）：upreq_exp_half_sq：eᶻ == (eᶻᐟ²)²；
   upreq_exp_neg_half_sq：e⁻ˣ == (e⁻ˣᐟ²)²（五步链步骤3 取用面：
   eˣ 项取 z := real_opp x 级联可达）；支撑件 upreq_half_opp、
   upreq_real_opp_opp（库内缺位补建）——均逐点 Q 环恒等 ring 判定。
   ── 依赖：AttnSqrt（sqrt_real_plus_half_half）；S02_CauchyComplete
   （Real/real_eq/real_plus/real_mult/real_const/real_opp 定义与投影
   件、real_eq_trans）；S03_QExp（cauchy_real_exp_plus／wd、
   real_exp_neg）；S07_RealSetoidExpLog（real_eq_mult_compat）；
   Stdlib QArith（QArith/Qabs）、Arith、Setoid、Morphisms。
   ── 构造性注记：Set 层语句（real_eq 为 Set 值；本件零 real_lt/
   real_le 面）；全 Qed 闭合；前缀 upreq_half 系防撞零占用；宿主件
   零改。
   ── 编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" UpReqRealHalf.v。
   ============================================================ *)

Require Import AttnSqrt.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete S03_QExp S07_RealSetoidExpLog.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 件 0（主件函数形）：Real 层半元函数                              *)
(*   upreq_half x := ½·x（常值序列 ½ 的乘法包装；逐项即 v_n=u_n/2）。 *)
(* ============================================================ *)
Definition upreq_half (x : Real) : Real := real_mult (real_const (1#2)) x.

(* ============================================================ *)
(* 件 1：逐点投影 projT1 (upreq_half x) n == ½·x_n                  *)
(*   （S02 三投影件直拼；供后续 ε 预算/界估计论证取用的独立锚）     *)
(* ============================================================ *)
Lemma upreq_half_proj : forall (x : Real) (n : nat),
  projT1 (upreq_half x) n == (1#2) * projT1 x n.
Proof.
  intros x n.
  unfold upreq_half.
  rewrite (real_mult_const_proj (1#2) x n).
  rewrite (real_const_proj (1#2) n).
  reflexivity.
Qed.

(* ============================================================ *)
(* 件 2（主定理）：加倍恒等 half x + half x == x                    *)
(*   取用 AttnSqrt sqrt_real_plus_half_half 一跳 exact（函数定义    *)
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
    - reflexivity. }
  apply Qlt_to_QltT.
  setoid_rewrite Habs0.
  apply QltT_to_Qlt. exact Heps.
Qed.

(* ============================================================ *)
(* 件 4：双重取反消去 real_opp (real_opp x) == x（库内缺位补建）    *)
(*   逐点：−(−x_n) − x_n == 0，ring 判定；N:=0 全域生效。           *)
(*   （eˣ 原生形 real_exp_neg (real_opp x) 与加餐件级联的运输基础）  *)
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
    - reflexivity. }
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
(*   五步链步骤3 取用位：eˣ := real_exp_neg (real_opp x) 项，再经    *)
(*   件 4 于参位 x 级联即得 eˣ == (eˣᐟ²)² 原生形（本件不代做，       *)
(*   留给后续件按其链位自行拼接）。                                   *)
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
