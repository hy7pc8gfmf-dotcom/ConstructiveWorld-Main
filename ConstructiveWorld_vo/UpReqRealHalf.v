
(* ============================================================ *)
(* UpReqRealHalf.v *)
(* *)
(* 目的： Real 层 halving 基建件。 *)
(* 主件： upreq_half 定义与 upreq_half_plus / upreq_half_opp / upreq_exp_half_sq 定律族。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 半元的良定义性由乘法直接继承，无需重证模数；柯西序列性质随承。 *)
(* 构造性注记：Set 层承载、零承认、可提取。 *)
(* 编译配方：rocq 9.1 直调 + cpu_guard。 *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                                *)
(* 定位：eˣ>0 五步链步骤3（eˣ=(eˣᐟ²)²）的缺位基础模块——Real 层半元    *)
(*   函数形。UpReqExpPos.v 头注步骤3 标注「halving 件库内缺位」，   *)
(*   本件零触碰：只做等式面（real_eq），不做 real_lt/real_le 面的   *)
(*   平方非负陈述，不做该等式的 Or/le 形应用。                     *)
(*                                                                *)
(* 主定理：upreq_half_plus : forall x : Real,                      *)
(*   real_eq (real_plus (upreq_half x) (upreq_half x)) x。          *)
(*                                                                *)
(* 路线裁决（候选路线A 与依存纪律⑤的合流）：                    *)
(*   路线A 的逐项半化 v_n := u_n/2 在本库的合法包装即              *)
(*   upreq_half x := real_mult (real_const (1#2)) x——real_mult 对  *)
(*   cauchy 序列封闭（S02 real_mult Defined 级收敛装配），「v 仍是  *)
(*   cauchy 序列」由 real_mult 的良定义性直接继承，无需重证模数    *)
(*   折半；逐点投影 projT1 (upreq_half x) n == (1#2)·x_n 由件 1    *)
(*   独立落件（S02 三投影件直拼）。（b）结果与原 Real 相等（real_eq  *)
(*   逐 eps）即主定理，依存 AttnSqrt 现成件 sqrt_real_plus_half_    *)
(*   half 一跳 exact（该件逐点证 ½x_n+½x_n−x_n==0 经 ring 判定，    *)
(*   N:=0 全域生效）。库内另有 S08 real_half_plus_half（inv2 形，   *)
(*   real_inv_pos 载体），与本件 const(½) 形互为换位，不重复依存。  *)
(*                                                                *)
(* 加餐（等式面，与步骤4 裁决不冲突）：                            *)
(*   件 5 upreq_exp_half_sq：eᶻ == (eᶻᐟ²)²（cauchy_real_exp 一般形）*)
(*   件 6 upreq_exp_neg_half_sq：e⁻ˣ == (e⁻ˣᐟ²)²（real_exp_neg 形，  *)
(*   即五步链步骤3 依存面：eˣ 项取 z := real_opp x 级联可达）。     *)
(*   支撑基础模块：件 3 upreq_half_opp（half 与 real_opp 交换）、       *)
(*   件 4 upreq_real_opp_opp（双重取反消去，库内缺位补建）——均      *)
(*   逐点 Q 环恒等 ring 判定，S02 投影件直拼。                     *)
(*                                                                *)
(* 库件依存清单（零新假设位）：                                    *)
(*   S02：Real/real_eq/real_plus/real_mult/real_const/real_opp 定  *)
(*   义，real_plus_proj/real_const_proj/real_mult_const_proj/      *)
(*   real_opp_proj、real_eq_trans。                                *)
(*   AttnSqrt：sqrt_real_plus_half_half（主定理依存位）。           *)
(*   S07（经 CW_ConstructiveWorld_219）：cauchy_real_exp_plus、     *)
(*   cauchy_real_exp_wd、real_exp_neg 定义、RealSetoid.            *)
(*   real_eq_mult_compat。                                         *)
(*                                                                *)
(* 红线自查：Set 层语句（real_eq 为 Set 值；本件零 real_lt/real_le  *)
(*   面）；Empty_set/Not 消去未用亦无需；全 Qed 闭合；前缀 upreq_   *)
(*   half/upreq_real_opp_opp/upreq_exp_half_sq/upreq_exp_neg_half_  *)
(*   sq 双树 grep 防撞零命中；既有文件零改，仅新建本件。            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219 AttnSqrt.
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
