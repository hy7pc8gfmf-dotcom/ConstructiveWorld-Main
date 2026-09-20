(* ============================================================ *)
(* PintPosGrid.v —— P1b 残面判定件：「段上逐点正 ⟹ 积分正」的否定性见证。 *)
(*                                                                     *)
(* 数学背景：一期 pint_integral = Σ a_k/(k+1) 恰为 [0,1] 上多项式的真    *)
(*   积分（线性泛函）；「系数任意但段上逐点正 ⟹ 积分正」对线性泛函一般   *)
(*   不真。本件给出显式二次多项式反例，将 P1b 的定位改判为               *)
(*   「命题本身需强化」。                                               *)
(*                                                                     *)
(* 反例（n=2）：pg_counterex(x) = −x² + x − 11/64                       *)
(*   = 1/64 + (3/4−x)(x−1/4)。                                        *)
(*   肢一（段上逐点正，带显式下界）：x ∈ [1/4,3/4] ⟹ 两因子非负，        *)
(*       pg_counterex(x) ≥ 1/64 > 0——平方差分解                         *)
(*       1/16−(x−1/2)² = (3/4−x)(x−1/4)，全程不依赖 ε-网格与有限和逼近； *)
(*   肢二（积分负）：∫₀¹ = −11/64 + 1/2 − 1/3 = −1/192 < 0。            *)
(*                                                                     *)
(* 结论：① P1b 原命题（段上逐点正 ⟹ 全积分正）为假，反例即肢一与肢二    *)
(*      的合取。其修正方向：                                            *)
(*      (a) 系数级分解：f = g + h、h 系数全非负 ⟹ ∫f ≥ ∫g               *)
(*          （一期 pint_integral_nonneg 与 P1 的 pm_pointwise_le_integral*)
(*          已全量覆盖）；                                              *)
(*      (b) Beta 闭式：I_n = ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} 的下界取        *)
(*          ∫₀¹ tⁿ(1−t)ⁿ = (n!)²/(2n+1)!，化为纯阶乘不等式，             *)
(*          不经段上逐点化；                                            *)
(*      ② 真方向：「全 [0,1] 逐点正 ⟹ 积分正」成立（连续 + 紧），其      *)
(*         构造性证明需 ε-网格有限和下界（未竟项，留待下界构造件）；      *)
(*      「Bernstein 系数全正（加系数正值条件）⟹ 积分正」为可判定的       *)
(*      充分条件（∫ΣbᵢBᵢ = (1/(n+1))Σbᵢ），需 mono↔Bernstein 基变换，    *)
(*      是 P1 件对任意系数多项式的真扩充方向。                           *)
(*                                                                     *)
(* 构造性注记：语句面全 Set（QleT'/QltT 与 Type 积 *，零 Prop 语句、     *)
(*   零 Prop 前提）；前提面仅 QleT' 段端点；证明面 Q 层结构化             *)
(*   （Qle_trans / Qplus_le_compat / Qmult_le_compat_r 两肢 + Qeq        *)
(*   setoid 换形，数值件 vm_compute）；提取面 eval/int 纯函数；          *)
(*   零承认、零经典逻辑；PolyIntegral 的 pint_ 接口只使用不重定义。      *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、PolyIntegral；Stdlib QArith、 *)
(*   Qabs、List、Arith、ZArith、Lia、Extraction。编译配方：coqc 9.1      *)
(*   直调无 -Q，cpu_guard 包裹，-o 临时目录（树内 .vo 不动）。           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs Lists.List Arith.Arith
               ZArith.ZArith Lia.
Import ListNotations.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import PolyIntegral.

(* ============================================================ *)
(* §1 内部支撑引理（Q 层，仅证明内使用） *)
(* ============================================================ *)

(* 非负两数之积非负（Qle 层；经 0·b 与 Qmult_le_compat_r 两步，
   与 PintMono 的 pm_mult_r0_le 同型） *)
Lemma pg_mult0 : forall a b : Q, Qle 0 a -> Qle 0 b -> Qle 0 (a * b).
Proof.
  intros a b Ha Hb.
  apply (Qle_trans 0 (0 * b) (a * b)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_r 0 a b).
    + exact Ha.
    + exact Hb.
Qed.

(* 右减端换形：x ≤ y ⟹ 0 ≤ y − x（Qplus_le_compat 双边形式配 Qplus_opp_r
   折叠左端；stdlib 本轨无单边 le_compat_r，故用双边对称构造） *)
Lemma pg_qle_minus_r : forall x y : Q, Qle x y -> Qle 0 (y - x).
Proof.
  intros x y H.
  apply (Qle_trans 0 (x + (- x)) (y + (- x))).
  - rewrite Qplus_opp_r. apply Qle_refl.
  - apply (Qplus_le_compat x y (- x) (- x)).
    + exact H.
    + apply Qle_refl.
Qed.

(* 数值引理：0 < 1/64（vm_compute 一步；同型于 S02 的 qltT_0_1） *)
Lemma pg_lt_1_64 : Qlt 0 (1 # 64).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 反例定义与恒等式 *)
(* ============================================================ *)

(* 反例多项式（pint 系数列表编码，头 = 常数项）：
   pg_counterex(x) = −11/64 + x·(1 + x·(−1)) = −x² + x − 11/64 *)
Definition pg_counterex : list Q := (- 11 # 64) :: (1 # 1) :: (- 1 # 1) :: nil.

(* 恒等式：pg_counterex(x) == 1/64 + (3/4−x)·(x−1/4)
   （平方差分解 1/16 − (x−1/2)² = (3/4−x)(x−1/4) 的应用形） *)
Lemma pg_counterex_eval_eq : forall x : Q,
  QeqT (pint_eval pg_counterex x) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
Proof.
  intros x. apply qeq_imp_qeqT. unfold pg_counterex. cbn [pint_eval]. ring.
Qed.

(* ============================================================ *)
(* §3 肢一：段上逐点正（显式正下界 1/64，强于原命题的严格正结论） *)
(* ============================================================ *)

(* 主件：x ∈ [1/4,3/4] ⟹ pg_counterex(x) ≥ 1/64（QleT' Set 面） *)
Theorem pg_counterex_seg_ge : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QleT' (1 # 64) (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HP : Qle 0 (((3 # 4) - x) * (x - (1 # 4)))).
  { apply pg_mult0.
    - apply pg_qle_minus_r. apply QleT'_to_Qle. exact Hhi.
    - apply pg_qle_minus_r. apply QleT'_to_Qle. exact Hlo. }
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qle_to_QleT'.
  rewrite HE.
  apply (Qle_trans (1 # 64) ((1 # 64) + 0) ((1 # 64) + ((3 # 4) - x) * (x - (1 # 4)))).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat (1 # 64) (1 # 64) 0
                           (((3 # 4) - x) * (x - (1 # 4)))).
    + apply Qle_refl.
    + exact HP.
Qed.

(* 原命题同形件：x ∈ [1/4,3/4] ⟹ pg_counterex(x) > 0（QltT Set 面） *)
Theorem pg_counterex_seg_pos : forall x : Q,
  QleT' (1 # 4) x -> QleT' x (3 # 4) ->
  QltT 0 (pint_eval pg_counterex x).
Proof.
  intros x Hlo Hhi.
  assert (HE : pint_eval pg_counterex x == (1 # 64) + ((3 # 4) - x) * (x - (1 # 4))).
  { apply qeqT_imp_qeq. apply pg_counterex_eval_eq. }
  apply Qlt_to_QltT.
  rewrite HE.
  apply (Qplus_lt_le_compat 0 (1 # 64) 0 (((3 # 4) - x) * (x - (1 # 4)))).
  - apply pg_lt_1_64.
  - apply pg_mult0.
    + apply pg_qle_minus_r. apply QleT'_to_Qle. exact Hhi.
    + apply pg_qle_minus_r. apply QleT'_to_Qle. exact Hlo.
Qed.

(* ============================================================ *)
(* §4 肢二：积分负（封闭计算：∫ = −1/192 < 0） *)
(* ============================================================ *)

Theorem pg_counterex_int_neg : QltT (pint_integral pg_counterex) 0.
Proof.
  unfold pg_counterex, pint_integral. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §5 否定性见证的合取（Set 面 Type 积：两肢并列构成 P1b 原命题反例） *)
(*                                                               *)
(*   pg_P1b_counterexample 的存在 ⟹ 「段上逐点正 ⟹ 积分正」原命题     *)
(*   不可能成立——任何该形构造作用于 pg_counterex 即与肢二矛盾。 *)
(*   P1b 定位改判为「命题需强化」（修正方向见文件头）。 *)
(* ============================================================ *)

Definition pg_P1b_death_certificate : Set :=
  (forall x : Q, QleT' (1 # 4) x -> QleT' x (3 # 4) ->
     QltT 0 (pint_eval pg_counterex x))
  * QltT (pint_integral pg_counterex) 0.

Theorem pg_P1b_counterexample : pg_P1b_death_certificate.
Proof.
  split.
  - apply pg_counterex_seg_pos.
  - exact pg_counterex_int_neg.
Qed.

(* ============================================================ *)
(* 提取与假设审计（编译期输出） *)
(* ============================================================ *)

Extraction "pintposgrid_extract.ml"
  pg_counterex pg_counterex_seg_ge pg_counterex_seg_pos
  pg_counterex_int_neg pg_P1b_counterexample.

Print Assumptions pg_counterex_seg_ge.
Print Assumptions pg_counterex_seg_pos.
Print Assumptions pg_counterex_int_neg.
Print Assumptions pg_P1b_counterexample.
