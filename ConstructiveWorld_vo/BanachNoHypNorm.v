(* ============================================================ *)
(* BanachNoHypNorm.v —— INSTB 未消解项①剩余字段位                  *)
(* 使命: 补齐 E-载体范数字段 bnorm_plus/bnorm_mult（次可加/次可乘），  *)
(*   收束 UpReqBanachInstB 未消解项①剩余位（乘法群四面已由            *)
(*   UpReqBanachInstEMult 之 bxem_mult_assoc/one_l/one_r/              *)
(*   distrib_l/distrib_r 闭合）。                                      *)
(* 技术: E-载体 bxib_E 上 bnorm := Qabs ∘ qnorm ∘ ev；运算位 ev 按定义  *)
(*   已带一层 qnorm，字段位左端现双层 qnorm——先 bxib_qnorm_fix_id      *)
(*   （Id 不动点）退化为单层，再落 Qle 引擎内衬层用 stdlib Qabs 引擎   *)
(*   （Qabs_triangle/Qabs_Qmult/Qabs_wd ＋ Qplus_comp/Qmult_comp）     *)
(*   ＋ qeq_le 运输组装，末级 Qle_to_QleT' 回 Set 面。注：Qabs         *)
(*   (qnorm t) 与 Qabs t 的 Leibniz 等式被 bxib_canon_pin_wall 阻断，  *)
(*   故退化与换形全走 Qeq/QeqT/Id-不动点面（与该阻碍正交）。           *)
(* 构造性（自审）: 语句面全 Set 层（QleT' 承载序，Qle/Qeq 仅引擎内衬，  *)
(*   零 Prop 泄露）；全件 Qed 真证、零承认语句；提取检验 Obj.magic=0；  *)
(*   Print Assumptions 全件 Closed。前缀 bnhn_ 全库零撞名。            *)
(* 依赖清单: S01_BaseRing、S02_CauchyComplete、UpReqBanachInstB；      *)
(*   Stdlib QArith.QArith、QArith.Qabs、Arith.Arith、Lia、Extraction。 *)
(* 编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树  *)
(*   同世界重编），COQLIB/ROCQLIB 全字面环境前缀。                     *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* 件一：bnorm_plus 字段位（次可加）——                               *)
(*   QleT' (bnorm (eplus a b)) (bnorm a + bnorm b)                  *)
(*   （类字段 bnorm_plus 在 E-载体 bxib_E 上的同位定理；双层 qnorm    *)
(*     退化 + Qabs_triangle 三段运输。）                             *)
(* ============================================================ *)

Lemma bnhn_bnorm_plus : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_eplus a b))
        (bxib_bnorm a + bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_eplus a b))
    with (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))).
  (* 双层 qnorm 退化（Id 不动点，QleT' 目标内 Leibniz 改写合法位） *)
  rewrite (bxib_qnorm_fix_id (Qplus (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a + bxib_ev b)%Q) _).
  - (* 左端换形：|qnorm (x+y)| ≤ |x+y|（Qeq 运输，非钉定位） *)
    apply qeq_le.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a + bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q + Qabs (bxib_ev b)%Q)%Q _).
    + (* 三角不等式（stdlib Qabs_triangle） *)
      apply Qabs_triangle.
    + (* 右端换形：|x|+|y| ≤ |qnorm x|+|qnorm y|
         （Qplus_comp Proper 项式：x x' Hx y y' Hy 交错参序） *)
      apply qeq_le.
      exact (Qplus_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* ============================================================ *)
(* 件二：bnorm_mult 字段位（次可乘）——                               *)
(*   QleT' (bnorm (emult a b)) (bnorm a * bnorm b)                  *)
(*   （类字段 bnorm_mult 在 E-载体 bxib_E 上的同位定理；退化同款 +    *)
(*     Qabs_Qmult 等式换形（Qeq 强于 Qle 经 qeq_le 降取）。）         *)
(* ============================================================ *)

Lemma bnhn_bnorm_mult : forall a b : bxib_E,
  QleT' (bxib_bnorm (bxib_emult a b))
        (bxib_bnorm a * bxib_bnorm b)%Q.
Proof.
  intros a b. unfold bxib_bnorm.
  change (bxib_ev (bxib_emult a b))
    with (bxib_qnorm (Qmult (bxib_ev a) (bxib_ev b))).
  rewrite (bxib_qnorm_fix_id (Qmult (bxib_ev a) (bxib_ev b))).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxib_ev a * bxib_ev b)%Q) _).
  - (* 左端换形：|qnorm (x*y)| ≤ |x*y| *)
    apply qeq_le.
    exact (Qabs_wd _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a * bxib_ev b)%Q))).
  - apply (Qle_trans _ (Qabs (bxib_ev a)%Q * Qabs (bxib_ev b)%Q)%Q _).
    + (* |x*y| == |x|·|y|（stdlib Qabs_Qmult，Qeq 经 qeq_le 降取 Qle） *)
      apply qeq_le. apply Qabs_Qmult.
    + (* 右端换形：|x|·|y| ≤ |qnorm x|·|qnorm y|
         （Qmult_comp Proper 项式：x x' Hx y y' Hy 交错参序） *)
      apply qeq_le.
      exact (Qmult_comp (Qabs (bxib_ev a)%Q) (Qabs (bxib_qnorm (bxib_ev a)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev a)))))
               (Qabs (bxib_ev b)%Q) (Qabs (bxib_qnorm (bxib_ev b)))
               (Qabs_wd _ _ (Qeq_sym _ _ (qeqT_imp_qeq _ _ (bxib_qnorm_fix (bxib_ev b)))))).
Qed.

(* ============================================================ *)
(* 核验记录（对称申报，不落承认件面）：                             *)
(*   ① 本件即 INSTB 未消解项① 的闭合件：乘法群四面（bxem_ 系）+    *)
(*     bnorm_plus/bnorm_mult（本件 bnhn_）全数补齐，E-载体对冻结类     *)
(*     代数/范数字段位无剩余缺口（完备性字段照 INS 先例另列，        *)
(*     bnorm_coef 钉定语句面修订属上游改形——两处维持原未消解项状态）。 *)
(*   ② 伴随注：bxem_mult 与 bxib_emult 为 delta 同一定义              *)
(*     （bxem_mult a b := bxib_emult a b），本件语句面取构造子直形。   *)
(*   ③ 退化机同源性：本件双层退化 = bxem_mult_wd 同款                 *)
(*     （fix_id → qnorm_id_of_qeqT → fix_id 链的 QleT' 版），          *)
(*     序面用 Qabs_triangle/Qabs_Qmult 替 bxem 的 qeqT cong 位。       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction bnhn_bnorm_plus bnhn_bnorm_mult.

Print Assumptions bnhn_bnorm_plus.
Print Assumptions bnhn_bnorm_mult.
