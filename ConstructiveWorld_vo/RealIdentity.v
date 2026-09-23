(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ri_x_eq_pn_qn（原 L83，4 句玩具证）                                  *)
(*   ri_real_proj（原 L76，2 句玩具证）                                   *)
(* ============================================================ *)

(* ============================================================ *)
(* RealIdentity.v —— 本件形式化 ln2 逼近恒等式的实数层语句化与装配：          *)
(*   I_n := ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt = 2^{n+1}·q̃_n·ln2 − r_n，          *)
(*   ln2 − x'_n = I_n/(2^{n+1}·q̃_n)，x'_n == p_n/q̃_n == tn_x n == bv_x n；   *)
(*   X := ln2i_x 的柯西极限（ri_real）。恒等式的实数层语句：                  *)
(*   real_eq (real_metric X (real_const x'_n)) (I_n/(2^{n+1}·q̃_n))。          *)
(*                                                                          *)
(* 范围注记：I_n 的实数承载以输入接口 ri_Iface 条件供给（I_n 本体积分面       *)
(*   ——部分分式分解或级数尾几何界——尚在库外，为后续工作）；正性面不在        *)
(*   本件范围，本件只做等式与上界两面。                                       *)
(*                                                                          *)
(* 主要结果：                                                                *)
(*   ri_real / ri_x：ln2i_x 实数承载 + x'_n := p_n/q̃_n 的 Q 常数实嵌入；      *)
(*   ri_x_eq_tn：ri_x n == tn_x n（经 tn_x_eq_bv_x）；                        *)
(*   ri_metric / ri_metric_proj：proj == |ln2i_x k − x'_n|（度量面）；        *)
(*   ri_qnorm / ri_cx_eq_r / ri_core_pt：归一因子 c_n := 2^{n+1}·q̃_n 与       *)
(*     核心代数 c_n·|X_k − x'_n| == |c_n·X_k − r_n|（逐点精确，纯 Q 层）；     *)
(*   ri_identity_leg / ri_identity_spec / ri_identity_assembly：目标恒等式    *)
(*     的条件形语句与装配——ri_identity_leg（Ireal_n == |c_n·X − r_n|）       *)
(*     一经供给，|X − x'_n| == Ireal_n/c_n 随 eps 判据即实例化消解；                *)
(*   ri_upper_transfer：上界面转移——Ireal_n/c_n ≤ θ^n ⟹ |X − x'_n| ≤ θ^n；   *)
(*   ri_lineabs / ri_metric_line_scale：lineabs_n == c_n·metric_n 逐点成立，  *)
(*     即 supply 面（clo/θ 判据）的逐点输入形（接口登记）。                   *)
(*                                                                          *)
(* 锚组：c_1 = 12、c_2·x'_2 == r_2 = 72、|X_5 − x'_1| = 7/320 与             *)
(*   线面 21/80 = 12·(7/320) 的比例双锚。                                    *)
(*                                                                          *)
(* 后续工作登记：x' 族的整数 supply 实例化缺口——真分子 p_n 自 n=3 起         *)
(*   本质有理，ln2i_pade_supply 的整数系数线面需先做整数重整（另案）。        *)
(*                                                                          *)
(* 构造性注记：全件 Qed、零承认；语句面全 Set（QeqT/real_eq/real_le/sigT）；  *)
(*   证内推理面仅服务 Q 层推理，零前提残留；可提取；                          *)
(*   文末 Print Assumptions 复核。                                           *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp                             *)
(*   + UpReqIrrationalCriterion（lic_metric_proj/lic_seq_cauchy）             *)
(*   + UpReqLn2Irrational（ln2i_x/e/tail/vanish）                             *)
(*   + BeukersLists BeukersVariant TrueNumerator。                            *)
(*                                                                          *)
(* 编译配方：coqc 9.1 直调（无 -Q），cpu_guard 包裹，-o 输出临时目录，         *)
(*   树内 .vo 不重写。                                                       *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(*                                                                          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqIrrationalCriterion UpReqLn2Irrational.
Require Import BeukersLists BeukersVariant TrueNumerator.

Open Scope nat_scope.

(* ============================================================ *)
(* §A real 承载与 x'_n 语句化（Q 常数实嵌入）                             *)
(* ============================================================ *)

(* ln2 实数承载：ln2i_x 的柯西极限（尾控与消失两肢由源模块供给；
   与 Ln2Bridge.ln2b_X 同一定义面，独立命名以免跨文件重名） *)
Definition ri_real : Real :=
  existT (fun u : Qseq => cauchy u) ln2i_x
    (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish).

Lemma ri_real_proj : forall k : nat, projT1 ri_real k == ln2i_x k.
Proof. intro k. exact (Qeq_refl (ln2i_x k)). Qed.

(* ri_x：x'_n := p_n/q̃_n（即 bv_x；Q 常数，待 real_const 实嵌入） *)
Definition ri_x (n : nat) : Q := bv_x n.

(* ri_x_eq_pn_qn：ri_x n == bv_p n / q̃_n *)
Lemma ri_x_eq_pn_qn : forall n : nat,
  QeqT (ri_x n) (bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  unfold ri_x, bv_x.
  apply qeq_imp_qeqT.
  exact (Qeq_refl (bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)).
Qed.

(* ri_x_eq_tn：ri_x n == tn_x n（由 tn_x_eq_bv_x 经 Qeq 桥反接） *)
Lemma ri_x_eq_tn : forall n : nat, QeqT (ri_x n) (tn_x n).
Proof.
  intro n. unfold ri_x. apply qeq_imp_qeqT. symmetry.
  apply qeqT_imp_qeq. apply tn_x_eq_bv_x.
Qed.

(* ============================================================ *)
(* §B 归一因子面：c_n := 2^{n+1}·q̃_n                                     *)
(* ============================================================ *)

Definition ri_qnorm (n : nat) : Q :=
  (q_pow (2 # 1)%Q (Datatypes.S n) * (Z.of_nat (bk_Qn_qtilde n) # 1)%Q)%Q.

Lemma ri_pow3_ge1 : forall n : nat, (1 <= 3 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - cbn. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma ri_qtilde_ge1 : forall n : nat, (1 <= bk_Qn_qtilde n)%nat.
Proof.
  intro n. pose proof (bk_Qn_ge_3pow_nat n) as H3.
  pose proof (ri_pow3_ge1 n) as H1. lia.
Qed.

Lemma ri_qtilde_pos : forall n : nat, Qlt 0 ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. unfold Qlt. cbn [Qnum Qden].
  pose proof (proj1 (Nat2Z.inj_le 1 (bk_Qn_qtilde n)) (ri_qtilde_ge1 n)) as Hz.
  lia.
Qed.

Lemma ri_qtilde_ne0 : forall n : nat,
  ~ ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q == 0%Q).
Proof.
  intros n Hc. unfold Qeq in Hc. cbn [Qnum Qden] in Hc.
  pose proof (proj1 (Nat2Z.inj_le 1 (bk_Qn_qtilde n)) (ri_qtilde_ge1 n)) as Hz.
  lia.
Qed.

Lemma ri_qpow2_pos : forall k : nat, Qlt 0 (q_pow (2 # 1)%Q k).
Proof.
  induction k as [| k IH].
  - unfold Qlt. cbn [q_pow Qnum Qden]. lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat.
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

Lemma ri_qnorm_pos : forall n : nat, Qlt 0 (ri_qnorm n).
Proof.
  intro n. unfold ri_qnorm. apply Qmult_lt_0_compat.
  - apply ri_qpow2_pos.
  - apply ri_qtilde_pos.
Qed.

Lemma ri_qnorm_ne0 : forall n : nat, ~ (ri_qnorm n == 0%Q).
Proof.
  intros n Hc. unfold ri_qnorm in Hc.
  apply (Qmult_integral _ _) in Hc. destruct Hc as [H1 | H2].
  - exact (tn_qpow2_ne (Datatypes.S n) H1).
  - exact (ri_qtilde_ne0 n H2).
Qed.

(* ============================================================ *)
(* §C 度量面（lic_metric_proj 投影）+ 线面 + 逐点精确代数核                  *)
(* ============================================================ *)

(* ri_metric：real_metric ri_real (real_const x'_n) 的投影对象 *)
Definition ri_metric (n : nat) : Real :=
  real_metric ri_real (real_const (ri_x n)).

Lemma ri_metric_proj : forall (n k : nat),
  projT1 (ri_metric n) k == Qabs ((ln2i_x k - ri_x n)%Q).
Proof.
  intros n k. unfold ri_metric.
  rewrite lic_metric_proj. rewrite ri_real_proj. reflexivity.
Qed.

(* ri_lineabs：线面 |c_n·X − r_n|（I_n 的实数面逐点语义；
   有理常数版——supply 整系数线面的 p_n/q̃_n 归一对照形，见 §E） *)
Definition ri_lineabs (n : nat) : Real :=
  real_abs (real_plus (real_mult (real_const (ri_qnorm n)) ri_real)
                      (real_opp (real_const (tn_r n)))).

Lemma ri_lineabs_proj : forall (n k : nat),
  projT1 (ri_lineabs n) k == Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q).
Proof.
  intros n k. unfold ri_lineabs.
  rewrite real_abs_proj, real_plus_proj, real_mult_const_proj, real_opp_proj,
          real_const_proj, ri_real_proj.
  reflexivity.
Qed.

(* 归一乘法闭合：c_n·x'_n == r_n（x'_n = r_n/c_n 的 Q 层定形） *)
Lemma ri_cx_eq_r : forall n : nat, (ri_qnorm n * ri_x n)%Q == tn_r n.
Proof.
  intro n. unfold ri_qnorm, ri_x, bv_x, Qdiv.
  transitivity (q_pow (2 # 1)%Q (Datatypes.S n)
                * (bv_p n * ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q
                             * Qinv ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q))))%Q.
  - ring.
  - rewrite (Qmult_inv_r (Z.of_nat (bk_Qn_qtilde n) # 1)%Q (ri_qtilde_ne0 n)).
    rewrite Qmult_1_r. reflexivity.
Qed.

(* ri_core_pt（纯 Q 层，逐点精确）：c_n·|X_k − x'_n| == |c_n·X_k − r_n|
   ——修正恒等式实数层的代数本体（等式面的核心） *)
Lemma ri_core_pt : forall (n k : nat),
  (ri_qnorm n * Qabs ((ln2i_x k - ri_x n)%Q))%Q
  == Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q).
Proof.
  intros n k.
  assert (Hsplit : Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q)
                   == Qabs ((ri_qnorm n * (ln2i_x k - ri_x n))%Q)).
  { rewrite <- (ri_cx_eq_r n). apply Qabs_wd. unfold Qminus. ring. }
  rewrite Hsplit.
  rewrite (Qabs_Qmult (ri_qnorm n) (ln2i_x k - ri_x n)%Q).
  rewrite (Qabs_pos (ri_qnorm n) (Qlt_le_weak 0%Q (ri_qnorm n) (ri_qnorm_pos n))).
  reflexivity.
Qed.

(* ri_metric_line_scale：线面 == c_n·度量面（逐点；supply 输入形） *)
Lemma ri_metric_line_scale : forall (n k : nat),
  projT1 (ri_lineabs n) k == (ri_qnorm n * projT1 (ri_metric n) k)%Q.
Proof.
  intros n k. rewrite ri_lineabs_proj. rewrite ri_metric_proj.
  symmetry. apply ri_core_pt.
Qed.

(* ============================================================ *)
(* §D 目标恒等式的实数层语句（条件形）与装配：ri_identity_assembly         *)
(* ============================================================ *)

(* ri_Iface：I_n 侧实数面输入形（nat → Real）；
   I_n 本体积表面（部分分式分解）尚在库外，见文件头范围注记 *)
Definition ri_Iface : Set := nat -> Real.

(* ri_identity_leg（输入面）：Ireal_n == |c_n·X − r_n| == I_n（实数层） *)
Definition ri_identity_leg (Ireal : ri_Iface) : Set :=
  forall n : nat, real_eq (Ireal n) (ri_lineabs n).

(* ri_identity_spec（目标恒等式）：
   real_metric X (real_const x'_n) == I_n/(2^{n+1}·q̃_n)（实数层） *)
Definition ri_identity_spec (Ireal : ri_Iface) : Set :=
  forall n : nat,
    real_eq (ri_metric n)
            (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n)))).

(* ri_eps_core（纯 Q 层支撑）：c·m == L、0 < c、|I − L| < c·eps
   ⟹ |m − I·c⁻¹| < eps（恒等式装配的全部剩余代数） *)
Lemma ri_eps_core : forall c m I L eps : Q,
  (c * m == L)%Q -> Qlt 0 c -> Qlt (Qabs (I - L)) (c * eps)%Q ->
  Qlt (Qabs (m - I * Qinv c)%Q) eps.
Proof.
  intros c m I L eps Hcm Hc Hlt.
  assert (Hc0 : ~ (c == 0%Q)).
  { intro Hz. apply (Qlt_not_eq 0%Q c Hc).
    apply Qeq_sym. exact Hz. }
  assert (Hinv : (c * Qinv c)%Q == 1%Q) by (apply Qmult_inv_r; exact Hc0).
  assert (Hic0 : Qlt 0 (Qinv c)) by (apply Qinv_lt_0_compat; exact Hc).
  assert (Hs : (m - I * Qinv c)%Q == ((L - I) * Qinv c)%Q).
  { assert (HmL : (L * Qinv c)%Q == m%Q).
    { rewrite <- Hcm. transitivity (m * (c * Qinv c))%Q.
      - ring.
      - rewrite Hinv. apply Qmult_1_r. }
    unfold Qminus. rewrite <- HmL. ring. }
  rewrite Hs. rewrite Qabs_Qmult. rewrite (Qabs_Qminus L I).
  assert (Habs : Qabs (Qinv c) == Qinv c)
    by (apply Qabs_pos; apply Qlt_le_weak; exact Hic0).
  rewrite Habs.
  assert (Hstep : (c * eps * Qinv c)%Q == eps%Q).
  { transitivity (eps * (c * Qinv c))%Q.
    - ring.
    - rewrite Hinv. apply Qmult_1_r. }
  rewrite <- Hstep.
  apply (Qmult_lt_compat_r (Qabs (I - L)) (c * eps)%Q (Qinv c) Hic0).
  exact Hlt.
Qed.

(* ri_identity_assembly：Ireal 输入面一经供给，目标恒等式实数层实例化消解。
   路径：逐点核（ri_core_pt 精确）+ 输入面 eps 读数除以 c_n。
   （QltT 目标先降为 Qlt 推理面再改写，lic_tail_e 同款写法） *)
Theorem ri_identity_assembly : forall Ireal : ri_Iface,
  ri_identity_leg Ireal -> ri_identity_spec Ireal.
Proof.
  intros Ireal Hleg n eps Heps.
  assert (Hce : QltT 0 ((ri_qnorm n * eps)%Q)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply ri_qnorm_pos.
    - apply QltT_to_Qlt. exact Heps. }
  destruct (Hleg n ((ri_qnorm n * eps)%Q) Hce) as [N HN].
  exists N. intros k Hk.
  pose proof (QltT_to_Qlt _ _ (HN k Hk)) as HNk.
  apply Qlt_to_QltT.
  rewrite ri_metric_proj.
  rewrite real_mult_proj, real_const_proj.
  apply (ri_eps_core (ri_qnorm n) (Qabs ((ln2i_x k - ri_x n)%Q))
                     (projT1 (Ireal n) k) (projT1 (ri_lineabs n) k) eps).
  - transitivity (Qabs ((ri_qnorm n * ln2i_x k - tn_r n)%Q)).
    + apply ri_core_pt.
    + symmetry. apply ri_lineabs_proj.
  - apply ri_qnorm_pos.
  - exact HNk.
Qed.

(* ============================================================ *)
(* §E supply 接口对齐（接口登记）                                         *)
(* ============================================================ *)
(* 接口事实：ln2b_delta_of_supply 的 real_metric 面所需形式为              *)
(*   |A_n·X − B_n|（ln2b_line，A B : nat -> Z 整系数）。装配件输出          *)
(*   （度量面 ri_metric + 归一因子 ri_qnorm + 有理常数线面 ri_lineabs）     *)
(*   经 ri_metric_line_scale 恰为其逐点缩放像：                            *)
(*     lineabs_n == c_n·metric_n（逐点精确），                            *)
(* 即 supply 面 clo/θ 判据（clo_n ≤ |A_n X − B_n| ≤ θ^n）的输入形可从装配   *)
(* 输出逐点直读。后续工作：x' 族的 B_n := p_n 自 n=3 起非整（整性事实       *)
(*   见 TrueNumerator 文件头），整系数重整是 supply 实例化的前置工作；       *)
(* A/B 整化与 supply 装配另案。                                          *)

(* ri_upper_transfer（上界面转移）：Ireal_n/c_n ≤ θ^n ⟹ |X − x'_n| ≤ θ^n
   （real_eq 经右支入 real_le + real_le 传递——supply 上界判据的输入形） *)
Theorem ri_upper_transfer : forall (Ireal : ri_Iface) (th : Q),
  ri_identity_spec Ireal ->
  (forall n : nat, real_le (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n))))
                           (real_const (q_pow th n))) ->
  forall n : nat, real_le (ri_metric n) (real_const (q_pow th n)).
Proof.
  intros Ireal th Hspec Hup n.
  apply (real_le_trans (ri_metric n)
          (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n))))
          (real_const (q_pow th n))).
  - right. exact (Hspec n).
  - exact (Hup n).
Qed.

(* ============================================================ *)
(* §F 数值锚组（各锚由 vm_compute 经投影引理精确判定）                       *)
(* ============================================================ *)

(* 归一因子锚：c_1 = 2²·q̃_1 = 4·3 = 12 *)
Theorem ri_qnorm1_anchor : QeqT (ri_qnorm 1) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* r 族锚：c_2·x'_2 == r_2 = 72 *)
Theorem ri_cx2_anchor : QeqT ((ri_qnorm 2 * ri_x 2)%Q) (72 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* 度量面锚：|X_5 − x'_1| == |661/960 − 2/3| == 7/320（X_k := ln2i_x k） *)
Theorem ri_metric15_anchor : QeqT (projT1 (ri_metric 1) 5) (7 # 320)%Q.
Proof.
  apply qeq_imp_qeqT. rewrite ri_metric_proj. vm_compute. reflexivity.
Qed.

(* 线面锚：|c_1·X_5 − r_1| == |12·(661/960) − 8| == 21/80 = 12·(7/320)
   ——与度量面锚构成 ri_core_pt 比例双锚（c_1 = 12） *)
Theorem ri_lineabs15_anchor : QeqT (projT1 (ri_lineabs 1) 5) (21 # 80)%Q.
Proof.
  apply qeq_imp_qeqT. rewrite ri_lineabs_proj. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。          *)
(* ============================================================ *)

Print Assumptions ri_x_eq_tn.
Print Assumptions ri_core_pt.
Print Assumptions ri_identity_assembly.
Print Assumptions ri_upper_transfer.
Print Assumptions ri_metric15_anchor.
