(* ============================================================ *)
(* RealIdentity.v —— 切片代理D038（批次 E-STAGING-D038，20260919）      *)
(* 卡点 (c) 实数层装配切片（ri_ 前缀）。                                 *)
(*                                                                 *)
(* 【使命定谳面】D016 卡点 (c)「real 层装配（ln2i_x 消费）另案」与        *)
(* D021 剩余路径 (a)「恒等式本体语句化需实数层 ln2」由本席落位：           *)
(*   D016 修正恒等式（手算 n=0,1,2 勘误后真形）：                         *)
(*     I_n := ∫₀¹ tⁿ(1−t)ⁿ/(1−t/2)^{n+1} dt = 2^{n+1}·q̃_n·ln2 − r_n,   *)
(*     ln2 − x'_n = I_n/(2^{n+1}·q̃_n)，其中 x'_n = r_n/(2^{n+1}q̃_n)     *)
(*     == p_n/q̃_n == tn_x n == bv_x n（D026r tn_x_eq_bv_x 一般桥）。    *)
(*   本席给出该恒等式的 real 层语句化 + 真证装配：                          *)
(*     real_eq (real_metric X (real_const x'_n)) (I_n/(2^{n+1}q̃_n))，  *)
(*   其中 X := lim ln2i_x（ln2i 实数承载），I_n 侧以 real 面 Ireal 输入     *)
(*   （条件形——I_n 本体积分面在库外，D016 (a) 部分分式机挂账），             *)
(*   正性腿不碰（遵任务书定向），只做等式/上界两腿。                        *)
(*                                                                 *)
(* 【交付面（全 Qed 零承认）】                                           *)
(*  ① ri_real / ri_x：ln2i_x 实数承载 + x'_n := p_n/q̃_n 的 Q 常数        *)
(*     实嵌入语句面；ri_x_eq_tn 消费 D026r tn_x_eq_bv_x（Qeq 桥反接）；   *)
(*  ② ri_metric / ri_metric_proj：lic_metric_proj 投影到 ri_real 度量    *)
(*     面：proj == |ln2i_x k − x'_n|（使命①度量面）；                   *)
(*  ③ ri_qnorm / ri_cx_eq_r / ri_core_pt：归一因子 c_n := 2^{n+1}·q̃_n   *)
(*     面与核心代数 c·|X_k − x'_n| == |c·X_k − r_n|（逐点精确，纯 Q 层）；*)
(*  ④ ri_identity_leg / ri_identity_spec / ri_identity_assembly：        *)
(*     目标恒等式 real 层语句化（条件形）+ eps 机真证装配（使命②等式腿）   *)
(*     ——Ireal 输入腿 Ireal_n == |c_n·X − r_n| 一旦供给（I_n 实数面），   *)
(*     恒等式 |X − x'_n| == Ireal_n/c_n 即放电；                        *)
(*  ⑤ ri_upper_transfer：supply θ 腿转移件（使命②上界腿）：              *)
(*     Ireal_n/c_n ≤ θ^n ⟹ |X − x'_n| ≤ θ^n（real_le 传递 + eq 直入）；  *)
(*  ⑥ ri_lineabs / ri_metric_line_scale：supply 接口对齐读取器（使命③）   *)
(*     ——lineabs_n == c_n·metric_n 逐点：装配件输出（度量面 + 归一因子 +  *)
(*     线面）即 ln2i_pade_supply clo/θ 腿的逐点输入形（接口注释级登记，    *)
(*     不抢 D034 在飞 sa_ 总装面，见 §E 判词）；                        *)
(*  ⑦ 锚组：c_1 = 12、c_2·x'_2 == r_2 = 72（D016 r 族对账）、            *)
(*     |X_5 − x'_1| = 7/320 与线面 21/80 = 12·(7/320) 比例双锚。          *)
(*                                                                 *)
(* 【诚实降档登记（禁虚报）】                                            *)
(*   (i) 恒等式本体是条件形：I_n 的实数面（积分承载 / 级数极限实数化）      *)
(*       依赖 D016 (a) 部分分式机或 D021 级数尾几何界 Cauchy 机——两者皆   *)
(*       在库外，本席如实以 ri_identity_leg 输入腿挂账，装配件真证；        *)
(*   (ii) x' 族整系数 supply 实例化缺口（真分子 p_n 自 n=3 起本质有理，    *)
(*       D026r 整性预判）：ln2i_pade_supply 的 A/B 腿需 nat->Z，而        *)
(*       B_n := p_n 非整——整数重整是 supply 插槽的前置战役，本席仅做       *)
(*       接口注释级登记，不实装。                                      *)
(*                                                                 *)
(* 红线自审：① 零承认面（全件 Qed，依赖全在册）；                        *)
(*   ② 语句面全 Set（QeqT/real_eq/real_le/sigT；证内 Prop（Qlt/Qle）     *)
(*      仅作 Q 层推理脚手架，零泄露位、零前提挂脖）；                     *)
(*   ③ 非平凡（eps 机装配 + 逐点精确代数核 + real_le/eq 传递转移件）；     *)
(*   ④ 可提取（G3 探针独立文件实测，Obj.magic 计数=0）。                 *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp                       *)
(*   + UpReqIrrationalCriterion（lic_metric_proj/lic_seq_cauchy 投影面） *)
(*   + UpReqLn2Irrational（ln2i_x/e/tail/vanish 承载）                   *)
(*   + BeukersLists BeukersVariant TrueNumerator（bv_p/bv_x/q̃ 面 +       *)
(*     tn_r/tn_qpow2_ne/tn_x_eq_bv_x 定谳桥）。零云端零 git。            *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqIrrationalCriterion UpReqLn2Irrational.
Require Import BeukersLists BeukersVariant TrueNumerator.

Open Scope nat_scope.

(* ============================================================ *)
(* §A real 承载与 x'_n 语句化（使命①：Q 常数实嵌入 + D026r 消费）           *)
(* ============================================================ *)

(* ln2 实数承载：ln2i_x 的柯西极限（尾控+消失双腿由母件供给；
   与 Ln2Bridge.ln2b_X 同一定义面——本席独立命名免跨文件抢线） *)
Definition ri_real : Real :=
  existT (fun u : Qseq => cauchy u) ln2i_x
    (lic_seq_cauchy ln2i_x ln2i_e ln2i_tail ln2i_vanish).

Lemma ri_real_proj : forall k : nat, projT1 ri_real k == ln2i_x k.
Proof. intro k. reflexivity. Qed.

(* x'_n := p_n/q̃_n（bv_x 定形直载——Q 常数，待 real_const 实嵌入） *)
Definition ri_x (n : nat) : Q := bv_x n.

(* 定形展开面：ri_x n 就是 bv_p n / q̃_n（语句面登记） *)
Lemma ri_x_eq_pn_qn : forall n : nat,
  QeqT (ri_x n) (bv_p n / (Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n. unfold ri_x, bv_x. apply qeq_imp_qeqT. reflexivity.
Qed.

(* D026r 消费件：ri_x n == tn_x n（tn_x_eq_bv_x 经 Qeq 桥反接） *)
Lemma ri_x_eq_tn : forall n : nat, QeqT (ri_x n) (tn_x n).
Proof.
  intro n. unfold ri_x. apply qeq_imp_qeqT. symmetry.
  apply qeqT_imp_qeq. apply tn_x_eq_bv_x.
Qed.

(* ============================================================ *)
(* §B 归一因子面：c_n := 2^{n+1}·q̃_n（D016 bi_norm_factor 同族直载形）      *)
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

(* 度量面：real_metric ri_real (real_const x'_n) ——使命①的投影对象 *)
Definition ri_metric (n : nat) : Real :=
  real_metric ri_real (real_const (ri_x n)).

Lemma ri_metric_proj : forall (n k : nat),
  projT1 (ri_metric n) k == Qabs ((ln2i_x k - ri_x n)%Q).
Proof.
  intros n k. unfold ri_metric.
  rewrite lic_metric_proj. rewrite ri_real_proj. reflexivity.
Qed.

(* 线面：|c_n·X − r_n|（D016 修正恒等式的 I_n real 面逐点语义承载；
   有理常数版——supply 整系数 line 的 p_n/q̃_n 归一对照形，见 §E 判词） *)
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

(* 核心代数核（纯 Q 层，逐点精确）：c_n·|X_k − x'_n| == |c_n·X_k − r_n|
   ——D016 修正恒等式的实数层代数承载（等式腿的本体） *)
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

(* supply 接口对齐读取器：线面 == c_n·度量面（逐点，使命③的输入形） *)
Lemma ri_metric_line_scale : forall (n k : nat),
  projT1 (ri_lineabs n) k == (ri_qnorm n * projT1 (ri_metric n) k)%Q.
Proof.
  intros n k. rewrite ri_lineabs_proj. rewrite ri_metric_proj.
  symmetry. apply ri_core_pt.
Qed.

(* ============================================================ *)
(* §D 目标恒等式 real 层语句化（条件形）+ eps 机真证装配（使命②等式腿）      *)
(* ============================================================ *)

(* I_n 侧 real 面输入形：I_n 的实数承载 nat→Real
   （本体积分面 D016 (a) 部分分式机挂账——诚实降档，见文件头登记 (i)） *)
Definition ri_Iface : Set := nat -> Real.

(* 输入腿（I_n real 面语义）：Ireal_n == |c_n·X − r_n| == I_n（实数层） *)
Definition ri_identity_leg (Ireal : ri_Iface) : Set :=
  forall n : nat, real_eq (Ireal n) (ri_lineabs n).

(* 目标恒等式（D016 修正形）：
   real_metric X (real_const x'_n) == I_n/(2^{n+1}·q̃_n) —— real 层承载 *)
Definition ri_identity_spec (Ireal : ri_Iface) : Set :=
  forall n : nat,
    real_eq (ri_metric n)
            (real_mult (Ireal n) (real_const (Qinv (ri_qnorm n)))).

(* eps 机支撑件（纯 Q 层，Qlt 脚手架面）：c·m == L、0 < c、|I − L| < c·eps
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

(* 主装配（真证）：Ireal 输入腿一旦供给，目标恒等式 real 层放电。
   机路：逐点核（ri_core_pt 精确）+ 输入腿 eps 读数除以 c_n —— 零 LPO。
   （QltT 目标先降 Qlt 脚手架再重写，lic_tail_e 同款 idiom） *)
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
(* §E supply 接口对齐（使命③：接口注释级登记，不抢 D034 sa_ 面）             *)
(* ============================================================ *)
(* 判词：L2（ln2b_delta_of_supply）的 real_metric 面消费形为               *)
(*   |A_n·X − B_n|（ln2b_line，A B : nat -> Z 整系数）。本席装配件输出      *)
(*   （度量面 ri_metric + 归一因子 ri_qnorm + 有理常数线面 ri_lineabs）     *)
(*   经 ri_metric_line_scale 恰为其逐点缩放像：                            *)
(*     lineabs_n == c_n·metric_n（逐点精确），                            *)
(* 即 supply clo/θ 腿（clo_n ≤ |A_n X − B_n| ≤ θ^n）的输入形可从装配       *)
(* 输出逐点直读。缺口登记：x' 族的 B_n := p_n 自 n=3 起非整（D026r 整性     *)
(* 预判），整系数重整是 supply 插槽前置战役——本席只做接口面登记，            *)
(* A/B 整化与 sa_ 总装归 D034 战役位。                                  *)

(* θ 腿转移件（上界腿）：Ireal_n/c_n ≤ θ^n ⟹ |X − x'_n| ≤ θ^n
   （real_eq 直入 real_le 右支 + real_le 传递——supply 上界腿的输入形） *)
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
(* §F 数值锚组（先锚后施工对账；vm_compute 档走投影引理）                     *)
(* ============================================================ *)

(* 归一因子：c_1 = 2²·q̃_1 = 4·3 = 12（D016「2^{2·1+1}·Q_1(1/2) = 12」对账） *)
Theorem ri_qnorm1_anchor : QeqT (ri_qnorm 1) (12 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* r 族对账：c_2·x'_2 == r_2 = 72（D016 r: 0, 8, 72） *)
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
(* 假设审计留痕：Print Assumptions（G4 复核位）                            *)
(* ============================================================ *)

Print Assumptions ri_x_eq_tn.
Print Assumptions ri_core_pt.
Print Assumptions ri_identity_assembly.
Print Assumptions ri_upper_transfer.
Print Assumptions ri_metric15_anchor.
