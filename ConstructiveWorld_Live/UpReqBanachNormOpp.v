(* ============================================================ *)
(* UpReqBanachNormOpp.v —— 席AA11：B5 件一速收（Qred 唯一性 +      *)
(*   bnorm Opp 面，20260914）                                     *)
(* ============================================================ *)
(* 使命（AA8 分解报告 B5 工单）：件一 qred_unique——INS L45 挂账     *)
(*   「保持 Id 余域不动，bnorm := Qred∘Qabs」的 Id-良定钥匙：       *)
(*     bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y *)
(*   （Leibniz 余域原形）；并落位 bnorm Opp/倒数面（件名对应）。    *)
(* 现成腿复用（AA8 判定 B5 最大惊喜＝B1 在飞件已铺 Z.gcd 腿）：     *)
(*   ① UpReqBanachInstB 规范形唯一机器（Zis_gcd_intro +            *)
(*      rel_prime_cross_prod + Z.mul_reg_l 面，bxib_cross_unique   *)
(*      同配方）——本席以 gcd=1 互素转移件重新组装：规范对           *)
(*      （Z.gcd 分子分母 = 1）交叉乘唯一，不触碰 ggcd 符号归约，    *)
(*      预避 AA3 实测的 Z.gcd 展开 Ffix 卡壳墙；                   *)
(*   ② UpReqBanachInstReal 的 bnorm_opp 攻墙链（bxra_qabs_opp_norm  *)
(*      ＝ Z.gcd_opp_l + bxib_div_exact + Z.mul_reg_l + Z.abs_opp  *)
(*      ＋ eq→Id match 桥，AA3 席交付）——Opp 面消费件直用；        *)
(*   ③ stdlib Qcanon.Qred_iff + Qreduction.Qred_correct——Qred 的   *)
(*      规范对特征（二次不变 Qred(Qred x)=Qred x 喂 Qred_iff），    *)
(*      主件组装腿。                                               *)
(* 主件证法（三腿组装，~40 行真构造）：                             *)
(*   x==y ⇒ Qred x==Qred y（Qred_correct 双向中转）⇒ 交叉乘式；     *)
(*   Qred x / Qred y 各为规范对（bno_qred_canon）；规范对交叉乘     *)
(*   唯一（Gauss/rel_prime_cross_prod）⇒ 分子分母分别相等 ⇒        *)
(*   Qred x = Qred y。                                             *)
(* 公理面自审：全件零 Axiom 零 Parameter 零 Conjecture 零           *)
(*   Admitted 零 Variable 零 Hypothesis；语句面全 Set/eq/Id/Qeq    *)
(*   形；主件出口 Print Assumptions Closed；Separate Extraction    *)
(*   Obj.magic 双零。                                              *)
(* 领土纪律：仅新建本件（bno_ 前缀全库零撞名）；既有件零改动        *)
(*   （仅 Require 消费 InstB/InstReal/S03 系）；禁 git。           *)
(* 件二状态：AA8 B5 工单件二（Σ1/k! 逃逸 sigT 显式速度形）——引擎段   *)
(*   本席闭合（bno_q_pow_one / bno_exp_series_succ_frac /             *)
(*   bno_mul_div_self / bno_exp_scale_Z＝n!·s_n 整数化核心），        *)
(*   逃逸主件（q==s_n 可判定分叉＋非零整数绝对值下界）仍挂账移交，     *)
(*   语句面以 bno_sum_inv_fact_escape 固化（诚实挂账，零硬凑）。       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qcanon
  ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：Z 层互素工具（规范对唯一机，bxib_cross_unique 同配方重组）   *)
(* ============================================================ *)

(* >0 桥（compare_gt_iff，bxib 同款） *)
Lemma bno_gt0_of_lt0 : forall d : Z, 0 < d -> (d > 0)%Z.
Proof. intros d H. apply (proj2 (Z.compare_gt_iff d 0)). exact H. Qed.

(* gcd = 1 → 互素（Zis_gcd_intro 配方；rel_prime := Zis_gcd .. 1） *)
Lemma bno_rel_prime_of_gcd1 : forall n d : Z, Z.gcd n d = 1%Z -> rel_prime n d.
Proof.
  intros n d H. apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros z Hz1 Hz2.
    pose proof (Zgcd_is_gcd n d) as Hg. destruct Hg as [_ _ Hdiv].
    rewrite H in Hdiv. exact (Hdiv z Hz1 Hz2).
Qed.

(* 规范对交叉乘唯一：两对分子分母均与 1 互素、分母正、交叉乘相等
   ⇒ 整对相等（Gauss/rel_prime_cross_prod 直收） *)
Lemma bno_canon_pair_unique : forall n1 d1 n2 d2 : Z,
  Z.gcd n1 d1 = 1%Z -> Z.gcd n2 d2 = 1%Z -> (d1 > 0)%Z -> (d2 > 0)%Z ->
  (n1 * d2 = n2 * d1)%Z -> n1 = n2 /\ d1 = d2.
Proof.
  intros n1 d1 n2 d2 H1 H2 P1 P2 Hc.
  rewrite (Z.mul_comm n2 d1) in Hc.
  destruct (rel_prime_cross_prod n1 d1 n2 d2
    (bno_rel_prime_of_gcd1 n1 d1 H1) (bno_rel_prime_of_gcd1 n2 d2 H2)
    P1 P2 Hc) as [E1 E2].
  split; assumption.
Qed.

(* ============================================================ *)
(* S1：件一主件——Qred 唯一性（INS L45 挂账清偿）                   *)
(* ============================================================ *)

(* Qred 输出恒为规范对（二次不变喂 Qred_iff） *)
Lemma bno_qred_canon : forall x : Q,
  Z.gcd (Qnum (Qred x)) (Z.pos (Qden (Qred x))) = 1%Z.
Proof.
  intro x.
  assert (Hi : Qred (Qred x) = Qred x) by (apply Qred_complete, Qred_correct).
  exact (proj1 (Qred_iff (Qred x)) Hi).
Qed.

(* 主件：Qred 唯一性（Qeq 入，Leibniz eq 出——Id-良定钥匙） *)
Lemma bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y.
Proof.
  intros x y Hxy.
  pose proof (bno_qred_canon x) as Hc1.
  pose proof (bno_qred_canon y) as Hc2.
  assert (Hr : Qred x == Qred y).
  { apply (Qeq_trans _ x).
    - apply Qred_correct.
    - rewrite Hxy. apply (Qeq_sym (Qred y) y). apply Qred_correct. }
  destruct (Qred x) as [n1 d1] eqn:Ex.
  destruct (Qred y) as [n2 d2] eqn:Ey.
  simpl in Hc1, Hc2.
  unfold Qeq in Hr; simpl in Hr.
  destruct (bno_canon_pair_unique n1 (Z.pos d1) n2 (Z.pos d2)
    Hc1 Hc2 ltac:(apply bno_gt0_of_lt0; lia) ltac:(apply bno_gt0_of_lt0; lia)
    Hr) as [E1 E2].
  apply Pos2Z.inj in E2. rewrite E1, E2. reflexivity.
Qed.

(* 主件 Id 面（eq→Id 桥，InstReal 现成腿） *)
Lemma bno_qred_unique_id : forall x y : Q, x == y -> Id (Qred x) (Qred y).
Proof. intros x y H. apply bxra_id_of_eq. apply bno_qred_unique. exact H. Qed.

(* ============================================================ *)
(* S2：bnorm Opp/倒数面落位（INS L45 处方 bnorm := Qred∘Qabs 的     *)
(*     bnorm_opp 位 discharge ＋ InstReal 攻墙链消费转写）          *)
(* ============================================================ *)

(* 新件：Qred∘Qabs 的取负不变（eq 形）——Q 载体 bnorm_opp 字段位 *)
Lemma bno_qred_abs_opp : forall u : Q, Qred (Qabs (Qopp u)) = Qred (Qabs u).
Proof.
  intro u. apply Qred_complete.
  destruct u as [n d]. cbn [Qopp Qabs].
  unfold Qeq; simpl. rewrite Z.abs_opp. reflexivity.
Qed.

(* 同件 Id 形（eq→Id 桥） *)
Lemma bno_qred_abs_opp_id : forall u : Q,
  Id (Qred (Qabs (Qopp u))) (Qred (Qabs u)).
Proof. intro u. apply bxra_id_of_eq. apply bno_qred_abs_opp. Qed.

(* 消费形转写①（InstReal 现成腿直用，语句形保留库内 Id 原形：
   Qopp 与 qnorm 的 Qabs-范数不变） *)
Lemma bno_qabs_qnorm_opp : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof. intro u. apply bxra_qabs_opp_norm. Qed.

(* 消费形转写②（Real 载体面：bnorm(opp x) ＝ bnorm x，库内 Id 原形） *)
Lemma bno_bnorm_opp_real : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof. intro a. apply bxra_f_norm_opp. Qed.

(* ============================================================ *)
(* S3：件二挂账形（AA8 B5 工单指定语句面，证体移交——诚实挂账，      *)
(*     零硬凑。原料清单见交付报告：q_fact_pos/exp_series 系         *)
(*     （S03_QExp）、n!·s_n 整数化引擎、q==s_n 可判定分叉。）       *)
(* ============================================================ *)

Definition bno_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).

(* ---- 件二引擎件（冲刺段，预算内闭合三件；逃逸主件仍挂账） ---- *)

(* 引擎①：1 的幂归一 *)
Lemma bno_q_pow_one : forall n : nat, q_pow 1%Q n == 1%Q.
Proof.
  induction n as [| m IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qmult_1_l. exact IH.
Qed.

(* 引擎②前小件：q*(1/q) 归一（Qdiv 定义展开位；Qmult_inv_r 的 ≠ 是 Qeq 形） *)
Lemma bno_mul_div_self : forall q : Q, ~ (q == 0%Q) -> q * (1%Q / q) == 1%Q.
Proof.
  intros q Hq. unfold Qdiv. rewrite Qmult_1_l. apply Qmult_inv_r. exact Hq.
Qed.

(* 引擎②：exp_series 单步分数形（B:=1 位） *)
Lemma bno_exp_series_succ_frac : forall n : nat,
  exp_series (Datatypes.S n) 1%Q
    == exp_series n 1%Q + 1%Q / q_fact (Datatypes.S n)%Q.
Proof.
  intro n. cbn [exp_series]. rewrite bno_q_pow_one. reflexivity.
Qed.

(* 引擎③：n!·s_n 整数化（Σ1/k! 不收敛性的核心原料——n! 倍后落 Z） *)
Lemma bno_exp_scale_Z : forall n : nat,
  sigT (fun z : Z => QeqT (q_fact n * exp_series n 1)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. apply qeq_imp_qeqT. unfold Qeq. cbn [q_fact exp_series Qnum Qden Qmult]. reflexivity.
  - destruct IH as [z Hz].
    exists (Z.of_nat (Datatypes.S m) * z + 1)%Z.
    apply qeq_imp_qeqT.
    rewrite q_fact_succ.
    rewrite bno_exp_series_succ_frac.
    assert (Hq0 : ~ ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m == 0%Q)).
    { intro Hc. apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S m))).
      apply Qeq_sym. exact Hc. }
    assert (Hs : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * (1%Q / ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q) == 1%Q).
    { apply bno_mul_div_self. exact Hq0. }
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * exp_series m 1%Q == ((Z.of_nat (Datatypes.S m) * z) # 1)%Q).
    { apply (Qeq_trans _ ((Z.of_nat (Datatypes.S m) # 1)%Q
                          * (q_fact m * exp_series m 1)%Q)%Q).
      - apply Qeq_sym. apply Qmult_assoc.
      - apply (@Qmult_comp (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Qeq_refl (Z.of_nat (Datatypes.S m) # 1)%Q)
                           (q_fact m * exp_series m 1)%Q ((z # 1)%Q)
                           (qeqT_imp_qeq (q_fact m * exp_series m 1)%Q
                                ((z # 1)%Q) Hz)). }
    rewrite Qmult_plus_distr_r.
    rewrite Hs.
    rewrite Hm.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult].
    first [lia | ring | reflexivity].
Qed.

(* ============================================================ *)
(* S4：提取探针 + 假设面自审（G3 面）                               *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
(* 提取纪律（INST5/AA3 同款）：只收标量/引理级件；Id/eq 值件提取     *)
(*   零依赖载体项，Obj.magic 预期双零。                            *)
Separate Extraction bno_qred_unique bno_qred_unique_id bno_canon_pair_unique
  bno_rel_prime_of_gcd1 bno_gt0_of_lt0 bno_qred_canon bno_qred_abs_opp
  bno_qred_abs_opp_id bno_qabs_qnorm_opp bno_bnorm_opp_real.

Print Assumptions bno_qred_unique.
Print Assumptions bno_qred_unique_id.
Print Assumptions bno_canon_pair_unique.
Print Assumptions bno_qred_abs_opp.
Print Assumptions bno_qred_abs_opp_id.
Print Assumptions bno_qabs_qnorm_opp.
Print Assumptions bno_bnorm_opp_real.
Print Assumptions bno_q_pow_one.
Print Assumptions bno_exp_series_succ_frac.
Print Assumptions bno_mul_div_self.
Print Assumptions bno_exp_scale_Z.
