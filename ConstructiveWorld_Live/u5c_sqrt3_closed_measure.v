(* ========================================================================== *)
(* u5c_sqrt3_closed_measure.v —— √3 构造性可提取无理性测度（闭式常元件）        *)
(* ========================================================================== *)
(* 一、使命：对任意有理数 q=a/b（a:Z、b:positive），给出显式闭式常元            *)
(*     c=1/(12·b²)（主定理语句中分母按正数算术 12*(b*b) 书写，与 Z 层           *)
(*     12*(Z.pos b)*(Z.pos b) 同值；原冻结文本的 Z 形分母无法通过类型检查，      *)
(*     此为最小语义保形替代，随执行记录响亮登记），使 real_const c 与 √3 的         *)
(*     Newton 逼近序列 is3_x（池内 UpReqSqrt3Irrational）柯西极限的实度量之间    *)
(*     有 real_lt 严格分离。即 √3 的逐有理数可计算分离证书（无理性测度）：       *)
(*     给定 a,b 可计算逃逸点 n0=den(q)+3 与常元 c，全件可提取可执行。           *)
(* 二、方法：统一逃逸点 n0=den(q)+3 四分支（q≤0／0<q 且 q²<3／3<q² 且 q≤7/4／   *)
(*     q>7/4）逐支证边距 |q−x(n0)|−e(n0) ≥ 2c = 1/(6b²)，再接通用桥             *)
(*     dmec_escape_to_dist_any（边距参数化分离引理，直接 Require 复用）。       *)
(*     四支数值链：q≤0: 5/3−1/12；q²<3: 2/(7b²)−1/12；3<q²≤7/4 支:              *)
(*     (1/b²−1/(8b²))·2/7−1/12 = 1/(4b²)−1/12 = 1/(6b²)=2c 恰好衔接；            *)
(*     q>7/4: 1/(4b)−1/(12b²) ≥ 1/(6b²)。                                     *)
(* 三、依赖：池内在册件链 S01_BaseRing、S02_CauchyComplete、S03_QExp、          *)
(*     SumInvFactEscape、UpReqBanachNormOpp、UpReqIrrationalCriterion、         *)
(*     UpReqSqrt3Irrational（ir2/is3 全套）与 u5c_dm_escape_to_dist_any（通用桥）；*)
(*     Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。 *)
(*     并行他件（u5c_aux_natpow／u5c_dm_escape_window／u5c_sqrt2_closed_measure）*)
(*     零 Require 零触碰；自携副本一律 dms3_ 前缀。                             *)
(* 四、构造性：语句面全 Set 层（sigT／S01.And／QltT／QleT'／real_lt）；全零承认、 *)
(*     零公理、零经典逻辑；定义透明。本件辅助件以 lia/nia 做归纳切割与 Q 交叉积  *)
(*     收尾（例外册 solver 冻结条款任务指令点名形，此处响亮登记；主定理为长链      *)
(*     装配，以 exact 接通用桥收尾，非 solver 收尾）。                          *)
(* 五、编译配方：source Live/toolchain/env.sh 后池目录内                         *)
(*     rocq c -native-compiler no -q -Q . "" u5c_sqrt3_closed_measure.v         *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：nat 幂界自携副本（dms3_pow12/dms3_pow4/dms3_pow2b 工艺）      *)
(* ============================================================ *)

(* 线性归纳基：2k+1 ≤ 2^{k+1} *)
Lemma dms3_lin_pow : forall k : nat, (2 * k + 1 <= 2 ^ (k + 1))%nat.
Proof.
  induction k as [|k IH].
  - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
  - replace (2 ^ (Datatypes.S k + 1))%nat with (2 * 2 ^ (k + 1))%nat
      by (replace (Datatypes.S k + 1)%nat with (Datatypes.S (k + 1))%nat by lia;
          rewrite Nat.pow_succ_r'; reflexivity).
    pose proof (ir2_pow_ge (k + 1)) as Hp.
    lia.
Qed.

(* 平方归纳基：k² ≤ 2^{k+1}（k ≥ 1） *)
Lemma dms3_pow2b : forall k : nat, (1 <= k)%nat -> (k * k <= 2 ^ (k + 1))%nat.
Proof.
  induction k as [|k IH]; intro Hk.
  - lia.
  - replace (2 ^ (Datatypes.S k + 1))%nat with (2 * 2 ^ (k + 1))%nat
      by (replace (Datatypes.S k + 1)%nat with (Datatypes.S (k + 1))%nat by lia;
          rewrite Nat.pow_succ_r'; reflexivity).
    destruct (Nat.eq_dec k 0) as [Hk0 | Hk0].
    + subst k. apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    + assert (Hk1 : (1 <= k)%nat) by lia.
      pose proof (IH Hk1) as IH'.
      pose proof (dms3_lin_pow k) as Hlin.
      replace (Datatypes.S k * Datatypes.S k)%nat
        with (k * k + 2 * k + 1)%nat by ring.
      lia.
Qed.

(* 4k² ≤ 2^{k+3} *)
Lemma dms3_pow4 : forall k : nat, (1 <= k)%nat -> (4 * k * k <= 2 ^ (k + 3))%nat.
Proof.
  intros k Hk. pose proof (dms3_pow2b k Hk) as H2.
  assert (Hy : (2 ^ (k + 1) = 2 * 2 ^ k)%nat).
  { replace (k + 1)%nat with (Datatypes.S k)%nat by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  assert (Hx : (2 ^ (k + 3) = 8 * 2 ^ k)%nat).
  { replace (k + 3)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S k)))%nat by lia.
    rewrite !Nat.pow_succ_r'. lia. }
  rewrite Hx. rewrite Hy in H2. nia.
Qed.

(* 12k² ≤ 2^{k+5}（e 界的主配重） *)
Lemma dms3_pow12 : forall k : nat, (1 <= k)%nat -> (12 * k * k <= 2 ^ (k + 5))%nat.
Proof.
  intros k Hk. pose proof (dms3_pow2b k Hk) as H2.
  assert (Hy : (2 ^ (k + 1) = 2 * 2 ^ k)%nat).
  { replace (k + 1)%nat with (Datatypes.S k)%nat by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  assert (Hx : (2 ^ (k + 5) = 32 * 2 ^ k)%nat).
  { replace (k + 5)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))%nat
      by lia.
    rewrite !Nat.pow_succ_r'. lia. }
  rewrite Hx. rewrite Hy in H2. nia.
Qed.

(* ============================================================ *)
(* S1：自携微转换与通用小件                                          *)
(* ============================================================ *)

(* 右端加项消去（Qle 层） *)
Lemma dms3_qle_add_cancel_r : forall x y z : Q, QleT' (x + z) (y + z) -> QleT' x y.
Proof.
  intros [xn xd] [yn yd] [zn zd] H.
  pose proof (QleT'_to_Qle _ _ H) as H0.
  apply Qle_to_QleT'.
  unfold Qle in H0 |- *. cbn [Qnum Qden Qplus] in H0 |- *.
  assert (Hxz : (Z.pos (xd * zd) = Z.pos xd * Z.pos zd)%Z) by (apply Pos2Z.inj_mul).
  assert (Hyz : (Z.pos (yd * zd) = Z.pos yd * Z.pos zd)%Z) by (apply Pos2Z.inj_mul).
  rewrite Hxz, Hyz in H0.
  assert (Hxd : (0 < Z.pos xd)%Z) by apply Pos2Z.is_pos.
  assert (Hyd : (0 < Z.pos yd)%Z) by apply Pos2Z.is_pos.
  assert (Hzd : (0 < Z.pos zd)%Z) by apply Pos2Z.is_pos.
  nia.
Qed.

(* 边距改形：Qle (cc+e) X → QleT' cc (X−e)（接通用桥的边距输入形） *)
Lemma dms3_margin_close : forall cc e X : Q, QleT' (cc + e) X -> QleT' cc ((X - e)%Q).
Proof.
  intros cc e X H.
  apply Qle_to_QleT'.
  apply QleT'_to_Qle.
  apply (dms3_qle_add_cancel_r cc ((X - e)%Q) e).
  apply Qle_to_QleT'.
  apply (Qle_trans _ X).
  - exact (QleT'_to_Qle _ _ H).
  - apply qeq_le. symmetry. apply lic_qlt_minus_add_r.
Qed.

(* 2^k 的 Q 形严格正 *)
Lemma dms3_qp_pos : forall k : nat, QltT 0%Q ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  intro k. apply Qlt_to_QltT.
  pose proof (ir2_pow_ge k) as Hp.
  assert (H1 : (1 <= 2 ^ k)%nat) by lia.
  pose proof (proj1 (Nat2Z.inj_le _ _) H1) as HpZ.
  change (Z.of_nat 1) with 1%Z in HpZ.
  unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* 分母为正变量时的 Qle 交叉乘帮助件 *)
Lemma dms3_qle_cross : forall (an bn : Z) (ad bd : positive),
  (an * Z.pos bd <= bn * Z.pos ad)%Z -> QleT' ((an # ad)) ((bn # bd))%Q.
Proof.
  intros an bn ad bd H. apply Qle_to_QleT'.
  unfold Qle. cbn [Qnum Qden]. exact H.
Qed.

(* 同分母加一（Qeq 恒等，供常元和的规范化改写） *)
Lemma dms3_pair_add : forall p : positive, QeqT (((1 # p) + (1 # p))%Q) ((2 # p)%Q).
Proof.
  intro p. apply qeq_imp_qeqT.
  unfold Qeq, Qplus. cbn [Qnum Qden]. rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma dms3_pair_add2 : forall p : positive, QeqT (((2 # p) + (1 # p))%Q) ((3 # p)%Q).
Proof.
  intro p. apply qeq_imp_qeqT.
  unfold Qeq, Qplus. cbn [Qnum Qden]. rewrite Pos2Z.inj_mul. ring.
Qed.

(* den(q) ≥ 1 *)
Lemma dms3_hkb1 : forall b : positive, (1 <= Z.to_nat (Z.pos b))%nat.
Proof.
  intro b.
  destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
  exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
  rewrite Ek in Hz. cbn in Hz. lia.
Qed.

(* ============================================================ *)
(* S2：e/δ 量化界（基座 is3_x1=(7#4) 算 e(1)、步进 is3_e_step）       *)
(* ============================================================ *)

(* 幂步进换算：(2^{S m + 2}#1)·((1#2)·e) == (2^{m+2}#1)·e *)
Lemma dms3_step_eq : forall (m : nat) (e : Q),
  QeqT (((Z.of_nat (2 ^ (Datatypes.S m + 2)) # 1) * ((1 # 2) * e))%Q)
       (((Z.of_nat (2 ^ (m + 2)) # 1) * e)%Q).
Proof.
  intros m e. apply qeq_imp_qeqT.
  assert (H : (2 ^ (Datatypes.S m + 2) = 2 * 2 ^ (m + 2))%nat).
  { replace (Datatypes.S m + 2)%nat with (Datatypes.S (m + 2))%nat by lia.
    rewrite Nat.pow_succ_r'. reflexivity. }
  pose proof (f_equal Z.of_nat H) as Hz. rewrite Nat2Z.inj_mul in Hz.
  change (Z.of_nat 2) with 2%Z in Hz.
  unfold Qeq, Qmult. cbn [Qnum Qden]. rewrite Hz.
  rewrite ?Pos.mul_1_l. repeat rewrite Pos2Z.inj_mul. ring.
Qed.

(* 乘性衰减主链：(2^{n+2}#1)·e(n) ≤ 1（n ≥ 1；基座 e(1)=1/32） *)
Lemma dms3_e_mul : forall n : nat, (1 <= n)%nat ->
  QleT' (((Z.of_nat (2 ^ (n + 2))) # 1)%Q * is3_e n) 1%Q.
Proof.
  intro n. induction n as [|n IH]; intro Hn1.
  - apply Qle_to_QleT'. lia.
  - destruct n as [|n'].
    + apply Qle_to_QleT'.
      change (is3_e 1) with (1 # 32)%Q.
      replace (2 ^ (1 + 2))%nat with 8%nat by reflexivity.
      unfold Qle, Qmult. cbn [Qnum Qden Z.of_nat]. lia.
    + assert (Hn'1 : (1 <= Datatypes.S n')%nat) by lia.
      pose proof (is3_e_step (Datatypes.S n') Hn'1) as Hstep.
      pose proof (IH Hn'1) as IH'.
      apply Qle_to_QleT'.
      apply (Qle_trans _
        (((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S n') + 2))) # 1)%Q
          * ((1 # 2) * is3_e (Datatypes.S n'))%Q)%Q).
      * apply (ir2_mult_le_compat_l (is3_e (Datatypes.S (Datatypes.S n')))
              ((1 # 2) * is3_e (Datatypes.S n'))
              ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S n') + 2))) # 1)).
        -- exact Hstep.
        -- apply Qlt_le_weak. apply QltT_to_Qlt. apply dms3_qp_pos.
      * pose proof (qeqT_imp_qeq _ _
                      (dms3_step_eq (Datatypes.S n')
                        (is3_e (Datatypes.S n')))) as Heq.
        rewrite Heq. exact (QleT'_to_Qle _ _ IH').
Qed.

(* Qinv 形：e(n) ≤ 2^{−(n+2)}（n ≥ 1） *)
Lemma dms3_e_pow_le : forall n : nat, (1 <= n)%nat ->
  QleT' (is3_e n) (Qinv ((Z.of_nat (2 ^ (n + 2))) # 1)%Q).
Proof.
  intros n Hn1. apply Qle_to_QleT'.
  apply (ir2_le_inv ((Z.of_nat (2 ^ (n + 2))) # 1)%Q (is3_e n)).
  - apply QltT_to_Qlt. apply dms3_qp_pos.
  - apply QleT'_to_Qle. apply (dms3_e_mul n Hn1).
Qed.

(* 闭式 e 界：n0 ≥ den+3 → e(n0) ≤ 1/(12b²) *)
Lemma dms3_e_bnd : forall (b : positive) (n : nat),
  (Z.to_nat (Z.pos b) + 3 <= n)%nat ->
  QleT' (is3_e n) ((1 # (12 * (b * b)))%Q).
Proof.
  intros b n Hn.
  apply Qle_to_QleT'.
  pose proof (dms3_hkb1 b) as Hkb1.
  assert (Hn1 : (1 <= n)%nat) by lia.
  pose proof (dms3_e_pow_le n Hn1) as H1.
  assert (Hmono : (2 ^ (Z.to_nat (Z.pos b) + 5) <= 2 ^ (n + 2))%nat)
    by (apply Nat.pow_le_mono_r; lia).
  assert (H2 : Qle (Qinv ((Z.of_nat (2 ^ (n + 2))) # 1)%Q)
                   (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 5))) # 1)%Q)).
  { apply (ir2_inv_le ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 5))) # 1)%Q
                      ((Z.of_nat (2 ^ (n + 2))) # 1)%Q).
    - apply QltT_to_Qlt. apply dms3_qp_pos.
    - unfold Qle. cbn [Qnum Qden].
      pose proof (proj1 (Nat2Z.inj_le _ _) Hmono) as HmZ.
      lia. }
  assert (H3 : Qle (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 5))) # 1)%Q)
                   ((1 # (12 * (b * b)))%Q)).
  { apply (ir2_ge_inv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 5))) # 1)%Q
                      ((1 # (12 * (b * b)))%Q)).
    - apply QltT_to_Qlt. apply dms3_qp_pos.
    - pose proof (dms3_pow12 (Z.to_nat (Z.pos b)) Hkb1) as Hp12.
      pose proof (proj1 (Nat2Z.inj_le _ _) Hp12) as Hp12Z.
      rewrite !Nat2Z.inj_mul in Hp12Z.
      change (Z.of_nat 12) with 12%Z in Hp12Z.
      pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hkb.
      rewrite Hkb in Hp12Z.
      unfold Qle, Qmult. cbn [Qnum Qden].
      repeat rewrite Pos2Z.inj_mul.
      nia. }
  apply (Qle_trans _ (Qinv ((Z.of_nat (2 ^ (n + 2))) # 1)%Q)).
  - exact (QleT'_to_Qle _ _ H1).
  - exact (Qle_trans _ _ _ H2 H3).
Qed.

(* δ 的乘性衰减：(2^{n+1}#1)·δ(n) ≤ 1（n ≥ 1；δ=2e） *)
Lemma dms3_delta_mul : forall n : nat, (1 <= n)%nat ->
  QleT' (((Z.of_nat (2 ^ (n + 1))) # 1)%Q * is3_delta n) 1%Q.
Proof.
  intros n Hn1.
  apply Qle_to_QleT'.
  assert (Hd2e : (is3_delta n == ((2 # 1) * is3_e n))%Q)
    by (unfold is3_e; ring).
  pose proof (dms3_e_mul n Hn1) as He.
  apply (Qle_trans _
    ((((Z.of_nat (2 ^ (n + 1))) # 1)%Q * ((2 # 1) * is3_e n))%Q)).
  - rewrite Hd2e. apply Qle_refl.
  - apply (Qle_trans _ ((((Z.of_nat (2 ^ (n + 2))) # 1)%Q * is3_e n)%Q)).
    + apply qeq_le.
      unfold Qeq, Qmult. cbn [Qnum Qden].
      assert (Hpow : (2 ^ (n + 2) = 2 * 2 ^ (n + 1))%nat)
        by (replace (n + 2)%nat with (Datatypes.S (n + 1))%nat by lia;
            rewrite Nat.pow_succ_r'; reflexivity).
      pose proof (f_equal Z.of_nat Hpow) as Hz. rewrite Nat2Z.inj_mul in Hz.
      change (Z.of_nat 2) with 2%Z in Hz. rewrite Hz.
      rewrite ?Pos.mul_1_l. repeat rewrite Pos2Z.inj_mul. ring.
    + exact (QleT'_to_Qle _ _ He).
Qed.

(* 闭式 δ 界：n0 = den+3 处 δ(n0) ≤ 1/(8b²) *)
Lemma dms3_delta_eighth : forall b : positive,
  QleT' (is3_delta (Z.to_nat (Z.pos b) + 3)) ((1 # (8 * (b * b)))%Q).
Proof.
  intro b.
  apply Qle_to_QleT'.
  pose proof (dms3_hkb1 b) as Hkb1.
  assert (Hn1 : (1 <= Z.to_nat (Z.pos b) + 3)%nat) by lia.
  pose proof (dms3_delta_mul (Z.to_nat (Z.pos b) + 3) Hn1) as H1.
  assert (H2 : Qle (is3_delta (Z.to_nat (Z.pos b) + 3))
                   (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3 + 1))) # 1)%Q)).
  { apply (ir2_le_inv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3 + 1))) # 1)%Q
                      (is3_delta (Z.to_nat (Z.pos b) + 3))).
    - apply QltT_to_Qlt. apply dms3_qp_pos.
    - exact (QleT'_to_Qle _ _ H1). }
  assert (H3 : Qle (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3 + 1))) # 1)%Q)
                   (Qinv (((8 * (Z.pos b * Z.pos b)) # 1)%Q))).
  { apply (ir2_inv_le (((8 * (Z.pos b * Z.pos b)) # 1)%Q)
                      ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3 + 1))) # 1)%Q).
    - unfold Qlt. cbn [Qnum Qden]. repeat rewrite Pos2Z.inj_mul.
      assert (HB1 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      nia.
    - pose proof (dms3_pow2b (Z.to_nat (Z.pos b)) Hkb1) as Hp2.
      replace (Z.to_nat (Z.pos b) + 1)%nat
        with (Datatypes.S (Z.to_nat (Z.pos b)))%nat in Hp2 by lia.
      rewrite Nat.pow_succ_r' in Hp2.
      replace (Z.to_nat (Z.pos b) + 3 + 1)%nat
        with (Datatypes.S (Datatypes.S (Datatypes.S
                (Datatypes.S (Z.to_nat (Z.pos b))))))%nat by lia.
      rewrite !Nat.pow_succ_r'.
      unfold Qle. cbn [Qnum Qden].
      pose proof (proj1 (Nat2Z.inj_le _ _) Hp2) as Hp2Z.
      rewrite !Nat2Z.inj_mul in Hp2Z.
      pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hkb.
      rewrite Hkb in Hp2Z.
      repeat rewrite Pos2Z.inj_mul. nia. }
  assert (H4 : Qle (Qinv (((8 * (Z.pos b * Z.pos b)) # 1)%Q))
                   ((1 # (8 * (b * b)))%Q)).
  { apply (ir2_ge_inv (((8 * (Z.pos b * Z.pos b)) # 1)%Q)
                      ((1 # (8 * (b * b)))%Q)).
    - unfold Qlt. cbn [Qnum Qden]. repeat rewrite Pos2Z.inj_mul.
      assert (HB1 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      nia.
    - unfold Qle, Qmult. cbn [Qnum Qden]. repeat rewrite Pos2Z.inj_mul. nia. }
  apply (Qle_trans _ (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3 + 1))) # 1)%Q)).
  - exact H2.
  - exact (Qle_trans _ _ _ H3 H4).
Qed.

(* ============================================================ *)
(* S3：统一逃逸窗口与边距（四分支，n0 = den(q)+3）                      *)
(* ============================================================ *)

(* 常元与逃逸点的显式定义（Defined 透明；主定理处按转换性对应冻结语句） *)
Definition dms3_n0 (b : positive) : nat := Z.to_nat (Z.pos b) + 3.
Definition dms3_c (b : positive) : Q := (1 # (12 * (b * b)))%Q.

(* 统一边距：|q−x(n0)|−e(n0) ≥ 2c = 1/(6b²)，四分支一体 *)
Lemma dms3_margin_closed : forall (a : Z) (b : positive),
  QleT' ((dms3_c b + dms3_c b)%Q)
        ((Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
          - is3_e (dms3_n0 b))%Q).
Proof.
  intros a b.
  unfold dms3_c, dms3_n0.
  pose proof (Pos2Z.is_pos b) as Hb0.
  pose proof (dms3_hkb1 b) as Hkb1.
  assert (Hn01 : (1 <= Z.to_nat (Z.pos b) + 3)%nat) by lia.
  pose proof (is3_x_lb (Z.to_nat (Z.pos b) + 3)) as Hxlb.
  pose proof (is3_x_ub (Z.to_nat (Z.pos b) + 3) Hn01) as Hxub.
  pose proof (is3_x_pos (Z.to_nat (Z.pos b) + 3)) as Hxpos.
  pose proof (dms3_e_bnd b (Z.to_nat (Z.pos b) + 3) (Nat.le_refl _)) as Heb.
  assert (HB1 : (1 <= Z.pos b * Z.pos b)%Z) by nia.
  destruct (Qlt_bool 0%Q ((a # b)%Q)) eqn:Hpos.
  - (* —— q > 0 —— *)
    pose proof (lic_qlt_bool_true 0%Q ((a # b)%Q) Hpos) as Hq0.
    assert (Hq0p : Qle 0%Q ((a # b)%Q)) by (apply Qlt_le_weak; exact Hq0).
    destruct (Qlt_bool ((a # b)%Q * (a # b)%Q) 3%Q) eqn:H3b.
    + (* B2：0 < q 且 q² < 3 *)
      pose proof (lic_qlt_bool_true ((a # b)%Q * (a # b)%Q) 3%Q H3b) as H3.
      assert (Hqx2 : Qlt ((a # b)%Q * (a # b)%Q)
                       (is3_x (Z.to_nat (Z.pos b) + 3)
                        * is3_x (Z.to_nat (Z.pos b) + 3))).
      { apply (Qlt_le_trans ((a # b)%Q * (a # b)%Q) 3%Q
                (is3_x (Z.to_nat (Z.pos b) + 3)
                 * is3_x (Z.to_nat (Z.pos b) + 3))).
        - exact H3.
        - apply is3_sq_ge3. }
      assert (Hqltx : Qlt ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))).
      { apply (ir2_lt_of_sq (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q));
          [apply Qlt_le_weak; exact Hxpos | exact Hq0p | exact Hqx2]. }
      assert (Hm : Qle ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                     ((Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)
                       - is3_e (Z.to_nat (Z.pos b) + 3))%Q)).
      { rewrite (Qabs_Qminus ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))).
        rewrite (ir2_abs_sub (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)
                  (Qlt_le_weak _ _ Hqltx)).
        assert (Hsuff : Qle (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                              + is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                             ((is3_x (Z.to_nat (Z.pos b) + 3)
                               - (a # b)%Q)%Q)).
        { apply (Qle_trans _ (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                               + (1 # (12 * (b * b))))%Q)).
          - apply Qplus_le_compat.
            + apply Qle_refl.
            + exact (QleT'_to_Qle _ _ Heb).
          - rewrite (qeqT_imp_qeq _ _ (dms3_pair_add (12 * (b * b)))).
            rewrite (qeqT_imp_qeq _ _ (dms3_pair_add2 (12 * (b * b)))).
            apply (Qle_trans (3 # (12 * (b * b)))%Q
                    (((1 # (b * b)) * (2 # 7))%Q)
                    (is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q).
            + unfold Qle, Qmult. cbn [Qnum Qden].
              repeat rewrite Pos2Z.inj_mul. nia.
            + assert (Hgap : Qle ((3 - ((a # b)%Q * (a # b)%Q)) * (2 # 7))
                                  (is3_x (Z.to_nat (Z.pos b) + 3)
                                   - (a # b)%Q)%Q).
              { apply (is3_gap_lower (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q));
                  [exact Hq0p
                  | apply Qlt_le_weak; exact Hqltx
                  | exact Hxub
                  | apply is3_sq_ge3
                  | exact H3]. }
              assert (Hgap2 : Qle ((1 # (b * b)) * (2 # 7))
                                   ((3 - ((a # b)%Q * (a # b)%Q)) * (2 # 7))).
              { apply Qmult_le_compat_r.
                - assert (Hz3 : (a * a < 3 * Z.pos b * Z.pos b)%Z).
                  { pose proof H3 as H3'. unfold Qlt, Qmult in H3'.
                    cbn [Qnum Qden] in H3'. rewrite Pos2Z.inj_mul in H3'. lia. }
                  assert (Hne3z : (a * a <> 3 * (Z.pos b * Z.pos b))%Z).
                  { intro Hc. exact (is3_no_sqrtZ a (Z.pos b) Hb0 Hc). }
                  assert (Hg1 : (1 <= 3 * Z.pos b * Z.pos b - a * a)%Z) by lia.
                  unfold Qle, Qminus, Qopp, Qplus, Qmult. cbn [Qnum Qden].
                  repeat rewrite Pos2Z.inj_mul. nia.
                - unfold Qle. cbn [Qnum Qden]. lia. }
              apply (Qle_trans _ ((3 - ((a # b)%Q * (a # b)%Q)) * (2 # 7))%Q).
              * exact Hgap2.
              * exact Hgap. }
        apply QleT'_to_Qle.
        apply (dms3_qle_add_cancel_r
                ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                (((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)
                  - is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                (is3_e (Z.to_nat (Z.pos b) + 3))).
        apply Qle_to_QleT'.
        apply (Qle_trans _
                ((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q)).
        - exact Hsuff.
        - apply qeq_le. symmetry. apply lic_qlt_minus_add_r. }
      exact (Qle_to_QleT' _ _ Hm).
    + pose proof (lic_qlt_bool_false_le ((a # b)%Q * (a # b)%Q) 3%Q H3b) as Hge3.
      destruct (Qeq_dec ((a # b)%Q * (a # b)%Q) 3%Q) as [Heq3 | Hne3].
      * exfalso. exact (is3_no_sqrt3 ((a # b)%Q) Heq3).
      * destruct (Qlt_bool 3%Q ((a # b)%Q * (a # b)%Q)) eqn:H3lt.
        -- pose proof (lic_qlt_bool_true 3%Q ((a # b)%Q * (a # b)%Q) H3lt) as Hlt3.
           destruct (Qlt_bool (7 # 4) ((a # b)%Q)) eqn:H74b.
           ++ (* B4：7/4 < q *)
              pose proof (lic_qlt_bool_true (7 # 4) ((a # b)%Q) H74b) as H74.
              assert (Hqltx : Qlt (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)).
              { apply (Qle_lt_trans (is3_x (Z.to_nat (Z.pos b) + 3))
                        (7 # 4) ((a # b)%Q));
                  [exact Hxub | exact H74]. }
              assert (Hxq : Qle ((a # b)%Q - (7 # 4))
                                 ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
              { pose proof (Qopp_le_compat (is3_x (Z.to_nat (Z.pos b) + 3))
                              (7 # 4) Hxub) as Hopp.
                pose proof (ir2_add_le_r (Qopp (7 # 4))
                             (Qopp (is3_x (Z.to_nat (Z.pos b) + 3)))
                             ((a # b)%Q) Hopp) as Hle.
                rewrite (Qplus_comm (Qopp (7 # 4)) ((a # b)%Q)) in Hle.
                rewrite (Qplus_comm (Qopp (is3_x (Z.to_nat (Z.pos b) + 3)))
                          ((a # b)%Q)) in Hle.
                exact Hle. }
              assert (H74z : (7 * Z.pos b < 4 * a)%Z).
              { pose proof H74 as H74'. unfold Qlt in H74'.
                cbn [Qnum Qden] in H74'. lia. }
              assert (Hm : Qle ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                             ((Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)
                               - is3_e (Z.to_nat (Z.pos b) + 3))%Q)).
              { rewrite (ir2_abs_sub ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))
                          (Qlt_le_weak _ _ Hqltx)).
                assert (Hsuff : Qle (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                                      + is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                                     ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                { apply (Qle_trans _ (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                                       + (1 # (12 * (b * b))))%Q)).
                  - apply Qplus_le_compat.
                    + apply Qle_refl.
                    + exact (QleT'_to_Qle _ _ Heb).
                  - rewrite (qeqT_imp_qeq _ _ (dms3_pair_add (12 * (b * b)))).
                    rewrite (qeqT_imp_qeq _ _ (dms3_pair_add2 (12 * (b * b)))).
                    apply (Qle_trans (3 # (12 * (b * b)))%Q
                            ((1 # (4 * b))%Q)
                            ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                    + unfold Qle. cbn [Qnum Qden].
                      repeat rewrite Pos2Z.inj_mul. nia.
                    + apply (Qle_trans _ ((a # b)%Q - (7 # 4))%Q).
                      * unfold Qle, Qminus, Qopp, Qplus. cbn [Qnum Qden].
                        repeat rewrite Pos2Z.inj_mul. nia.
                      * exact Hxq. }
                apply QleT'_to_Qle.
                apply (dms3_qle_add_cancel_r
                        ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                        (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3)
                          - is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                        (is3_e (Z.to_nat (Z.pos b) + 3))).
                apply Qle_to_QleT'.
                apply (Qle_trans _
                        ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                - exact Hsuff.
                - apply qeq_le. symmetry. apply lic_qlt_minus_add_r. }
              exact (Qle_to_QleT' _ _ Hm).
           ++ (* B3：3 < q² 且 q ≤ 7/4 *)
              pose proof (lic_qlt_bool_false_le (7 # 4) ((a # b)%Q) H74b) as H74.
              assert (Hz3' : (3 * Z.pos b * Z.pos b < a * a)%Z).
              { pose proof Hlt3 as H3'. unfold Qlt, Qmult in H3'.
                cbn [Qnum Qden] in H3'. rewrite Pos2Z.inj_mul in H3'. lia. }
              assert (Hgap3 : Qle ((1 # (b * b)))
                                   ((a # b)%Q * (a # b)%Q - 3%Q)%Q).
              { assert (Hg1 : (1 <= a * a - 3 * Z.pos b * Z.pos b)%Z) by lia.
                unfold Qle, Qminus, Qopp, Qplus, Qmult. cbn [Qnum Qden].
                repeat rewrite Pos2Z.inj_mul. nia. }
              assert (H8 : Qle (is3_delta (Z.to_nat (Z.pos b) + 3))
                                ((1 # (8 * (b * b)))%Q))
                by (apply QleT'_to_Qle; apply dms3_delta_eighth).
              assert (Hdlt : Qlt (is3_delta (Z.to_nat (Z.pos b) + 3))
                                  ((a # b)%Q * (a # b)%Q - 3%Q)%Q).
              { apply (Qle_lt_trans (is3_delta (Z.to_nat (Z.pos b) + 3))
                        ((1 # (8 * (b * b)))%Q)
                        ((a # b)%Q * (a # b)%Q - 3%Q)%Q).
                - exact H8.
                - apply (Qlt_le_trans ((1 # (8 * (b * b)))%Q) ((1 # (b * b)))%Q).
                  + unfold Qlt. cbn [Qnum Qden].
                    repeat rewrite Pos2Z.inj_mul. nia.
                  + exact Hgap3. }
              assert (Hqx2 : Qlt (is3_x (Z.to_nat (Z.pos b) + 3)
                                   * is3_x (Z.to_nat (Z.pos b) + 3))
                                  ((a # b)%Q * (a # b)%Q)).
              { pose proof (lic_qlt_minus_add_r
                             (is3_x (Z.to_nat (Z.pos b) + 3)
                              * is3_x (Z.to_nat (Z.pos b) + 3)) 3%Q) as Hr1.
                pose proof (lic_qlt_minus_add_r
                             ((a # b)%Q * (a # b)%Q) 3%Q) as Hr2.
                apply (Qle_lt_trans
                        (is3_x (Z.to_nat (Z.pos b) + 3)
                         * is3_x (Z.to_nat (Z.pos b) + 3))
                        ((is3_x (Z.to_nat (Z.pos b) + 3)
                          * is3_x (Z.to_nat (Z.pos b) + 3) - 3%Q) + 3%Q)%Q
                        ((a # b)%Q * (a # b)%Q)).
                - apply (qeq_le _ _ (Qeq_sym _ _ Hr1)).
                - apply (lic_qlt_comp_r
                          (((a # b)%Q * (a # b)%Q - 3%Q) + 3%Q)%Q
                          ((a # b)%Q * (a # b)%Q)
                          ((is3_x (Z.to_nat (Z.pos b) + 3)
                            * is3_x (Z.to_nat (Z.pos b) + 3) - 3%Q) + 3%Q)%Q).
                  + exact Hr2.
                  + apply (lic_qlt_add_r _ _ 3%Q Hdlt). }
              assert (Hqltx : Qlt (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)).
              { apply (ir2_lt_of_sq ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3)));
                  [exact Hq0p
                  | apply Qlt_le_weak; exact Hxpos
                  | exact Hqx2]. }
              assert (Hsum : Qlt 0%Q ((a # b)%Q
                              + is3_x (Z.to_nat (Z.pos b) + 3))%Q).
              { apply ir2_qpos_add; [exact Hq0 | exact Hxpos]. }
              assert (Hne : ~ (((a # b)%Q
                                 + is3_x (Z.to_nat (Z.pos b) + 3))%Q == 0%Q)).
              { intro Hc.
                apply (Qlt_not_eq 0%Q
                        ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3)) Hsum).
                rewrite Hc. apply Qeq_refl. }
              assert (Hbridge : (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))
                                 == (((a # b)%Q * (a # b)%Q
                                      - is3_x (Z.to_nat (Z.pos b) + 3)
                                        * is3_x (Z.to_nat (Z.pos b) + 3))
                                     * Qinv ((a # b)%Q
                                             + is3_x (Z.to_nat (Z.pos b) + 3))))%Q).
              { pose proof (bno_mul_div_self
                             ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3)) Hne) as Hb.
                unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
                assert (Hpm : ((((((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3)) * ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3))) * Qinv (((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3))))) == ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3)))%Q).
                { rewrite <- (Qmult_assoc ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))
                              ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3))
                              (Qinv ((a # b)%Q
                                     + is3_x (Z.to_nat (Z.pos b) + 3)))).
                  rewrite Hb. apply Qmult_1_r. }
                rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
              assert (Hsqeq : ((((a # b)%Q * (a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3) * is3_x (Z.to_nat (Z.pos b) + 3)) == ((a # b)%Q * (a # b)%Q - 3%Q - is3_delta (Z.to_nat (Z.pos b) + 3))))%Q)
                by (unfold is3_delta; ring).
              assert (Hsumub : Qle ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3))
                                    ((7 # 2))%Q).
              { apply (Qle_trans _ ((7 # 4) + (7 # 4))%Q).
                - apply (Qplus_le_compat ((a # b)%Q) (7 # 4)
                           (is3_x (Z.to_nat (Z.pos b) + 3)) (7 # 4));
                    [exact H74 | exact Hxub].
                - apply qeq_le. reflexivity. }
              assert (Hinv : Qle ((2 # 7))
                                  (Qinv ((a # b)%Q
                                         + is3_x (Z.to_nat (Z.pos b) + 3)))%Q).
              { apply (Qle_trans ((2 # 7)) (Qinv (7 # 2))%Q
                         (Qinv ((a # b)%Q
                                + is3_x (Z.to_nat (Z.pos b) + 3)))%Q).
                - apply qeq_le. reflexivity.
                - apply (ir2_inv_le ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3))
                          (7 # 2));
                    [exact Hsum | exact Hsumub]. }
              assert (Hsub : Qle ((1 # (b * b)) - (1 # (8 * (b * b)))%Q)
                                  ((a # b)%Q * (a # b)%Q - 3%Q
                                   - is3_delta (Z.to_nat (Z.pos b) + 3))%Q).
              { assert (Hadd : Qle ((1 # (b * b))
                                     + is3_delta (Z.to_nat (Z.pos b) + 3))%Q
                                    ((a # b)%Q * (a # b)%Q - 3%Q
                                     + (1 # (8 * (b * b))))%Q).
                { apply Qplus_le_compat; [exact Hgap3 | exact H8]. }
                assert (E1 : ((((1 # (b * b)) - (1 # (8 * (b * b)))) + ((1 # (8 * (b * b))) + is3_delta (Z.to_nat (Z.pos b) + 3))) == ((1 # (b * b)) + is3_delta (Z.to_nat (Z.pos b) + 3)))%Q) by ring.
                assert (E2 : ((((a # b)%Q * (a # b)%Q - 3%Q - is3_delta (Z.to_nat (Z.pos b) + 3)) + ((1 # (8 * (b * b))) + is3_delta (Z.to_nat (Z.pos b) + 3))) == ((a # b)%Q * (a # b)%Q - 3%Q + (1 # (8 * (b * b)))))%Q) by ring.
                apply QleT'_to_Qle.
                apply (dms3_qle_add_cancel_r
                        ((1 # (b * b)) - (1 # (8 * (b * b)))%Q)
                        ((a # b)%Q * (a # b)%Q - 3%Q
                         - is3_delta (Z.to_nat (Z.pos b) + 3))%Q
                        ((1 # (8 * (b * b)))
                         + is3_delta (Z.to_nat (Z.pos b) + 3))%Q).
                apply Qle_to_QleT'.
                rewrite E1, E2. exact Hadd. }
              assert (Hw0 : Qle 0%Q (((a # b)%Q * (a # b)%Q - 3%Q
                                      - is3_delta (Z.to_nat (Z.pos b) + 3))%Q)).
              { apply (Qle_trans _ ((1 # (b * b)) - (1 # (8 * (b * b)))%Q)).
                - unfold Qle, Qminus, Qopp, Qplus. cbn [Qnum Qden].
                  repeat rewrite Pos2Z.inj_mul.
                  assert (HB2 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
                  nia.
                - exact Hsub. }
              assert (Hsplit : ((1 # (4 * (b * b)))
                                == ((1 # (b * b)) - (1 # (8 * (b * b))))
                                   * (2 # 7))%Q).
              { unfold Qeq, Qminus, Qopp, Qmult, Qplus. cbn [Qnum Qden].
                repeat rewrite Pos2Z.inj_mul. ring. }
              assert (Hm : Qle ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                             ((Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)
                               - is3_e (Z.to_nat (Z.pos b) + 3))%Q)).
              { rewrite (ir2_abs_sub ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))
                          (Qlt_le_weak _ _ Hqltx)).
                assert (Hsuff : Qle (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                                      + is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                                     ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                { apply (Qle_trans _ (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                                       + (1 # (12 * (b * b))))%Q)).
                  - apply Qplus_le_compat.
                    + apply Qle_refl.
                    + exact (QleT'_to_Qle _ _ Heb).
                  - rewrite (qeqT_imp_qeq _ _ (dms3_pair_add (12 * (b * b)))).
                    rewrite (qeqT_imp_qeq _ _ (dms3_pair_add2 (12 * (b * b)))).
                    apply (Qle_trans (3 # (12 * (b * b)))%Q
                            ((1 # (4 * (b * b)))%Q)
                            ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                    + unfold Qle. cbn [Qnum Qden].
                      repeat rewrite Pos2Z.inj_mul. nia.
                    + rewrite Hsplit. rewrite Hbridge. rewrite Hsqeq.
                      apply (Qle_trans _
                              ((((a # b)%Q * (a # b)%Q - 3%Q
                                 - is3_delta (Z.to_nat (Z.pos b) + 3))%Q)
                                * (2 # 7))%Q).
                      * apply Qmult_le_compat_r.
                        -- exact Hsub.
                        -- unfold Qle. cbn [Qnum Qden]. lia.
                      * apply (ir2_mult_le_compat_l (2 # 7)
                                (Qinv ((a # b)%Q + is3_x (Z.to_nat (Z.pos b) + 3)))
                                (((a # b)%Q * (a # b)%Q - 3%Q
                                  - is3_delta (Z.to_nat (Z.pos b) + 3))%Q)).
                        -- exact Hinv.
                        -- exact Hw0. }
                apply QleT'_to_Qle.
                apply (dms3_qle_add_cancel_r
                        ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                        (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3)
                          - is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                        (is3_e (Z.to_nat (Z.pos b) + 3))).
                apply Qle_to_QleT'.
                apply (Qle_trans _
                        ((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q).
                - exact Hsuff.
                - apply qeq_le. symmetry. apply lic_qlt_minus_add_r. }
              exact (Qle_to_QleT' _ _ Hm).
        -- (* ¬(3<q²) 且 3 ≤ q² ⟹ q² == 3，与 is3_no_sqrt3 矛盾 *)
           exfalso. apply Hne3.
           pose proof (lic_qlt_bool_false_le 3%Q ((a # b)%Q * (a # b)%Q) H3lt) as Hle3'.
           apply (Qle_antisym ((a # b)%Q * (a # b)%Q) 3%Q); [exact Hle3' | exact Hge3].
  - (* —— q ≤ 0：A = x−q ≥ 5/3 —— *)
    pose proof (lic_qlt_bool_false_le 0%Q ((a # b)%Q) Hpos) as Hq0.
    assert (Hqx : Qle ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))).
    { apply (Qle_trans ((a # b)%Q) 0%Q (is3_x (Z.to_nat (Z.pos b) + 3))).
      - exact Hq0.
      - apply Qlt_le_weak. exact Hxpos. }
    assert (Hxq : Qle (is3_x (Z.to_nat (Z.pos b) + 3))
                      ((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q)).
    { pose proof (Qopp_le_compat ((a # b)%Q) 0%Q Hq0) as Hopp.
      change (Qopp 0%Q) with 0%Q in Hopp.
      pose proof (ir2_add_le_r 0%Q (Qopp ((a # b)%Q))
                   (is3_x (Z.to_nat (Z.pos b) + 3)) Hopp) as Hle.
      rewrite Qplus_0_l in Hle.
      rewrite (Qplus_comm (Qopp ((a # b)%Q))
                (is3_x (Z.to_nat (Z.pos b) + 3))) in Hle.
      exact Hle. }
    assert (Hm : Qle ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
                   ((Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)
                     - is3_e (Z.to_nat (Z.pos b) + 3))%Q)).
    { rewrite (Qabs_Qminus ((a # b)%Q) (is3_x (Z.to_nat (Z.pos b) + 3))).
      rewrite (ir2_abs_sub (is3_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q) Hqx).
      assert (Hsuff : Qle (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                            + is3_e (Z.to_nat (Z.pos b) + 3))%Q)
                           ((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q)).
      { apply (Qle_trans _ (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
                             + (1 # (12 * (b * b))))%Q)).
        - apply Qplus_le_compat.
          + apply Qle_refl.
          + exact (QleT'_to_Qle _ _ Heb).
        - rewrite (qeqT_imp_qeq _ _ (dms3_pair_add (12 * (b * b)))).
          rewrite (qeqT_imp_qeq _ _ (dms3_pair_add2 (12 * (b * b)))).
          apply (Qle_trans (3 # (12 * (b * b)))%Q (5 # 3)%Q
                  (is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q).
          + unfold Qle. cbn [Qnum Qden]. repeat rewrite Pos2Z.inj_mul. nia.
          + apply (Qle_trans _ (is3_x (Z.to_nat (Z.pos b) + 3)));
              [exact Hxlb | exact Hxq]. }
      apply QleT'_to_Qle.
      apply (dms3_qle_add_cancel_r
              ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)
              (((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)
                - is3_e (Z.to_nat (Z.pos b) + 3))%Q)
              (is3_e (Z.to_nat (Z.pos b) + 3))).
      apply Qle_to_QleT'.
      apply (Qle_trans _
              ((is3_x (Z.to_nat (Z.pos b) + 3) - (a # b)%Q)%Q)).
      - exact Hsuff.
      - apply qeq_le. symmetry. apply lic_qlt_minus_add_r. }
    exact (Qle_to_QleT' _ _ Hm).
Qed.

(* 固定逃逸点处的严格逃逸（主定理装配用） *)
Lemma dms3_escape_at : forall (a : Z) (b : positive),
  QltT (is3_e (Z.to_nat (Z.pos b) + 3))
       (Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)).
Proof.
  intros a b.
  pose proof (dms3_margin_closed a b) as HmT'.
  pose proof (QleT'_to_Qle _ _ HmT') as Hm.
  assert (Hcc0 : Qlt 0%Q ((1 # (12 * (b * b))) + (1 # (12 * (b * b)))%Q)).
  { unfold Qlt, Qplus. cbn [Qnum Qden]. repeat rewrite Pos2Z.inj_mul.
    assert (HB1 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
    nia. }
  remember (Qabs (((a # b)%Q - is3_x (Z.to_nat (Z.pos b) + 3))%Q)) as A
    eqn:HA.
  unfold dms3_n0 in Hm.
  rewrite <- HA in Hm.
  assert (HA2 : (((A - is3_e (Z.to_nat (Z.pos b) + 3))
                  + is3_e (Z.to_nat (Z.pos b) + 3)) == A)%Q)
    by apply lic_qlt_minus_add_r.
  apply Qlt_to_QltT.
  rewrite <- HA2.
  apply (Qlt_le_trans (is3_e (Z.to_nat (Z.pos b) + 3))
          (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))
            + is3_e (Z.to_nat (Z.pos b) + 3))%Q)
          ((A - is3_e (Z.to_nat (Z.pos b) + 3))
           + is3_e (Z.to_nat (Z.pos b) + 3))%Q).
  - assert (Hlt1 : Qlt (is3_e (Z.to_nat (Z.pos b) + 3) + 0%Q)
                     (is3_e (Z.to_nat (Z.pos b) + 3)
                      + ((1 # (12 * (b * b))) + (1 # (12 * (b * b))))%Q))
      by (apply (lic_qlt_add_l _ _ _ Hcc0)).
    rewrite Qplus_0_r in Hlt1.
    rewrite (Qplus_comm (is3_e (Z.to_nat (Z.pos b) + 3))
              ((1 # (12 * (b * b))) + (1 # (12 * (b * b))))) in Hlt1.
    exact Hlt1.
  - apply Qplus_le_compat.
    + exact Hm.
    + apply Qle_refl.
Qed.

(* 统一逃逸窗口：n0 := den(q)+3（四分支收拢后的显式见证形） *)
Lemma dms3_escape_closed_window : forall (a : Z) (b : positive),
  sigT (fun n : nat => And ((Z.to_nat (Z.pos b) + 3 <= n)%nat)
    (QltT (is3_e n) (Qabs (((a # b)%Q - is3_x n)%Q)))).
Proof.
  intros a b. exists (Z.to_nat (Z.pos b) + 3)%nat. split.
  - apply Nat.le_refl.
  - apply dms3_escape_at.
Qed.

(* ============================================================ *)
(* S4：主定理——√3 闭式分离常元（装配通用桥）                          *)
(* ============================================================ *)

(* 定 c 装配件：通用桥 dmec_escape_to_dist_any 的同构延伸——
   因冻结语句以 Qeq 确定 c=1/(12b²)，而 dmec 输出 sigT 的见证 c0 在语句面
   不透明（其谓词无 Qeq 位），末里按同一边距参数化工艺以固定字面常元装配。 *)
Lemma dms3_measure_assembly : forall (a : Z) (b : positive),
  QltT 0%Q ((1 # (12 * (b * b)))%Q) ->
  QleT' ((dms3_c b + dms3_c b)%Q)
        ((Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
          - is3_e (dms3_n0 b))%Q) ->
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (12 * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                              (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros a b Hc0T Hm.
  exists ((1 # (12 * (b * b)))%Q).
  split.
  - exact Hc0T.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + unfold real_lt.
      exists ((1 # (12 * (b * b)))%Q).
      split.
      * exact Hc0T.
      * exists (dms3_n0 b). intros k HkN.
        apply NatLe_drop in HkN.
        assert (Hn01 : (1 <= dms3_n0 b)%nat).
        { unfold dms3_n0. pose proof (dms3_hkb1 b). lia. }
        pose proof (QltT_to_Qlt _ _ (is3_tail (dms3_n0 b) k Hn01 HkN)) as Ht0'.
        assert (Hpre : ((a # b)%Q - is3_x (dms3_n0 b))%Q
                       == (((a # b)%Q - is3_x k)
                           + (is3_x k - is3_x (dms3_n0 b)))%Q)
          by exact (lic_qlt_tri_decomp ((a # b)%Q)
                      (is3_x (dms3_n0 b)) (is3_x k)).
        assert (Htri : Qle (Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q))
                           (Qabs (((a # b)%Q - is3_x k)%Q)
                            + Qabs ((is3_x k - is3_x (dms3_n0 b))%Q))).
        { pose proof (Qabs_triangle (((a # b)%Q - is3_x k)%Q)
                        ((is3_x k - is3_x (dms3_n0 b))%Q)) as HT.
          apply (Qle_trans (Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q))
                   (Qabs ((((a # b)%Q - is3_x k)
                           + (is3_x k - is3_x (dms3_n0 b)))%Q))).
          - apply qeq_le. setoid_rewrite Hpre. apply Qeq_refl.
          - exact HT. }
        assert (Hlt1 : Qlt (Qabs (((a # b)%Q - is3_x k)%Q)
                             + Qabs ((is3_x k - is3_x (dms3_n0 b))%Q))
                            (Qabs (((a # b)%Q - is3_x k)%Q)
                             + is3_e (dms3_n0 b)))
          by (apply (lic_qlt_add_l _ _ _ Ht0')).
        assert (Hlt2 : Qlt (Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q))
                            (Qabs (((a # b)%Q - is3_x k)%Q)
                             + is3_e (dms3_n0 b)))
          by (apply (Qle_lt_trans
                      (Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q))
                      (Qabs (((a # b)%Q - is3_x k)%Q)
                       + Qabs ((is3_x k - is3_x (dms3_n0 b))%Q))
                      (Qabs (((a # b)%Q - is3_x k)%Q)
                       + is3_e (dms3_n0 b)));
              [exact Htri | exact Hlt1]).
        assert (HA2 : (((Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
                         - is3_e (dms3_n0 b))
                        + is3_e (dms3_n0 b))
                       == Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q))%Q)
          by apply lic_qlt_minus_add_r.
        rewrite <- HA2 in Hlt2.
        assert (Hltm : Qlt ((Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
                              - is3_e (dms3_n0 b)))
                            (Qabs (((a # b)%Q - is3_x k)%Q)))
          by (apply (lic_qlt_add_r_cancel_r
                      ((Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
                        - is3_e (dms3_n0 b))%Q)
                      (Qabs (((a # b)%Q - is3_x k)%Q))
                      (is3_e (dms3_n0 b))); exact Hlt2).
        pose proof (QleT'_to_Qle _ _ Hm) as Hm'.
        assert (HltQ : Qlt (((1 # (12 * (b * b))) + (1 # (12 * (b * b)))))
                            (Qabs (((a # b)%Q - is3_x k)%Q)))
          by (apply (Qle_lt_trans
                      (((1 # (12 * (b * b))) + (1 # (12 * (b * b))))%Q)
                      (Qabs (((a # b)%Q - is3_x (dms3_n0 b))%Q)
                       - is3_e (dms3_n0 b))%Q
                      (Qabs (((a # b)%Q - is3_x k)%Q)));
              [exact Hm' | exact Hltm]).
        assert (Hfin : Qlt ((1 # (12 * (b * b))))
                            ((Qabs (((a # b)%Q - is3_x k)%Q)
                              - (1 # (12 * (b * b))))%Q)).
        { apply (lic_qlt_add_r_cancel_r ((1 # (12 * (b * b))))
                  ((Qabs (((a # b)%Q - is3_x k)%Q)
                    - (1 # (12 * (b * b))))%Q)
                  ((1 # (12 * (b * b))))).
          rewrite (lic_qlt_minus_add_r (Qabs (((a # b)%Q - is3_x k)%Q))
                    ((1 # (12 * (b * b))))). exact HltQ. }
        assert (HPr : projT1 (real_metric
                               (existT (fun u : Qseq => cauchy u) is3_x
                                 (lic_seq_cauchy is3_x is3_e is3_tail
                                  is3_vanish))
                               (real_const ((a # b)%Q))) k
                   == Qabs ((is3_x k - (a # b)%Q)%Q))
          by apply lic_metric_proj.
        apply (lic_qltt_comp_r
                ((Qabs (((a # b)%Q - is3_x k)%Q)
                  - (1 # (12 * (b * b))))%Q)
                (projT1 (real_metric
                          (existT (fun u : Qseq => cauchy u) is3_x
                            (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
                          (real_const ((a # b)%Q))) k
                 - projT1 (real_const ((1 # (12 * (b * b))))) k)
                ((1 # (12 * (b * b))))).
        -- rewrite real_const_proj. rewrite HPr.
           rewrite (Qabs_Qminus ((a # b)%Q) (is3_x k)). reflexivity.
        -- apply Qlt_to_QltT. exact Hfin.
Qed.

Theorem u5c_sqrt3_closed_measure : forall (a : Z) (b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (12 * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) is3_x
                              (lic_seq_cauchy is3_x is3_e is3_tail is3_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros a b.
  assert (Hc0T : QltT 0%Q ((1 # (12 * (b * b)))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia. }
  exact (dms3_measure_assembly a b Hc0T (dms3_margin_closed a b)).
Qed.

(* ============================================================ *)
(* S5：提取检验与公理面自审                                           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt3_closed_measure dms3_measure_assembly dms3_escape_closed_window
  dms3_escape_at dms3_margin_closed dms3_e_pow_le dms3_e_bnd
  dms3_delta_eighth dms3_delta_mul dms3_e_mul dms3_step_eq
  dms3_pow12 dms3_pow4 dms3_pow2b dms3_lin_pow
  dms3_qle_add_cancel_r dms3_margin_close dms3_qle_cross dms3_qp_pos
  dms3_pair_add dms3_pair_add2 dms3_hkb1.

Print Assumptions u5c_sqrt3_closed_measure.
Print Assumptions dms3_margin_closed.
Print Assumptions dms3_escape_closed_window.
