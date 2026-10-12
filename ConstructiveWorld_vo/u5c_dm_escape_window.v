(* 五字段指针｜使命：√2 牛顿序列 x(n) 的统一逃逸窗口件——对任意有理数 q = a/b，
   逃逸点 n0 := Z.to_nat (Z.pos b) + 3 对全体 q 一致可行：ir2_e(n0) ≤ 1/(12 b²) 且
   ir2_e(n0) < |q − x(n0)|（Qabs 见证形）。这是首个不依赖逐 q 分支选取窗口
   位置的显式逃逸点定理：四分支（q≤0 / q²<2 / 2<q²∧q≤3/2 / q>3/2）共用同一
   窗口，闭式分离常元 1/(12 b²) 路线的窗口件供给。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational
   （以上皆池内在册件，只读引用）；Stdlib QArith、Qabs、ZArith、Arith、
   Bool、Lia、Setoid、Morphisms、Qfield。
   对标行：UpReqSqrt3Irrational.v ir2_decay、ir2_e_step、ir2_delta_pow_le、
   ir2_le_inv、ir2_inv_le、ir2_gap_lower、ir2_gap_upper_small、ir2_escape；
   UpReqIrrationalCriterion.v lic_escape_window。
   构造性注记：四语句语句面全 Set 层（sigT/And/QltT），零承认、零经典逻辑、
   零全局假设位；证明体实质推导链＝归纳（e≤2^−(n+2)）＋三连换算
   （delta_pow_le → qp_pow → le_inv）＋幂界归纳自携副本（dmew_pow12/dmew_pow4）
   ＋四分支可判定分叉（Qlt_bool ×3 ＋ Qeq_dec）显式构造 n0=den(q)+3。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_dm_escape_window.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S1：nat 幂界自携副本（12b²≤2^(b+5)、4b²≤2^(b+3)）                    *)
(* ============================================================ *)

Lemma dmew_pow12 : forall j : nat, (12 * (j * j) <= 2 ^ (j + 5))%nat.
Proof.
  assert (H32 : forall j : nat, (32 * j + 32 <= 2 ^ (j + 5))%nat).
  { induction j as [|j IH].
    - cbn. lia.
    - replace ((Datatypes.S j) + 5)%nat with (Datatypes.S (j + 5))%nat by lia.
      rewrite (Nat.pow_succ_r' 2%nat (j + 5)).
      lia. }
  induction j as [|j IH].
  - cbn. lia.
  - replace ((Datatypes.S j) + 5)%nat with (Datatypes.S (j + 5))%nat by lia.
    rewrite (Nat.pow_succ_r' 2%nat (j + 5)).
    replace (12 * (Datatypes.S j * Datatypes.S j))%nat with (12 * (j * j) + 24 * j + 12)%nat by ring.
    pose proof (H32 j) as Hx. lia.
Qed.

Lemma dmew_pow4 : forall j : nat, (4 * (j * j) <= 2 ^ (j + 3))%nat.
Proof.
  assert (H8 : forall j : nat, (8 * j + 8 <= 2 ^ (j + 3))%nat).
  { induction j as [|j IH].
    - cbn. lia.
    - replace ((Datatypes.S j) + 3)%nat with (Datatypes.S (j + 3))%nat by lia.
      rewrite (Nat.pow_succ_r' 2%nat (j + 3)).
      lia. }
  induction j as [|j IH].
  - cbn. lia.
  - replace ((Datatypes.S j) + 3)%nat with (Datatypes.S (j + 3))%nat by lia.
    rewrite (Nat.pow_succ_r' 2%nat (j + 3)).
    replace (4 * (Datatypes.S j * Datatypes.S j))%nat with (4 * (j * j) + 8 * j + 4)%nat by ring.
    pose proof (H8 j) as Hx. lia.
Qed.

(* ============================================================ *)
(* S2：Qinv 换算小件（半_inv = 乘二_inv）与衰减二件                       *)
(* ============================================================ *)

Lemma dmew_inv_half : forall z : Z,
  QeqT (Qinv ((2 * z) # 1)) ((1 # 2) * Qinv (z # 1))%Q.
Proof.
  intro z. apply qeq_imp_qeqT. destruct z as [|p|p]; unfold Qeq;
    cbn [Z.mul Qinv Qmult Qnum Qden Pos.mul]; reflexivity.
Qed.

(* 语句一：e(n) ≤ 2^−(n+2)（归纳：基座 n=1 走 change，步进 ir2_e_step＋半_inv 换算） *)
Lemma dmew_e_pow_le : forall n : nat, (1 <= n)%nat ->
  QleT' (ir2_e n) (Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S n)))) # 1)).
Proof.
  assert (Hmain : forall n : nat,
    Qle (ir2_e (Datatypes.S n)) (Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))) # 1))).
  { induction n as [|n IH].
    - rewrite <- (ir2_qp_pow 3).
      apply (ir2_le_inv (ir2_qp 3) (ir2_e 1)).
      + apply ir2_qp_pos.
      + rewrite (Qmult_comm (ir2_qp 3) (ir2_e 1)).
        change (ir2_e 1) with (4 # 32)%Q.
        change (ir2_qp 3) with (8 # 1)%Q.
        unfold Qle, Qmult. cbn [Qnum Qden Qinv]. lia.
    - assert (Hconv : (((1 # 2) * Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))) # 1))
                       == Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S n)))))) # 1))%Q).
      { rewrite (Nat.pow_succ_r' 2%nat (Datatypes.S (Datatypes.S (Datatypes.S n)))).
        rewrite (Nat2Z.inj_mul 2%nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))%nat).
        replace (Z.of_nat 2) with (2%Z) by reflexivity.
        apply Qeq_sym. apply qeqT_imp_qeq. apply dmew_inv_half. }
      rewrite <- Hconv.
      apply (Qle_trans (ir2_e (Datatypes.S (Datatypes.S n)))
              (((1 # 2) * ir2_e (Datatypes.S n))%Q)
              (((1 # 2) * Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))) # 1))%Q)).
      + apply (ir2_e_step (Datatypes.S n)). lia.
      + apply (ir2_mult_le_compat_l (ir2_e (Datatypes.S n))
                 (Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S n))))) # 1)) (1#2)).
        * exact IH.
        * unfold Qle. cbn [Qnum Qden Qinv]. lia. }
  intros n Hn. apply Qle_to_QleT'. destruct n as [|n'].
  - lia.
  - apply (Hmain n').
Qed.

(* 语句二：δ(n) ≤ 2^−n（delta_pow_le → qp_pow → le_inv 三连） *)
Lemma dmew_delta_pow_inv : forall n : nat, (1 <= n)%nat ->
  QleT' (ir2_delta n) (Qinv ((Z.of_nat (2 ^ n)) # 1)).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  apply (ir2_le_inv ((Z.of_nat (2 ^ n)) # 1) (ir2_delta n)).
  - assert (Hz : (0 < Z.of_nat (2 ^ n))%Z).
    { pose proof (ir2_pow_ge n) as Hp.
      assert (H0 : (0 < 2 ^ n)%nat) by lia.
      pose proof (proj1 (Nat2Z.inj_lt 0%nat (2 ^ n)%nat) H0) as Hzz.
      cbn [Z.of_nat] in Hzz. exact Hzz. }
    unfold Qlt. cbn [Qnum Qden Qinv]. lia.
  - rewrite (Qmult_comm ((Z.of_nat (2 ^ n)) # 1) (ir2_delta n)).
    rewrite <- (ir2_qp_pow n).
    apply (ir2_delta_pow_le n Hn).
Qed.

(* 语句三：e 界——n ≥ den(q)+3 时 e(n) ≤ 1/(12 b²)）
   链：dmew_e_pow_le → 2^(n+2) ≥ 2^(b+5) ≥ 12b² → ir2_inv_le 反向收尾 *)
Lemma dmew_e_bnd : forall (b : positive) (n : nat),
  (Z.to_nat (Z.pos b) + 3 <= n)%nat ->
  QleT' (ir2_e n) ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q).
Proof.
  intros b n Hn. apply Qle_to_QleT'.
  apply (Qle_trans (ir2_e n) (Qinv ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S n)))) # 1))
                   ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)).
  - apply QleT'_to_Qle. apply dmew_e_pow_le. lia.
  - apply (ir2_inv_le ((12 * (Z.pos b * Z.pos b)) # 1)
                      ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S n)))) # 1)).
    + pose proof (Pos2Z.is_pos b) as Hb0.
      unfold Qlt. cbn [Qnum Qden Qinv]. nia.
    + pose proof (dmew_pow12 (Z.to_nat (Z.pos b))) as H12.
      apply (proj1 (Nat2Z.inj_le _ _)) in H12.
      pose proof (Nat.pow_le_mono_r 2%nat (Z.to_nat (Z.pos b) + 5) (Datatypes.S (Datatypes.S n))
                    (ltac:(lia)) (ltac:(lia))) as Hpw.
      apply (proj1 (Nat2Z.inj_le _ _)) in Hpw.
      pose proof (Z2Nat.id (Z.pos b) (Z.lt_le_incl 0 (Z.pos b) (Pos2Z.is_pos b))) as Hbt.
      rewrite !Nat2Z.inj_mul in H12.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H12.
      rewrite Hbt in H12.
      unfold Qle. cbn [Qnum Qden Qinv]. lia.
Qed.

(* Qinv 桥接引理（辅助结构豁免·使用于主件证体）：Qinv 定义面 match on Qnum，
   非构造子分子（Z.mul 形）下 cbn 不归约、nia 面对不透明原子无法衔接——
   主件 10 站点统一以此二件桥接：1p 折叠正分子为正分母形；lt 走 9-case 构造子归约。 *)
Lemma dmew_Qinv_1p : forall p : positive, QeqT (Qinv ((Z.pos p) # 1)) (1 # p)%Q.
Proof. intros p. apply qeq_imp_qeqT. unfold Qeq, Qinv. cbn [Qnum Qden]. lia. Qed.

Lemma dmew_Qinv_lt : forall u v : Z, (0 < u)%Z -> (u < v)%Z ->
  QltT (Qinv (v # 1)) (Qinv (u # 1)).
Proof.
  intros u v Hu Hv. apply Qlt_to_QltT.
  destruct u as [|pu|pu]; destruct v as [|pv|pv];
    unfold Qlt, Qinv; cbn [Qnum Qden]; try lia; nia.
Qed.

(* ============================================================ *)
(* S3：统一逃逸窗口主件（n0 := den(q)+3 对全体 q 一致可行）                  *)
(* ============================================================ *)

Theorem dmew_escape_closed_window : forall (a : Z) (b : positive),
  sigT (fun n : nat => And ((Z.to_nat (Z.pos b) + 3 <= n)%nat)
    (QltT (ir2_e n) (Qabs (((a # b)%Q - ir2_x n)%Q)))).
Proof.
  intros a b.
  assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Hbt : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
  assert (Hn1 : (1 <= Z.to_nat (Z.pos b))%nat).
  { destruct (Z.to_nat (Z.pos b)) as [|t] eqn:Et; [ | lia].
    exfalso. pose proof (Z2Nat.id (Z.pos b) (Z.lt_le_incl 0 (Z.pos b) Hb0)) as Hz.
    rewrite Et in Hz. cbn [Z.of_nat] in Hz. discriminate. }
  assert (Hn13 : (1 <= Z.to_nat (Z.pos b) + 3)%nat) by lia.
  assert (Hq1 : Qinv ((Z.pos b * Z.pos b) # 1) == (1 # (b * b))%Q)
    by (rewrite <- (Pos2Z.inj_mul b b); apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  assert (Hq2 : Qinv ((2 * Z.pos b) # 1) == (1 # (2 * b))%Q)
    by (rewrite <- (Pos2Z.inj_mul 2 b); apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  assert (Hq3 : Qinv ((3 * (Z.pos b * Z.pos b)) # 1) == (1 # (3 * (b * b)))%Q)
    by (rewrite <- (Pos2Z.inj_mul b b), <- (Pos2Z.inj_mul 3 (b * b));
        apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  assert (Hq4 : Qinv ((4 * (Z.pos b * Z.pos b)) # 1) == (1 # (4 * (b * b)))%Q)
    by (rewrite <- (Pos2Z.inj_mul b b), <- (Pos2Z.inj_mul 4 (b * b));
        apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  assert (Hq12 : Qinv ((12 * (Z.pos b * Z.pos b)) # 1) == (1 # (12 * (b * b)))%Q)
    by (rewrite <- (Pos2Z.inj_mul b b), <- (Pos2Z.inj_mul 12 (b * b));
        apply qeqT_imp_qeq; apply dmew_Qinv_1p).
  pose proof (QleT'_to_Qle _ _
                (dmew_e_bnd b (Z.to_nat (Z.pos b) + 3)%nat
                (Nat.le_refl (Z.to_nat (Z.pos b) + 3)))) as He.
  pose proof (ir2_x_lb (Z.to_nat (Z.pos b) + 3)) as Hx_lb.
  pose proof (ir2_x_ub (Z.to_nat (Z.pos b) + 3) Hn13) as Hx_ub.
  pose proof (ir2_x_pos (Z.to_nat (Z.pos b) + 3)) as Hx_pos.
  pose proof (ir2_sq_ge2 (Z.to_nat (Z.pos b) + 3)) as Hx_sq.
  destruct (Qlt_bool 0%Q ((a # b)%Q)) eqn:Hpos.
  - (* q > 0 *)
    pose proof (lic_qlt_bool_true 0%Q ((a # b)%Q) Hpos) as Hq0.
    destruct (Qlt_bool (((a # b)%Q) * ((a # b)%Q)) 2%Q) eqn:H2b.
    + (* 分支二：q² < 2——x − q ≥ (2−q²)/3 ≥ 1/(3b²) > 1/(12b²) ≥ e 界 *)
      pose proof (lic_qlt_bool_true (((a # b)%Q) * ((a # b)%Q)) 2%Q H2b) as H2.
      exists (Z.to_nat (Z.pos b) + 3)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hqx : Qlt ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3))).
      { apply (ir2_lt_of_sq (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)).
        - apply Qlt_le_weak. exact Hx_pos.
        - apply Qlt_le_weak. exact Hq0.
        - exact (Qlt_le_trans (((a # b)%Q) * ((a # b)%Q)) 2%Q
                   (ir2_x (Z.to_nat (Z.pos b) + 3) * ir2_x (Z.to_nat (Z.pos b) + 3))
                   H2 Hx_sq). }
      rewrite (Qabs_Qminus ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3))).
      rewrite (ir2_abs_sub (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q))
        by (apply Qlt_le_weak; exact Hqx).
      apply (Qle_lt_trans (ir2_e (Z.to_nat (Z.pos b) + 3))
              ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
              ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
      * exact He.
      * apply (Qlt_le_trans ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
                ((Qinv ((3 * (Z.pos b * Z.pos b)) # 1))%Q)
                ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
        -- apply QltT_to_Qlt. apply dmew_Qinv_lt; nia.
        -- apply (Qle_trans ((Qinv ((3 * (Z.pos b * Z.pos b)) # 1))%Q)
                    ((((2%Q - (((a # b)%Q) * ((a # b)%Q)))%Q) * (1#3))%Q)
                    ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
           ++ pose proof H2 as H2z. unfold Qlt, Qmult in H2z.
              cbn [Qnum Qden Qinv] in H2z.
              assert (Hgap : (1 <= 2 * Z.pos (b * b) - a * a)%Z) by lia.
              rewrite Hq3. unfold Qle, Qmult, Qminus. cbn [Qnum Qden Qinv Qplus Qopp]. nia.
           ++ exact (ir2_gap_lower (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)
                       (Qlt_le_weak _ _ Hq0) (Qlt_le_weak _ _ Hqx)
                       Hx_ub Hx_sq H2).
    + (* q² ≥ 2：先以整隙排除 q² == 2，再入 q² > 2 两侧 *)
      pose proof (lic_qlt_bool_false_le (((a # b)%Q) * ((a # b)%Q)) 2%Q H2b)
        as Hge2.
      destruct (Qeq_dec (((a # b)%Q) * ((a # b)%Q)) 2%Q) as [Heq2 | Hne2].
      * exfalso. exact (ir2_no_sqrt2 ((a # b)%Q) Heq2).
      * destruct (Qlt_bool 2%Q (((a # b)%Q) * ((a # b)%Q))) eqn:H2lt.
        -- pose proof (lic_qlt_bool_true 2%Q (((a # b)%Q) * ((a # b)%Q)) H2lt)
             as Hlt2.
           destruct (Qlt_bool (3#2)%Q ((a # b)%Q)) eqn:H32b.
           ++ (* 分支四：q > 3/2——q − x ≥ q − 3/2 ≥ 1/(2b) > 1/(12b²) ≥ e 界 *)
              pose proof (lic_qlt_bool_true (3#2)%Q ((a # b)%Q) H32b) as H32.
              exists (Z.to_nat (Z.pos b) + 3)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hxq : Qlt (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)).
              { apply (Qle_lt_trans (ir2_x (Z.to_nat (Z.pos b) + 3)) (3#2)%Q ((a # b)%Q)).
                - exact Hx_ub.
                - exact H32. }
              rewrite (ir2_abs_sub ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3)))
                by (apply Qlt_le_weak; exact Hxq).
              assert (Hgap : (1 <= 2 * a - 3 * Z.pos b)%Z).
              { pose proof H32 as Hz32. unfold Qlt in Hz32.
                cbn [Qnum Qden Qinv] in Hz32. lia. }
              assert (Hq32 : Qle ((Qinv ((2 * Z.pos b) # 1))%Q)
                                  ((((a # b)%Q) - (3#2))%Q)).
              { rewrite Hq2. unfold Qle, Qminus. cbn [Qnum Qden Qinv Qplus Qopp]. nia. }
              assert (Hq32x : Qle ((((a # b)%Q) - (3#2))%Q)
                                   ((((a # b)%Q) - ir2_x (Z.to_nat (Z.pos b) + 3))%Q)).
              { unfold Qminus.
                pose proof (Qopp_le_compat (ir2_x (Z.to_nat (Z.pos b) + 3)) (3#2)%Q
                              Hx_ub) as Hneg.
                apply (Qplus_le_compat ((a # b)%Q) ((a # b)%Q)
                         (Qopp (3#2)) (Qopp (ir2_x (Z.to_nat (Z.pos b) + 3)))).
                + apply Qle_refl.
                + exact Hneg. }
              assert (Hlt12 : Qlt ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
                                   ((((a # b)%Q) - ir2_x (Z.to_nat (Z.pos b) + 3))%Q)).
              { apply (Qlt_le_trans ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
                        ((Qinv ((2 * Z.pos b) # 1))%Q)
                        ((((a # b)%Q) - ir2_x (Z.to_nat (Z.pos b) + 3))%Q)).
                - apply QltT_to_Qlt. apply dmew_Qinv_lt; nia.
                - exact (Qle_trans ((Qinv ((2 * Z.pos b) # 1))%Q)
                           ((((a # b)%Q) - (3#2))%Q)
                           ((((a # b)%Q) - ir2_x (Z.to_nat (Z.pos b) + 3))%Q)
                           Hq32 Hq32x). }
              exact (Qle_lt_trans (ir2_e (Z.to_nat (Z.pos b) + 3))
                      ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
                      ((((a # b)%Q) - ir2_x (Z.to_nat (Z.pos b) + 3))%Q) He Hlt12).
           ++ (* 分支三：2 < q² ∧ q ≤ 3/2——q − x ≥ (μ−δ)/3 ≥ 1/(4b²) > 1/(12b²)；
                 δ ≤ 1/(4b²) 走 dmew_delta_pow_inv＋dmew_pow4，收尾走
                 ir2_gap_upper_small（μ ≥ 1/b² 整隙肢为本件自建） *)
              pose proof (lic_qlt_bool_false_le (3#2)%Q ((a # b)%Q) H32b) as H32.
              exists (Z.to_nat (Z.pos b) + 3)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hdn : Qle (ir2_delta (Z.to_nat (Z.pos b) + 3))
                              ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)).
              { apply (Qle_trans (ir2_delta (Z.to_nat (Z.pos b) + 3))
                          (Qinv ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1))
                          ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)).
                - apply QleT'_to_Qle. apply dmew_delta_pow_inv. lia.
                - apply (ir2_inv_le ((4 * (Z.pos b * Z.pos b)) # 1)
                          ((Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 3))) # 1)).
                  + unfold Qlt. cbn [Qnum Qden Qinv]. nia.
                  + pose proof (dmew_pow4 (Z.to_nat (Z.pos b))) as H4.
                    apply (proj1 (Nat2Z.inj_le _ _)) in H4.
                    rewrite !Nat2Z.inj_mul in H4.
                    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H4.
                    rewrite Hbt in H4.
                    unfold Qle. cbn [Qnum Qden Qinv]. lia. }
              assert (Hmu : Qle ((Qinv ((Z.pos b * Z.pos b) # 1))%Q)
                              ((((a # b)%Q) * ((a # b)%Q) - 2%Q)%Q)).
              { pose proof Hlt2 as H2z. unfold Qlt, Qmult in H2z.
                cbn [Qnum Qden Qinv] in H2z.
                assert (Hgap : (1 <= a * a - 2 * Z.pos (b * b))%Z) by lia.
                rewrite Hq1. unfold Qle, Qmult, Qminus. cbn [Qnum Qden Qinv Qplus Qopp]. nia. }
              assert (Harith : Qle ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)
                                    (((2#5) * ((Qinv ((Z.pos b * Z.pos b) # 1)))%Q)%Q)).
              { rewrite Hq4, Hq1. unfold Qle, Qmult. cbn [Qnum Qden Qinv]. nia. }
              assert (Hmu5 : Qle (((2#5) * ((Qinv ((Z.pos b * Z.pos b) # 1)))%Q)%Q)
                                  (((2#5) * ((((a # b)%Q) * ((a # b)%Q)) - 2%Q))%Q)).
              { apply (ir2_mult_le_compat_l ((Qinv ((Z.pos b * Z.pos b) # 1)))
                         ((((a # b)%Q) * ((a # b)%Q) - 2%Q)) (2#5)).
                - exact Hmu.
                - unfold Qle. cbn [Qnum Qden Qinv]. lia. }
              assert (Hd5 : Qle (ir2_delta (Z.to_nat (Z.pos b) + 3))
                              (((2#5) * ((((a # b)%Q) * ((a # b)%Q)) - 2%Q))%Q)).
              { exact (Qle_trans (ir2_delta (Z.to_nat (Z.pos b) + 3))
                         ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)
                         (((2#5) * ((((a # b)%Q) * ((a # b)%Q)) - 2%Q))%Q)
                         Hdn (Qle_trans _ _ _ Harith Hmu5)). }
              assert (Hdlt : Qlt (ir2_delta (Z.to_nat (Z.pos b) + 3))
                               ((((a # b)%Q) * ((a # b)%Q) - 2%Q)%Q)).
              { apply (Qle_lt_trans (ir2_delta (Z.to_nat (Z.pos b) + 3))
                        ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)
                        ((((a # b)%Q) * ((a # b)%Q) - 2%Q)%Q)).
                - exact Hdn.
                - apply (Qlt_le_trans ((Qinv ((4 * (Z.pos b * Z.pos b)) # 1))%Q)
                           ((Qinv ((Z.pos b * Z.pos b) # 1))%Q)
                           ((((a # b)%Q) * ((a # b)%Q) - 2%Q)%Q)).
                  + apply QltT_to_Qlt. apply dmew_Qinv_lt; nia.
                  + exact Hmu. }
              assert (Hxq : Qlt (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)).
              { apply (ir2_lt_of_sq ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak. exact Hx_pos.
                - pose proof (lic_qlt_add_r (ir2_delta (Z.to_nat (Z.pos b) + 3))
                                ((((a # b)%Q) * ((a # b)%Q) - 2%Q)) 2%Q Hdlt)
                    as H1.
                  pose proof (lic_qlt_minus_add_r
                                (ir2_x (Z.to_nat (Z.pos b) + 3) * ir2_x (Z.to_nat (Z.pos b) + 3))
                                2%Q) as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (((a # b)%Q) * ((a # b)%Q)) 2%Q) as Hr2.
                  rewrite <- Hr1. rewrite <- Hr2. exact H1. }
              rewrite (ir2_abs_sub ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3)))
                by (apply Qlt_le_weak; exact Hxq).
              assert (Heq : (ir2_e (Z.to_nat (Z.pos b) + 3)
                             == ir2_delta (Z.to_nat (Z.pos b) + 3) * (1#2))%Q)
                by (unfold ir2_e; ring).
              rewrite Heq.
              apply (ir2_gap_upper_small (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q)
                       (ir2_delta (Z.to_nat (Z.pos b) + 3))).
              ** exact Hx_pos.
              ** exact Hq0.
              ** exact Hxq.
              ** exact H32.
              ** exact Hlt2.
              ** reflexivity.
              ** apply (ir2_delta_ge0 (Z.to_nat (Z.pos b) + 3)).
              ** exact Hd5.
        -- (* 2 ≤ q² 且 ¬(2 < q²)：q² == 2 与整隙矛盾 *)
           exfalso. apply Hne2.
           pose proof (lic_qlt_bool_false_le 2%Q (((a # b)%Q) * ((a # b)%Q)) H2lt)
             as Hle2.
           exact (Qle_antisym (((a # b)%Q) * ((a # b)%Q)) 2%Q Hle2 Hge2).

  - (* 分支一：q ≤ 0——x − q ≥ 7/5 > 1/(12b²) ≥ e 界 *)
    pose proof (lic_qlt_bool_false_le 0%Q ((a # b)%Q) Hpos) as Hq0.
    exists (Z.to_nat (Z.pos b) + 3)%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus ((a # b)%Q) (ir2_x (Z.to_nat (Z.pos b) + 3))).
    rewrite (ir2_abs_sub (ir2_x (Z.to_nat (Z.pos b) + 3)) ((a # b)%Q))
      by (apply (Qle_trans ((a # b)%Q) 0%Q (ir2_x (Z.to_nat (Z.pos b) + 3)));
          [exact Hq0 | apply Qlt_le_weak; exact Hx_pos]).
    apply (Qle_lt_trans (ir2_e (Z.to_nat (Z.pos b) + 3))
            ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q)
            ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
    + exact He.
    + apply (Qlt_le_trans ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q) ((7#5)%Q)
              ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
      * rewrite Hq12. unfold Qlt. cbn [Qnum Qden Qinv]. nia.
      * assert (Hxq5 : Qle ((7#5)%Q)
                         ((ir2_x (Z.to_nat (Z.pos b) + 3) - ((a # b)%Q))%Q)).
        { pose proof (Qopp_le_compat ((a # b)%Q) 0%Q Hq0) as Hnq.
          cbn [Qopp Z.opp] in Hnq.
          unfold Qminus.
          apply (Qle_trans ((7#5)%Q)
                  ((ir2_x (Z.to_nat (Z.pos b) + 3) + 0%Q)%Q)
                  ((ir2_x (Z.to_nat (Z.pos b) + 3) + (Qopp ((a # b)%Q)))%Q)).
          - rewrite Qplus_0_r. exact Hx_lb.
          - apply (Qplus_le_compat (ir2_x (Z.to_nat (Z.pos b) + 3))
                     (ir2_x (Z.to_nat (Z.pos b) + 3)) 0%Q (Qopp ((a # b)%Q)));
              [apply Qle_refl | exact Hnq]. }
        exact Hxq5.
Qed.

Print Assumptions dmew_e_pow_le.
Print Assumptions dmew_delta_pow_inv.
Print Assumptions dmew_e_bnd.
Print Assumptions dmew_escape_closed_window.
