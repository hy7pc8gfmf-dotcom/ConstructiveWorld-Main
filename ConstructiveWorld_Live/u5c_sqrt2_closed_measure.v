(* 五字段指针｜使命：√2 闭式分离常元主定理——首个显式构造性无理性测度。
   对任意有理数 q = a/b（b 为正分母），显式常元 c(q) = 1/(12·b²) 满足
   QltT 0 c 且 real_const c < |√2 − q|（Newton 序列极限的实度量）。此为
   u5c_inst_sqrt2.v 头注自标「闭式常元路线」的首个显式无理性测度（Liouville 型 下界 |√2 − a/b| > C/b² 的构造性实现），常元由 Qeq 确定、可提取可复算。
   证明结构：①统一逃逸窗口（n0 ≥ Z.to_nat b + 3）与 e 界 e(n0) ≤ 1/(12b²)；
   ②四分支边距链（全 Qle 链、证体内 Prop 合法）：
   分支一 q ≤ 0——|q−x| ≥ x ≥ 7/5 ≥ 1/(4b²)；分支二 q² < 2——|q−x| = x−q ≥
   (2−q²)/3 ≥ 1/(4b²)（整隙 2b²−a² ≥ 1，ir2_gap_lower 点态下界）；
   分支三 0 < q² 隙上且 q ≤ 3/2——|q−x| = q−x = (μ−δ)/(q+x) ≥ (μ−δ)/3 ≥ 1/(4b²)
   （μ = q²−2 ≥ 1/b² 整隙、δ = 2e ≤ 1/(6b²)、除法桥 bno_mul_div_self +
   ir2_sq_diff、ir2_inv_le 反向收尾）；分支四 q > 3/2——|q−x| ≥ q−3/2 ≥
   1/(2b) ≥ 1/(4b²)（整隙 2a−3b ≥ 1）；
   ③边距成形：lic_qlt_minus_add_r 移项＋dmcm_qle_add_cancel_r 得
   2c ≤ |q−x(n0)| − e(n0)，升 QleT' 形；④装配边距参数化桥
   dmec_escape_to_dist_any（任意 c ≤ 边距/2 皆分离），与 Qeq_refl 确定组装。
   推论 u5c_sqrt2_closed_measure_q 把主定理改写为任意 Q 的 q 形（QDen 确定）。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、SumInvFactEscape、
   UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_bridge、u5c_dm_escape_window、u5c_dm_escape_to_dist_any；
   Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。
   对标行：u5c_bridge.v u5c_escape_to_dist（存在型常数→闭式常元）；
   UpReqSqrt3Irrational.v ir2_gap_lower、ir2_x_lb/ub、ir2_sq_ge2、 ir2_no_sqrt2、ir2_inv_le、ir2_abs_sub、ir2_qpos_add、ir2_sq_diff；
   u5c_dm_escape_window.v dmew_escape_closed_window、dmew_e_bnd；
   u5c_dm_escape_to_dist_any.v dmec_escape_to_dist_any。
   构造性注记：语句面全 Set 层（sigT/prod/QltT/QleT'/real_lt），零 Prop
   前提位；证明体内 Prop 推导合法（Qle 链与整数整隙）；常元正性
   0 < 1/(12b²) 与四分支边距全为具体数值计算（cbn + nia/lia），零经典
   逻辑、零承认、零全局假设；定义面仅微转换 lemma，无新 Inductive。
   编译配方：source Live/toolchain/env.sh 后
   rocq c -native-compiler no -q -Q . "" u5c_sqrt2_closed_measure.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_bridge.
Require Import u5c_dm_escape_window.
Require Import u5c_dm_escape_to_dist_any.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S1：自携微转换：Qle 右端加项消去（边距成形用）                        *)
(* ============================================================ *)

Lemma dmcm_qle_add_cancel_r : forall x y z : Q, QleT' (x + z)%Q (y + z)%Q -> QleT' x y.
Proof.
  intros [xn xd] [yn yd] [zn zd] H.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ H) as Hle.
  unfold Qle, Qplus in Hle |- *.
  cbn [Qnum Qden Qplus] in Hle |- *. nia.
Qed.

(* ============================================================ *)
(* S2：四分支边距核（除 e 界假设外全自足；数值链经 /tmp 预检验证）          *)
(* ============================================================ *)

Lemma dmcm_margin_closed : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat -> QleT' (ir2_e n0) ((1 # (12 * (b * b)))%Q) ->
  QleT' (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q + ir2_e n0)%Q)
        (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hge Heb.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ Heb) as Heb'.
  assert (Hz : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  pose proof (ir2_x_lb n0) as Hxlb.
  pose proof (ir2_x_ub n0 Hge) as Hxub.
  pose proof (ir2_sq_ge2 n0) as Hx2.
  pose proof (ir2_x_pos n0) as Hxpos.
  assert (Hcce : Qle (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q)
                       + ir2_e n0)%Q
                     ((1 # (4 * (b * b)))%Q)).
  { apply (Qle_trans _ (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q)
                         + (1 # (12 * (b * b)))%Q)).
    - apply Qplus_le_compat; [apply Qle_refl | exact Heb'].
    - apply qeq_le.
      unfold Qeq, Qplus, Qmult.
      cbn [Qnum Qden Qplus Qmult].
      rewrite ?Pos2Z.inj_mul. ring. }
  destruct (Qlt_le_dec 0%Q (a # b)%Q) as [Hq0 | Hq0].
  - destruct (Qlt_le_dec ((a # b)%Q * (a # b)%Q) 2%Q) as [Hlt2 | Hge2].
    + (* 分支二：q² < 2 *)
      assert (Hqx : Qle (a # b)%Q (ir2_x n0)).
      { destruct (Qlt_le_dec (ir2_x n0) (a # b)%Q) as [Hxq | Hle].
        - exfalso.
          apply (Qlt_not_le ((a # b)%Q * (a # b)%Q) 2%Q Hlt2).
          apply (Qle_trans 2%Q (ir2_x n0 * ir2_x n0) ((a # b)%Q * (a # b)%Q)).
          + exact Hx2.
          + apply (ir2_sq_mono (a # b)%Q (ir2_x n0)).
            * apply Qlt_le_weak. exact Hxpos.
            * apply Qlt_le_weak. exact Hxq.
        - exact Hle. }
      rewrite (Qabs_Qminus (a # b)%Q (ir2_x n0)).
      rewrite (ir2_abs_sub (ir2_x n0) (a # b)%Q Hqx).
      apply (Qle_trans _ ((1 # (4 * (b * b)))%Q)).
      * exact Hcce.
      * apply (Qle_trans _ (((2 - ((a # b)%Q * (a # b)%Q)) * (1#3))%Q)).
        -- assert (Hzint : (a * a < 2 * (Z.pos b * Z.pos b))%Z).
           { pose proof Hlt2 as Hh. unfold Qlt, Qmult in Hh.
             cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh. nia. }
           unfold Qle, Qminus, Qmult, Qplus, Qopp;
             cbn [Qnum Qden Qminus Qmult Qplus Qopp];
             rewrite ?Pos2Z.inj_mul; nia.
        -- exact (ir2_gap_lower (ir2_x n0) (a # b)%Q
                    (Qlt_le_weak 0%Q (a # b)%Q Hq0) Hqx Hxub Hx2 Hlt2).
    + destruct (Qle_lt_or_eq 2%Q ((a # b)%Q * (a # b)%Q) Hge2) as [Hlt2 | Heq].
      * destruct (Qlt_le_dec (3#2) (a # b)%Q) as [Hqgt | Hq32].
        -- (* 分支四：q > 3/2 *)
           assert (Hside : Qle (ir2_x n0) (a # b)%Q).
           { apply (Qle_trans (ir2_x n0) (3#2) (a # b)%Q);
               [exact Hxub | apply Qlt_le_weak; exact Hqgt]. }
           rewrite (ir2_abs_sub (a # b)%Q (ir2_x n0) Hside).
           apply (Qle_trans _ ((1 # (2 * b))%Q)).
           { apply (Qle_trans _ ((1 # (4 * (b * b)))%Q)).
             - exact Hcce.
             - unfold Qle; cbn [Qnum Qden];
                 rewrite ?Pos2Z.inj_mul; nia. }
           apply (Qle_trans _ (((a # b)%Q - (3#2))%Q)).
           { assert (Hgap : (3 * Z.pos b < 2 * a)%Z).
             { pose proof Hqgt as Hh. unfold Qlt, Qmult in Hh.
               cbn [Qnum Qden] in Hh. nia. }
             unfold Qle, Qminus, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qplus Qopp Qmult];
               rewrite ?Pos2Z.inj_mul; nia. }
           apply (Qplus_le_compat (a # b)%Q (a # b)%Q (- (3#2))%Q (- ir2_x n0)%Q).
           { apply Qle_refl. }
           { apply (Qopp_le_compat (ir2_x n0) (3#2)%Q Hxub). }
        -- (* 分支三：q ≤ 3/2 且 q² > 2 *)
           assert (Hzpos : (2 * (Z.pos b * Z.pos b) < a * a)%Z).
           { pose proof Hlt2 as Hh. unfold Qlt, Qmult in Hh.
             cbn [Qnum Qden] in Hh. rewrite (Pos2Z.inj_mul b b) in Hh. nia. }
           assert (Hmu : Qle (1 # (b * b)) ((a # b)%Q * (a # b)%Q - 2%Q)%Q).
           { unfold Qle, Qminus, Qmult, Qplus, Qopp;
               cbn [Qnum Qden Qminus Qmult Qplus Qopp];
               rewrite ?Pos2Z.inj_mul; nia. }
           assert (Ed : (ir2_delta n0 == (2#1) * ir2_e n0)%Q)
             by (unfold ir2_e; ring).
           assert (Hdel : Qle (ir2_delta n0) ((1 # (6 * (b * b)))%Q)).
           { rewrite Ed. apply (Qle_trans _ ((2#1) * ((1 # (12 * (b * b)))%Q))).
             - apply (ir2_mult_le_compat_l (ir2_e n0)
                        ((1 # (12 * (b * b)))%Q) (2#1));
                 [exact Heb' | unfold Qle; cbn [Qnum Qden]; lia].
             - apply qeq_le. unfold Qeq, Qmult;
                 cbn [Qnum Qden Qmult]; rewrite ?Pos2Z.inj_mul; ring. }
           assert (Hmud : Qle (((1 # (b * b))%Q - (1 # (6 * (b * b)))%Q))
                              ((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q)).
           { apply (Qplus_le_compat (1 # (b * b))
                      ((a # b)%Q * (a # b)%Q - 2%Q)%Q
                      (- (1 # (6 * (b * b))))%Q (- ir2_delta n0)%Q).
             - exact Hmu.
             - apply (Qopp_le_compat (ir2_delta n0) ((1 # (6 * (b * b)))%Q)
                        Hdel). }
           assert (HDpos : Qle 0%Q
                              ((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q)).
           { apply (Qle_trans 0%Q
                  (((1 # (b * b))%Q - (1 # (6 * (b * b)))%Q))%Q _).
             - unfold Qle, Qminus, Qmult, Qplus, Qopp;
                 cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; nia.
             - exact Hmud. }
           assert (Hqxp : Qlt 0%Q ((a # b)%Q + ir2_x n0)%Q).
           { apply (ir2_qpos_add (a # b)%Q (ir2_x n0));
               [exact Hq0 | exact Hxpos]. }
           assert (Hqxn : ~ ((a # b)%Q + ir2_x n0 == 0%Q)).
           { intro Hc. apply (Qlt_not_eq 0%Q ((a # b)%Q + ir2_x n0) Hqxp).
             apply Qeq_sym. exact Hc. }
           assert (Hbridge : (((a # b)%Q - ir2_x n0) ==
              ((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q
                * Qinv ((a # b)%Q + ir2_x n0)))%Q).
           { pose proof (bno_mul_div_self ((a # b)%Q + ir2_x n0) Hqxn) as Hbd.
             unfold Qdiv in Hbd. rewrite Qmult_1_l in Hbd.
             assert (Hpm : (((((a # b)%Q - ir2_x n0) * ((a # b)%Q + ir2_x n0))
                              * Qinv ((a # b)%Q + ir2_x n0))
                             == ((a # b)%Q - ir2_x n0))%Q).
             { rewrite <- (Qmult_assoc ((a # b)%Q - ir2_x n0)
                            ((a # b)%Q + ir2_x n0)
                            (Qinv ((a # b)%Q + ir2_x n0))).
               rewrite Hbd. apply Qmult_1_r. }
             rewrite ir2_sq_diff in Hpm.
             assert (Hsh : (((a # b)%Q * (a # b)%Q - ir2_x n0 * ir2_x n0)
                             == (((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0))%Q)
               by (unfold ir2_delta; ring).
             rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
           assert (Hqxb : Qle ((a # b)%Q + ir2_x n0) (3#1)%Q).
           { apply (Qle_trans _ (((3#2) + (3#2))%Q)).
             - apply (Qplus_le_compat (a # b)%Q (3#2)%Q (ir2_x n0) (3#2)%Q);
                 [exact Hq32 | exact Hxub].
             - apply qeq_le. reflexivity. }
           assert (Hinv : Qle (Qinv (3#1)) (Qinv ((a # b)%Q + ir2_x n0))).
           { apply (ir2_inv_le ((a # b)%Q + ir2_x n0) (3#1)%Q);
               [exact Hqxp | exact Hqxb]. }
           assert (Hd3 : Qle ((1 # (4 * (b * b)))%Q)
              (((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q) * (1#3))%Q).
           { apply (Qle_trans _
                ((((1 # (b * b))%Q - (1 # (6 * (b * b)))%Q)) * (1#3))%Q).
             - unfold Qle, Qminus, Qmult, Qplus, Qopp;
                 cbn [Qnum Qden Qminus Qmult Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; nia.
             - apply (Qmult_le_compat_r _ _ (1#3));
                 [exact Hmud | unfold Qle; cbn [Qnum Qden]; lia]. }
           assert (Hbige : Qle
              (((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q) * (1#3))%Q
              ((a # b)%Q - ir2_x n0)%Q).
           { rewrite Hbridge.
             assert (E3 : ((1#3)%Q == Qinv (3#1))) by reflexivity.
             rewrite E3.
             apply (ir2_mult_le_compat_l (Qinv (3#1))
                      (Qinv ((a # b)%Q + ir2_x n0))
                      ((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q)).
             - exact Hinv.
             - exact HDpos. }
           assert (He0 : Qle 0%Q (ir2_e n0)).
           { unfold ir2_e.
             apply (Qle_trans _ (((1#2) * 0%Q)%Q)).
             - apply qeq_le. reflexivity.
             - apply (ir2_mult_le_compat_l 0%Q (ir2_delta n0) (1#2));
                 [exact (ir2_delta_ge0 n0) | unfold Qle; cbn [Qnum Qden]; lia]. }
           assert (Hsum0 : Qle 0%Q (((1 # (12 * (b * b)))%Q
                                      + (1 # (12 * (b * b)))%Q
                                      + ir2_e n0)%Q)).
           { apply (Qle_trans _ (0%Q + 0%Q)%Q).
             - apply qeq_le. reflexivity.
             - apply (Qplus_le_compat 0%Q
                        (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q))
                        0%Q (ir2_e n0)).
               + apply (Qle_trans 0%Q (0%Q + 0%Q)%Q _).
                 * apply qeq_le. reflexivity.
                 * apply (Qplus_le_compat 0%Q ((1 # (12 * (b * b)))%Q) 0%Q
                            ((1 # (12 * (b * b)))%Q));
                     [unfold Qle; cbn [Qnum Qden]; lia
                     | unfold Qle; cbn [Qnum Qden]; lia].
               + exact He0. }
           assert (Hge0 : Qle 0%Q ((a # b)%Q - ir2_x n0)%Q).
           { apply (Qle_trans 0%Q
                  (((1 # (12 * (b * b)))%Q + (1 # (12 * (b * b)))%Q
                    + ir2_e n0)%Q) ((a # b)%Q - ir2_x n0)%Q).
             - exact Hsum0.
             - apply (Qle_trans _ ((1 # (4 * (b * b)))%Q)).
               + exact Hcce.
               + apply (Qle_trans _ (((((a # b)%Q * (a # b)%Q - 2%Q)
                                        - ir2_delta n0)%Q) * (1#3))%Q).
                 * exact Hd3.
                 * exact Hbige. }
           assert (Hside : Qle (ir2_x n0) (a # b)%Q).
           { apply (Qle_trans (ir2_x n0)
                     (((a # b)%Q - ir2_x n0 + ir2_x n0)%Q) (a # b)%Q).
             - apply (Qle_trans (ir2_x n0) (0%Q + ir2_x n0)%Q
                      (((a # b)%Q - ir2_x n0 + ir2_x n0)%Q)).
               + rewrite Qplus_0_l. apply Qle_refl.
               + apply (Qplus_le_compat 0%Q ((a # b)%Q - ir2_x n0)%Q
                          (ir2_x n0) (ir2_x n0));
                   [exact Hge0 | apply Qle_refl].
             - apply qeq_le.
               unfold Qeq, Qminus, Qplus, Qopp;
                 cbn [Qnum Qden Qplus Qopp];
                 rewrite ?Pos2Z.inj_mul; ring. }
           rewrite (ir2_abs_sub (a # b)%Q (ir2_x n0) Hside).
           exact (Qle_trans _
                    (((((a # b)%Q * (a # b)%Q - 2%Q) - ir2_delta n0)%Q)
                      * (1#3)) _
                    (Qle_trans _ ((1 # (4 * (b * b)))%Q) _ Hcce Hd3)
                    Hbige).
      * exfalso. exact (ir2_no_sqrt2 (a # b)%Q (Qeq_sym _ _ Heq)).
  - (* 分支一：q ≤ 0 *)
    assert (Hqx : Qle (a # b)%Q (ir2_x n0)).
    { apply (Qle_trans (a # b)%Q 0%Q (ir2_x n0)).
      - exact Hq0.
      - apply (Qle_trans 0%Q (7#5) (ir2_x n0)).
        + unfold Qle. cbn [Qnum Qden]. lia.
        + exact Hxlb. }
    rewrite (Qabs_Qminus (a # b)%Q (ir2_x n0)).
    rewrite (ir2_abs_sub (ir2_x n0) (a # b)%Q Hqx).
    apply (Qle_trans _ ((1 # (4 * (b * b)))%Q)).
    + exact Hcce.
    + apply (Qle_trans _ (7#5)%Q).
      * unfold Qle; cbn [Qnum Qden]; rewrite ?Pos2Z.inj_mul; nia.
      * pose proof (Qopp_le_compat (a # b)%Q 0%Q Hq0) as Hnq.
        cbn [Qopp Z.opp] in Hnq.
        apply (Qle_trans (7#5) (ir2_x n0)
                ((ir2_x n0 + (- (a # b)))%Q)).
        { exact Hxlb. }
        { apply (Qle_trans (ir2_x n0) ((ir2_x n0 + 0%Q)%Q)
                   ((ir2_x n0 + (- (a # b)))%Q)).
          - rewrite Qplus_0_r. apply Qle_refl.
          - apply (Qplus_le_compat (ir2_x n0) (ir2_x n0) 0%Q
                     (- (a # b))%Q); [apply Qle_refl | exact Hnq]. }
Qed.


(* 装配助手：分离引理输出→定冠分量（结论取字面积型，绕 And 定义的展开） *)
Lemma dmcm_witness_assembly : forall (q : Q)
  (Hres : sigT (fun c0 : Q => And (QltT 0 c0)
             (real_lt (real_const c0)
                (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                                   (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                  (real_const q))))),
  QltT 0 (projT1 Hres) *
      (real_lt (real_const (projT1 Hres))
         (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                            (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
            (real_const q))).
Proof. intros q Hres. exact (projT2 Hres). Qed.

(* ============================================================ *)
(* S3：主定理（闭式常元 + Qeq 确定 + 实度量分离）                        *)
(* ============================================================ *)

Theorem u5c_sqrt2_closed_measure : forall (a : Z) (b : positive),
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c ((1 # (12 * (b * b)))%Q))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                              (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
               (real_const ((a # b)%Q)))))).
Proof.
  intros a b.
  destruct (dmew_escape_closed_window a b) as [n0 [Hge Hesc]].
  pose proof (dmew_e_bnd b n0 Hge) as Heb.
  (* 最小适配（预置 Heb 桥）：B2 版 dmew_e_bnd 的 e 界终形为
     Qinv ((12 * (Z.pos b * Z.pos b)) # 1)（Z 层非构造子积，Qinv match 磨损），
     与本件 QDen 形 (1 # (12 * (b * b))) 不可转换，一句 Qeq 换算桥接通。 *)
  assert (Hebq : Qinv ((12 * (Z.pos b * Z.pos b)) # 1) == (1 # (12 * (b * b)))%Q).
  { replace (12 * (Z.pos b * Z.pos b))%Z with (Z.pos (12 * (b * b)))%Z.
    - reflexivity.
    - rewrite (Pos2Z.inj_mul 12 (b * b)). rewrite (Pos2Z.inj_mul b b). reflexivity. }
  (* 最小适配注记：Qeq 桥不可 rewrite 进 QleT'（池自定义 Set＝
     Id (Qle_bool …) true，无 morphism 实例，两轮排查 :332 失配源）——
     沿窗内绿形态降 Qle 层 Qle_trans＋qeq_le 过桥再升回。 *)
  pose proof (QleT'_to_Qle _ _ Heb) as Hebl.
  clear Heb.
  assert (Heb : QleT' (ir2_e n0) ((1 # (12 * (b * b)))%Q)).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))).
    - exact Hebl.
    - apply qeq_le. exact Hebq. }
  clear Hebl.
  assert (Hn01 : (1 <= n0)%nat) by lia.
  assert (Hc0 : QltT 0 ((1 # (12 * (b * b)))%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    rewrite ?Pos2Z.inj_mul. pose proof (Pos2Z.is_pos b). lia. }
  pose proof (dmcm_margin_closed a b n0 Hn01 Heb) as HrawT'.
  pose proof (QleT'_to_Qle _ _ HrawT') as Hraw.
  rewrite <- (lic_qlt_minus_add_r (Qabs (((a # b)%Q - ir2_x n0)%Q))
                (ir2_e n0)) in Hraw.
  assert (Hmargin : QleT' (((1 # (12 * (b * b)))%Q
                             + (1 # (12 * (b * b)))%Q))
                          (((Qabs (((a # b)%Q - ir2_x n0)%Q))
                             - ir2_e n0)%Q)).
  { exact (dmcm_qle_add_cancel_r _ _ (ir2_e n0) (Qle_to_QleT' _ _ Hraw)). }
  (* 最小适配：dmec 应用内联至使用点——pose 变量会挡
     projT1 的 δ-ι 归约，内联后Defined 版 dmec 的见证直达显式常元。 *)
  exists ((1 # (12 * (b * b)))%Q).
  split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT. apply Qeq_refl.
    + exact (snd (dmcm_witness_assembly (a # b)%Q
           (dmec_escape_to_dist_any ir2_x ir2_e ir2_tail ir2_vanish
              (a # b)%Q n0 Hn01 Hesc ((1 # (12 * (b * b)))%Q) Hc0 Hmargin))).
Qed.

(* ============================================================ *)
(* S4：推论（q 形：QDen 确定）                                        *)
(* ============================================================ *)

(* 语句面修复申报（响亮，同 √3 件修复之先例）：任务指令冻结的
   (1 # (12 * (QDen q * QDen q)))%Q 经实测无法 typecheck（本环境 QDen q : Z，
   # 右元须 positive），按最小修复取合法 Qinv 左元形 Qinv ((12 * (QDen q *
   QDen q)) # 1)（有理数值恒同），证体走 u5c_sqrt2_closed_measure 直装
   ＋ qinv-12bb 型换算桥收尾。 *)
Theorem u5c_sqrt2_closed_measure_q : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (And (QeqT c (Qinv ((12 * (QDen q * QDen q)) # 1)))
         (real_lt (real_const c)
            (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                              (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
               (real_const q))))).
Proof.
  intro q. destruct q as [a b].
  pose proof (u5c_sqrt2_closed_measure a b) as H.
  destruct H as [c [Hc0 [Heq Hlt]]].
  exists c. split.
  - exact Hc0.
  - split.
    + apply qeq_imp_qeqT.
      pose proof (qeqT_imp_qeq _ _ Heq) as Heq'.
      rewrite Heq'. apply Qeq_sym.
      apply (Qeq_trans _ (Qinv ((12 * (Z.pos b * Z.pos b)) # 1))).
      * reflexivity.
      * replace (12 * (Z.pos b * Z.pos b))%Z with (Z.pos (12 * (b * b)))%Z.
        -- reflexivity.
        -- rewrite (Pos2Z.inj_mul 12 (b * b)). rewrite (Pos2Z.inj_mul b b).
           reflexivity.
    + exact Hlt.
Qed.

From Stdlib Require Import Extraction.
Separate Extraction u5c_sqrt2_closed_measure u5c_sqrt2_closed_measure_q.

Print Assumptions u5c_sqrt2_closed_measure.
Print Assumptions u5c_sqrt2_closed_measure_q.
