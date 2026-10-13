(* ===================================================================== *)
(*  abl_z3_decay.v —— ζ(3) 塔衰减估计面（截断被积族逐点封顶+立方竞争+分离）   *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    在 [0,1]³ 上建立截断被积式族 F_{n,M}(x,y,z)（zb3_beval_l 形）的       *)
(*    双侧控制：非负性与锐权上界 F_{m+1,M}(x,y,z) ≤ (1/4)·(1/40)^m          *)
(*    （上确界范数以逐点 ∀ 形作构造性渲染，(1−xyz)^{m+2}·部分和 ≤ 1 的      *)
(*    级数除法自由上界与逐点衰减 4·40^m·N^{m+1} ≤ T^{m+2} 复合）。另给出    *)
(*    终装配所需的增长率竞争判定 27^(m+1)·(1/4)(1/40)^m =                  *)
(*    (27/4)·(27/40)^m < 1（m ≥ 5），与立方整性分离面 d³·I_{m+1} < 1：      *)
(*    其中 d 的具体上界与逐点到积分的上界过渡以显式前提给出（ζ(2) 面        *)
(*    sep_small 同款接口形），相应引理到位后按同型实例化。                  *)
(*  依赖：                                                            *)
(*    缓存根 S01_BaseRing S02_CauchyComplete S03_QExp；池内                *)
(*    abl_z2_truncfam（zb2_ps_bound）、abl_z2_itg_carrier                  *)
(*    （zb2_q_pow_mul）、abl_z3_pointwise（逐点衰减机）、                   *)
(*    abl_z3_itg_carrier（zb3_beval_l/zb3_Isum）。零实数层、零经典逻辑。    *)
(*  对标：                                                            *)
(*    Beukers 1979 的 ζ(3) 被积式逐点估计与 lcm³ 增长率竞争步               *)
(*    （Hanson 1972：lcm(1,…,n) ≤ 3ⁿ）。                                   *)
(*  构造性：                                                          *)
(*    零假设声明；主语句面取 Set 层见证型 QleT'/QltT；情形分析经           *)
(*    Qlt_le_dec 与 le_lt_dec 的可判定分情况完成。                         *)
(* ===================================================================== *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" abl_z3_decay.v（经温控包裹）。            *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier.
Require Import abl_z2_pointwise.
Require Import abl_z3_pointwise abl_z3_itg_carrier.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 基础档：幂的正性、单位幂与正因子消去                                 *)
(* ===================================================================== *)

(* 幂的严格正性：0 < z ⟹ 0 < z^k *)
Lemma zb3_dc_qp_pos : forall (k : nat) (z : Q), 0 < z -> QltT 0 (q_pow z k).
Proof.
  intros k z Hz. induction k as [| k IH].
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - apply Qlt_to_QltT. cbn [q_pow].
    apply (Qmult_lt_0_compat z (q_pow z k) Hz (QltT_to_Qlt _ _ IH)).
Qed.

(* 单位幂：1^k == 1 *)
Lemma zb3_dc_qp_one : forall k : nat, q_pow 1 k == 1.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qmult_1_l. exact IH.
Qed.

(* 正因子消去：0 < p 且 a·p ≤ p ⟹ a ≤ 1 *)
Lemma zb3_dc_cancel_one : forall a p : Q, 0 < p -> a * p <= p -> a <= 1.
Proof.
  intros a p Hp H.
  destruct (Qlt_le_dec 1 a) as [Hgt | Hle].
  - exfalso.
    assert (Hlt : 1 * p < a * p) by (apply (Qmult_lt_compat_r 1 a p); assumption).
    assert (Hcon : a * p <= 1 * p).
    { assert (H1 : p == 1 * p) by ring.
      apply (Qle_trans (a * p) p (1 * p)).
      - exact H.
      - exact (zb2_le_eq p (1 * p) H1). }
    exact (Qlt_not_le (1 * p) (a * p) Hlt Hcon).
  - exact Hle.
Qed.

(* 三因子缩移：b·c ≤ 1 且 0 ≤ a ⟹ a·b·c ≤ a *)
Lemma zb3_dc_mul_le_shift : forall a b c : Q,
  b * c <= 1 -> 0 <= a -> a * b * c <= a.
Proof.
  intros a b c Hbc Ha.
  assert (Hq := Qmult_le_compat_r (b * c) 1 a Hbc Ha).
  rewrite Qmult_1_l in Hq.
  assert (E : a * b * c == (b * c) * a) by ring.
  rewrite E. exact Hq.
Qed.

(* 权重非负：0 ≤ (1/4)·(1/40)^m *)
Lemma zb3_dc_weight_ge0 : forall m : nat, QleT' 0 ((1#4) * q_pow (1#40) m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply q_pow_nonneg. unfold Qle. simpl. lia.
Qed.

(* zb2_pow ↔ q_pow 换形 *)
Lemma zb3_dc_pow_cv : forall (t : Q) (k : nat), zb2_pow t k == q_pow t k.
Proof.
  intros t k. induction k as [| k IH].
  - reflexivity.
  - cbn [zb2_pow q_pow]. rewrite IH. ring.
Qed.

(* ===================================================================== *)
(* §A 正性面：部分和与截断被积式族的非负性                                 *)
(* ===================================================================== *)

(* 部分和非负性：0 ≤ t ⟹ 0 ≤ Σ_{m≤M} C(n+m,n)·t^m *)
Lemma zb3_dc_ps_ge0 : forall (n M : nat) (t : Q), 0 <= t -> QleT' 0 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply Qle_to_QleT'. rewrite zb2_ps_zero. exact zb2_0_le_1.
  - apply Qle_to_QleT'. rewrite zb2_ps_unfold.
    apply (Qle_trans 0 (0 + 0)
             (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))).
    + rewrite Qplus_0_l. apply Qle_refl.
    + apply (Qplus_le_compat 0 (zb2_ps n M t) 0
               ((Z.of_nat (bkC (n + Datatypes.S M) n) # 1) * q_pow t (Datatypes.S M))).
      * exact (QleT'_to_Qle _ _ IH).
      * apply Qmult_le_0_compat.
        -- exact (QleT'_to_Qle _ _ (zb2_bkC_Q_nonneg (n + Datatypes.S M) n)).
        -- apply q_pow_nonneg. exact Ht.
Qed.

(* 截断被积式族在立方上的非负性（逐点） *)
Lemma zb3_dc_carrier_ge0 : forall (n M : nat) (x y z : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> 0 <= z -> z <= 1 ->
  QleT' 0 (zb3_beval_l (zb3_segl n M) x y z).
Proof.
  intros n M x y z Hx1 Hx2 Hy1 Hy2 Hz1 Hz2.
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply (zb2_le_sub z 1); exact Hz2).
  assert (HA : 0 <= q_pow (x * (1 - x)) n)
    by (apply q_pow_nonneg; apply (zb2_mult2_ge0 x (1 - x)); assumption).
  assert (HB : 0 <= q_pow (y * (1 - y)) n)
    by (apply q_pow_nonneg; apply (zb2_mult2_ge0 y (1 - y)); assumption).
  assert (HC : 0 <= q_pow (z * (1 - z)) n)
    by (apply q_pow_nonneg; apply (zb2_mult2_ge0 z (1 - z)); assumption).
  assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
  assert (Hxyz0 : 0 <= x * y * z)
    by (apply (Qmult_le_0_compat (x * y) z); assumption).
  assert (HD : 0 <= zb2_ps n M (x * y * z)).
  { pose proof (zb3_dc_ps_ge0 n M (x * y * z) Hxyz0) as HDt.
    exact (QleT'_to_Qle _ _ HDt). }
  pose proof (zb3_beval_segl n M x y z) as Hseg.
  apply Qle_to_QleT'. rewrite Hseg.
  assert (HAB : 0 <= q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
    by (apply Qmult_le_0_compat; assumption).
  apply (Qmult_le_0_compat
           (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n * q_pow (z * (1 - z)) n)
           (zb2_ps n M (x * y * z))).
  - apply (Qmult_le_0_compat (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
                             (q_pow (z * (1 - z)) n))
    ; [ exact HAB | exact HC ].
  - exact HD.
Qed.

(* ===================================================================== *)
(* §B 锐权面：截断被积式族的逐点上界 (1/4)(1/40)^m                         *)
(* ===================================================================== *)

(* 主定理（锐权面）：对指数 n = m+1 档与一切 x y z ∈ [0,1]³，
   截断被积式 F_{m+1,M}(x,y,z) ≤ (1/4)·(1/40)^m。
   链：级数除法自由上界 (1−xyz)^{m+2}·Σ ≤ 1 与逐点衰减
   4·40^m·N^{m+1} ≤ T^{m+2} 复合，按 T = 1−xyz 的符号分情况判定。 *)
Theorem zb3_dc_carrier_decay : forall (m M : nat) (x y z : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> 0 <= z -> z <= 1 ->
  QleT' (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z)
        ((1#4) * q_pow (1#40) m).
Proof.
  intros m M x y z Hx1 Hx2 Hy1 Hy2 Hz1 Hz2.
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply (zb2_le_sub z 1); exact Hz2).
  assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
  assert (Hxy1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
  assert (Hxyz0 : 0 <= x * y * z)
    by (apply (Qmult_le_0_compat (x * y) z); assumption).
  assert (Hxyz1 : x * y * z <= 1)
    by (apply (zb2_xy_le_1 (x * y) z)
       ; [ exact Hxy0 | exact Hxy1 | exact Hz1 | exact Hz2 ]).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x * y * z)
                (conj Hxyz0 Hxyz1)) as HpsT.
  pose proof (QleT'_to_Qle _ _ HpsT) as Hps.
  pose proof (zb3_beval_segl (Datatypes.S m) M x y z) as Hseg.
  assert (Hmerge : q_pow (x * (1 - x)) (Datatypes.S m)
                * q_pow (y * (1 - y)) (Datatypes.S m)
                * q_pow (z * (1 - z)) (Datatypes.S m)
                == q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)).
  { rewrite <- (zb2_q_pow_mul (x * (1 - x)) (y * (1 - y)) (Datatypes.S m)).
    rewrite <- (zb2_q_pow_mul (x * (1 - x) * (y * (1 - y))) (z * (1 - z)) (Datatypes.S m)).
    apply q_pow_wd. ring. }
  rewrite Hmerge in Hseg.
  assert (HN0 : 0 <= x * (1 - x) * y * (1 - y) * z * (1 - z)).
  { assert (HA : 0 <= x * (1 - x)) by (apply zb2_mult2_ge0; assumption).
    assert (HB : 0 <= y * (1 - y)) by (apply zb2_mult2_ge0; assumption).
    assert (HC : 0 <= z * (1 - z)) by (apply zb2_mult2_ge0; assumption).
    assert (Hpre : 0 <= (x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z)))).
    { apply (Qmult_le_0_compat (x * (1 - x)) ((y * (1 - y)) * (z * (1 - z))))
      ; [ exact HA
        | apply (Qmult_le_0_compat (y * (1 - y)) (z * (1 - z)))
        ; [ exact HB | exact HC ] ]. }
    apply (zb2_ge0_wd ((x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z))))
                      (x * (1 - x) * y * (1 - y) * z * (1 - z)))
    ; [ ring | exact Hpre ]. }
  assert (HK0 : 0 <= q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))
    by (apply q_pow_nonneg; exact HN0).
  (* (A)：T^{m+2}·F ≤ N^{m+1} *)
  assert (HA : q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
               * zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z
            <= q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)).
  { assert (Hrw : q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                  * zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z
               == (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                   * zb2_ps (Datatypes.S m) M (x * y * z))
                  * q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))
      by (rewrite Hseg; ring).
    rewrite Hrw.
    apply (Qle_trans _ (1 * q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))).
    - apply (Qmult_le_compat_r
               (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                * zb2_ps (Datatypes.S m) M (x * y * z))
               1
               (q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))
               Hps HK0).
    - assert (H1K : 1 * q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)
                 == q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)) by ring.
      rewrite H1K. apply Qle_refl. }
  (* (B)：4·40^m·N^{m+1} ≤ T^{m+2}（既有逐点衰减，幂记号统一为 q_pow） *)
  pose proof (zb3_pointwise_decay m x y z
                (conj Hx1 Hx2) (conj Hy1 Hy2) (conj Hz1 Hz2)) as HdecT.
  pose proof (zb2_qle_to_Qle _ _ HdecT) as Hdec0.
  rewrite (zb3_dc_pow_cv 40 m) in Hdec0.
  rewrite (zb3_dc_pow_cv (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)) in Hdec0.
  rewrite (zb3_dc_pow_cv (1 - x * y * z) (Datatypes.S (Datatypes.S m))) in Hdec0.
  assert (HK400 : 0 <= 4 * q_pow 40 m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  (* 组合：(A) 右乘 4·40^m 后与 (B) 串接 *)
  assert (HC : (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                * zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z)
               * (4 * q_pow 40 m)
            <= q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))).
  { apply (Qle_trans _
             (q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)
              * (4 * q_pow 40 m))).
    - apply (Qmult_le_compat_r
               (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                * zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z)
               (q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))
               (4 * q_pow 40 m) HA HK400).
    - assert (Hcomm : q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m)
                      * (4 * q_pow 40 m)
                   == 4 * q_pow 40 m * q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m))
        by ring.
      rewrite Hcomm. exact Hdec0. }
  (* 按 T = 1−xyz 的符号分情况 *)
  destruct (Qlt_le_dec 0 (1 - x * y * z)) as [Hpos | Hneg].
  - (* 主情形：T > 0，正因子消去后乘权重 *)
    pose proof (QltT_to_Qlt _ _
      (zb3_dc_qp_pos (Datatypes.S (Datatypes.S m)) (1 - x * y * z) Hpos)) as HPpos.
    assert (Hrg : (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))
                   * zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z)
                  * (4 * q_pow 40 m)
               == (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z * (4 * q_pow 40 m))
                  * q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))) by ring.
    rewrite Hrg in HC.
    pose proof (zb3_dc_cancel_one
                  (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z * (4 * q_pow 40 m))
                  (q_pow (1 - x * y * z) (Datatypes.S (Datatypes.S m))) HPpos HC) as H1.
    pose proof (QleT'_to_Qle _ _ (zb3_dc_weight_ge0 m)) as HW0.
    pose proof (Qmult_le_compat_r
                  (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z * (4 * q_pow 40 m))
                  1 ((1#4) * q_pow (1#40) m) H1 HW0) as Hmult.
    assert (Hunit : (4 * q_pow 40 m) * ((1#4) * q_pow (1#40) m) == 1).
    { assert (Hpm : q_pow 40 m * q_pow (1#40) m == 1).
      { rewrite <- (zb2_q_pow_mul 40 (1#40) m).
        assert (H4010 : 40 * (1#40) == 1) by ring.
        rewrite H4010. apply zb3_dc_qp_one. }
      assert (Hre : (4 * q_pow 40 m) * ((1#4) * q_pow (1#40) m)
                 == (4 * (1#4)) * (q_pow 40 m * q_pow (1#40) m)) by ring.
      rewrite Hre, Hpm. ring. }
    assert (Hlhs : (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z * (4 * q_pow 40 m))
                   * ((1#4) * q_pow (1#40) m)
                == zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z).
    { assert (Hre2 : (zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z * (4 * q_pow 40 m))
                     * ((1#4) * q_pow (1#40) m)
                  == zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z
                     * ((4 * q_pow 40 m) * ((1#4) * q_pow (1#40) m))) by ring.
      rewrite Hre2, Hunit. ring. }
    assert (Hrhs : 1 * ((1#4) * q_pow (1#40) m) == (1#4) * q_pow (1#40) m) by ring.
    rewrite Hrhs in Hmult. rewrite Hlhs in Hmult.
    apply Qle_to_QleT'. exact Hmult.
  - (* 边界情形：T ≤ 0 与 xyz ≤ 1 联立得 T = 0，进而 x = y = z = 1、F = 0 *)
    assert (HT0 : 0 <= 1 - x * y * z) by (apply (zb2_le_sub (x * y * z) 1); exact Hxyz1).
    assert (HTeq : 1 - x * y * z == 0) by (apply Qle_antisym; [ exact Hneg | exact HT0 ]).
    assert (Hxyzeq : x * y * z == 1).
    { assert (Ha : 1 - (1 - x * y * z) == 1 - 0) by (rewrite HTeq; ring).
      assert (Hb : 1 - (1 - x * y * z) == x * y * z) by ring.
      assert (Hc : 1 - 0 == 1) by ring.
      rewrite Hb, Hc in Ha. exact Ha. }
    assert (Hyz1 : y * z <= 1) by (apply (zb2_xy_le_1 y z); assumption).
    assert (Hxz1 : x * z <= 1) by (apply (zb2_xy_le_1 x z); assumption).
    assert (Hle1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
    assert (Hlex : x * y * z <= x)
      by (apply (zb3_dc_mul_le_shift x y z Hyz1 Hx1)).
    assert (Hley0 : y * x * z <= y)
      by (apply (zb3_dc_mul_le_shift y x z Hxz1 Hy1)).
    assert (Hley : x * y * z <= y).
    { assert (E : x * y * z == y * x * z) by ring.
      rewrite E. exact Hley0. }
    assert (Hlez0 : z * x * y <= z)
      by (apply (zb3_dc_mul_le_shift z x y Hle1 Hz1)).
    assert (Hlez : x * y * z <= z).
    { assert (E : x * y * z == z * x * y) by ring.
      rewrite E. exact Hlez0. }
    assert (Hx1e : x == 1).
    { apply Qle_antisym.
      - exact Hx2.
      - apply (Qle_trans 1 (x * y * z) x).
        + apply (zb2_le_eq 1 (x * y * z)). symmetry. exact Hxyzeq.
        + exact Hlex. }
    assert (Hy1e : y == 1).
    { apply Qle_antisym.
      - exact Hy2.
      - apply (Qle_trans 1 (x * y * z) y).
        + apply (zb2_le_eq 1 (x * y * z)). symmetry. exact Hxyzeq.
        + exact Hley. }
    assert (Hz1e : z == 1).
    { apply Qle_antisym.
      - exact Hz2.
      - apply (Qle_trans 1 (x * y * z) z).
        + apply (zb2_le_eq 1 (x * y * z)). symmetry. exact Hxyzeq.
        + exact Hlez. }
    assert (HN0e : x * (1 - x) * y * (1 - y) * z * (1 - z) == 0)
      by (rewrite Hx1e, Hy1e, Hz1e; ring).
    assert (Hq0 : q_pow (x * (1 - x) * y * (1 - y) * z * (1 - z)) (Datatypes.S m) == 0)
      by (rewrite HN0e; cbn [q_pow]; apply Qmult_0_l).
    assert (Hc0 : zb3_beval_l (zb3_segl (Datatypes.S m) M) x y z == 0)
      by (rewrite Hseg, Hq0; apply Qmult_0_l).
    apply Qle_to_QleT'. rewrite Hc0.
    apply QleT'_to_Qle. apply zb3_dc_weight_ge0.
Qed.

(* 数值基准：m = M = 1、x = y = z = 1/2 档的截断被积式值 = 5/256
   （= (1/4)³·(1 + 2·(1/8))，贯通截断展开与三次迭代积分承载机的引用链） *)
Lemma zb3_dc_anchor1 : zb3_beval_l (zb3_segl 1 1) (1#2) (1#2) (1#2) == (5#256).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* §C 竞争面：27^(m+1)·(1/4)(1/40)^m = (27/4)·(27/40)^m < 1（m ≥ 5）      *)
(* ===================================================================== *)

(* 竞争恒等式：27^(m+1)·(1/4)·(1/40)^m = (27/4)·(27/40)^m *)
Lemma zb3_dc_comp_id : forall m : nat,
  q_pow 27 (Datatypes.S m) * ((1#4) * q_pow (1#40) m) == (27#4) * q_pow (27#40) m.
Proof.
  intro m.
  assert (Hpm : q_pow 27 m * q_pow (1#40) m == q_pow (27#40) m).
  { rewrite <- (zb2_q_pow_mul 27 (1#40) m).
    assert (H2740 : 27 * (1#40) == (27#40)) by ring.
    rewrite H2740. reflexivity. }
  assert (Hre : q_pow 27 (Datatypes.S m) * ((1#4) * q_pow (1#40) m)
             == (27 * (1#4)) * (q_pow 27 m * q_pow (1#40) m)).
  { rewrite (q_pow_succ 27 m). ring. }
  rewrite Hre, Hpm. ring.
Qed.

(* 竞争基档：(27/4)·(27/40)^5 = 27^6/(4·40^5) = 387420489/409600000 < 1
   （全为字面有理数，Qlt_bool 可计算判定） *)
Lemma zb3_dc_comp_base : QltT ((27#4) * q_pow (27#40) 5) 1.
Proof. exact (id_refl (A:=bool) (x:=Qlt_bool ((27#4) * q_pow (27#40) 5) 1)). Qed.

(* 竞争步进：(27/4)·(27/40)^(m+1) ≤ (27/4)·(27/40)^m *)
Lemma zb3_dc_comp_step : forall m : nat,
  QleT' ((27#4) * q_pow (27#40) (Datatypes.S m)) ((27#4) * q_pow (27#40) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (27#4) * q_pow (27#40) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  assert (H2740 : (27#40) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (27#4) * q_pow (27#40) (Datatypes.S m)
             == (27#40) * ((27#4) * q_pow (27#40) m))
    by (rewrite (q_pow_succ (27#40) m); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (27#40) 1 ((27#4) * q_pow (27#40) m) H2740 Hge0) as Hle.
  assert (Hr2 : 1 * ((27#4) * q_pow (27#40) m) == (27#4) * q_pow (27#40) m) by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* 竞争平移：(27/4)·(27/40)^(m+d) ≤ (27/4)·(27/40)^m *)
Lemma zb3_dc_comp_drop : forall (d m : nat),
  QleT' ((27#4) * q_pow (27#40) (m + d)) ((27#4) * q_pow (27#40) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat) by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((27#4) * q_pow (27#40) (Datatypes.S (m + d)))
                       ((27#4) * q_pow (27#40) (m + d))
                       ((27#4) * q_pow (27#40) m)).
    + apply zb3_dc_comp_step.
    + apply IH.
Qed.

(* 竞争判定：m ≥ 5 ⟹ (27/4)·(27/40)^m < 1 *)
Lemma zb3_dc_comp_verdict : forall m : nat, (5 <= m)%nat -> QltT ((27#4) * q_pow (27#40) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 5 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((27#4) * q_pow (27#40) (Datatypes.S m))
                           ((27#4) * q_pow (27#40) m) 1).
      * apply zb3_dc_comp_step.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 5)%nat) by lia.
      rewrite Heq. exact zb3_dc_comp_base.
Qed.

(* ===================================================================== *)
(* §D 立方整性分离面：d³·I_{m+1} < 1（显式前提形式）                       *)
(* ===================================================================== *)

(* 立方权：0 ≤ d ≤ 3^{m+1} ⟹ d³ ≤ 27^{m+1} *)
Lemma zb3_dc_weight_cub : forall (m : nat) (d : Q),
  QleT' 0 d -> QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (d * d * d) (q_pow 27 (Datatypes.S m)).
Proof.
  intros m d Hd0 Hd.
  pose proof (QleT'_to_Qle _ _ Hd0) as Hd0q.
  pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
  assert (H30 : 0 <= q_pow 3 (Datatypes.S m))
    by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  (* 平方段：d² ≤ 9^{m+1} *)
  assert (H1 : d * d <= q_pow 3 (Datatypes.S m) * d)
    by (apply (Qmult_le_compat_r d (q_pow 3 (Datatypes.S m)) d); assumption).
  assert (H2 : q_pow 3 (Datatypes.S m) * d <= q_pow 3 (Datatypes.S m) * q_pow 3 (Datatypes.S m)).
  { assert (H2' : d * q_pow 3 (Datatypes.S m) <= q_pow 3 (Datatypes.S m) * q_pow 3 (Datatypes.S m))
      by (apply (Qmult_le_compat_r d (q_pow 3 (Datatypes.S m)) (q_pow 3 (Datatypes.S m))); assumption).
    assert (Hc : q_pow 3 (Datatypes.S m) * d == d * q_pow 3 (Datatypes.S m)) by ring.
    rewrite Hc. exact H2'. }
  assert (Hsq9 : q_pow 3 (Datatypes.S m) * q_pow 3 (Datatypes.S m) == q_pow 9 (Datatypes.S m)).
  { rewrite <- (zb2_q_pow_mul 3 3 (Datatypes.S m)).
    assert (H33 : 3 * 3 == 9) by ring.
    rewrite H33. reflexivity. }
  rewrite Hsq9 in H2.
  assert (Hfin2 : d * d <= q_pow 9 (Datatypes.S m)).
  { apply (Qle_trans _ (q_pow 3 (Datatypes.S m) * d)); [ exact H1 | exact H2 ]. }
  (* 立方段：d³ ≤ 27^{m+1} *)
  assert (H3 : (d * d) * d <= q_pow 9 (Datatypes.S m) * d).
  { apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m)) d Hfin2 Hd0q). }
  assert (H90 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (H4 : q_pow 9 (Datatypes.S m) * d <= q_pow 9 (Datatypes.S m) * q_pow 3 (Datatypes.S m)).
  { pose proof (Qmult_le_compat_r d (q_pow 3 (Datatypes.S m))
                  (q_pow 9 (Datatypes.S m)) Hdq H90) as Ht.
    assert (E1 : q_pow 9 (Datatypes.S m) * d == d * q_pow 9 (Datatypes.S m)) by ring.
    assert (E2 : q_pow 9 (Datatypes.S m) * q_pow 3 (Datatypes.S m)
              == q_pow 3 (Datatypes.S m) * q_pow 9 (Datatypes.S m)) by ring.
    rewrite E1, E2. exact Ht. }
  assert (Hsq27 : q_pow 9 (Datatypes.S m) * q_pow 3 (Datatypes.S m) == q_pow 27 (Datatypes.S m)).
  { rewrite <- (zb2_q_pow_mul 9 3 (Datatypes.S m)).
    assert (H93 : 9 * 3 == 27) by ring.
    rewrite H93. reflexivity. }
  apply Qle_to_QleT'.
  apply (Qle_trans ((d * d) * d) (q_pow 9 (Datatypes.S m) * d)).
  - exact H3.
  - rewrite <- Hsq27. exact H4.
Qed.

(* 分离主定理（显式前提形式）：设 d 满足 0 ≤ d ≤ 3^{m+1}（d 的具体上界
   引理由 Hanson 链按同型实例化），积分值 I_{m+1} 满足
   I ≤ (1/4)(1/40)^m（尾界机交接位），则当 m ≥ 5 时 d³·I_{m+1} < 1。 *)
Theorem zb3_dc_sep3_small : forall (m M : nat) (d : Q),
  (5 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (zb3_Isum (Datatypes.S m) M) ((1#4) * q_pow (1#40) m) ->
  QltT (d * d * d * zb3_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d Hm Hd0 Hd HI.
  pose proof (zb3_dc_weight_cub m d Hd0 Hd) as Hsq.
  pose proof (zb3_Isum_pos (Datatypes.S m) M) as HposT.
  pose proof (QleT'_to_Qle _ _ (qltT_leT' _ _ HposT)) as HposI.
  pose proof (QleT'_to_Qle _ _ HI) as HIq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  assert (H27 : 0 <= q_pow 27 (Datatypes.S m)) by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * d * zb3_Isum (Datatypes.S m) M
                <= q_pow 27 (Datatypes.S m) * zb3_Isum (Datatypes.S m) M)
    by (apply (Qmult_le_compat_r (d * d * d) (q_pow 27 (Datatypes.S m))
                                 (zb3_Isum (Datatypes.S m) M) Hsqq HposI)).
  assert (Hstep2 : q_pow 27 (Datatypes.S m) * zb3_Isum (Datatypes.S m) M
                <= q_pow 27 (Datatypes.S m) * ((1#4) * q_pow (1#40) m)).
  { assert (H2' : zb3_Isum (Datatypes.S m) M * q_pow 27 (Datatypes.S m)
               <= ((1#4) * q_pow (1#40) m) * q_pow 27 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (zb3_Isum (Datatypes.S m) M)
                                   ((1#4) * q_pow (1#40) m)
                                   (q_pow 27 (Datatypes.S m)) HIq H27)).
    assert (Hc1 : q_pow 27 (Datatypes.S m) * zb3_Isum (Datatypes.S m) M
               == zb3_Isum (Datatypes.S m) M * q_pow 27 (Datatypes.S m)) by ring.
    assert (Hc2 : ((1#4) * q_pow (1#40) m) * q_pow 27 (Datatypes.S m)
               == q_pow 27 (Datatypes.S m) * ((1#4) * q_pow (1#40) m)) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * d * zb3_Isum (Datatypes.S m) M <= (27#4) * q_pow (27#40) m).
  { apply (Qle_trans _ (q_pow 27 (Datatypes.S m) * ((1#4) * q_pow (1#40) m))).
    - apply (Qle_trans _ (q_pow 27 (Datatypes.S m) * zb3_Isum (Datatypes.S m) M)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (zb2_le_eq _ _ (zb3_dc_comp_id m)). }
  pose proof (QltT_to_Qlt _ _ (zb3_dc_comp_verdict m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* 数值基准：竞争基档数值锚（27^6 = 387420489 < 4·40^5 = 409600000） *)
Lemma zb3_dc_base_anchor : QltT ((27#4) * (14348907#102400000)) 1.
Proof. exact (id_refl (A:=bool) (x:=Qlt_bool ((27#4) * (14348907#102400000)) 1)). Qed.

(* ============================================================ *)
(* §F 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions zb3_dc_qp_pos.
Print Assumptions zb3_dc_qp_one.
Print Assumptions zb3_dc_cancel_one.
Print Assumptions zb3_dc_weight_ge0.
Print Assumptions zb3_dc_pow_cv.
Print Assumptions zb3_dc_ps_ge0.
Print Assumptions zb3_dc_carrier_ge0.
Print Assumptions zb3_dc_carrier_decay.
Print Assumptions zb3_dc_anchor1.
Print Assumptions zb3_dc_comp_id.
Print Assumptions zb3_dc_comp_base.
Print Assumptions zb3_dc_comp_step.
Print Assumptions zb3_dc_comp_drop.
Print Assumptions zb3_dc_comp_verdict.
Print Assumptions zb3_dc_weight_cub.
Print Assumptions zb3_dc_sep3_small.
Print Assumptions zb3_dc_base_anchor.
