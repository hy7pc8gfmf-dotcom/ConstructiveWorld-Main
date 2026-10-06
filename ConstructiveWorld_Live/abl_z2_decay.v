(* ===================================================================== *)
(* 模块：abl_z2_decay                                                    *)
(* 使命：Beukers 1979 ζ(2) 无理性证明的衰减估计面。在方形 [0,1]² 上建立   *)
(*   截断被积式族 F_{n,M}(x,y) 的双侧逐点控制：非负性，以及锐权上界        *)
(*   F_{m+1,M}(x,y) ≤ (1/4)·(1/10)^m（上确界范数以逐点 ∀ 形式作构造性     *)
(*   渲染）。另给出终装配所需的增长率竞争判定                             *)
(*   9^(m+1)·(1/4)(1/10)^m = (9/4)(9/10)^m < 1（m ≥ 8），以及整性分离面    *)
(*   d²·I_{m+1} < 1：其中 d 的具体上界与逐点到积分的上界过渡均以显式       *)
(*   前提给出，相应引理到位后按同型实例化。                               *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp；                      *)
(*   abl_z2_pointwise abl_z2_truncfam abl_z2_itg_carrier；                *)
(*   Stdlib：QArith ZArith Arith Lia Setoid。                             *)
(* 对标：Beukers, A note on the irrationality of ζ(2) and ζ(3),          *)
(*   Bull. London Math. Soc. 11 (1979)，被积式逐点估计与 lcm² 增长率      *)
(*   竞争步（Hanson 1972：lcm(1,…,n) ≤ 3^n）。                            *)
(* 构造性：零假设声明——全件不引入任何公理或承认式语句；主语句结论面取     *)
(*   Set 层见证型 QleT'／QltT；情形分析经 Qlt_le_dec 与 le_lt_dec 的       *)
(*   可判定分情况完成，零经典逻辑。                                       *)
(* 编译配方：rocq c -native-compiler no                                  *)
(*   -Q vo_local_world_unified_0930 "" -Q . "" abl_z2_decay.v             *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_pointwise abl_z2_truncfam abl_z2_itg_carrier.

Open Scope Q_scope.

(* ===================================================================== *)
(* §0 基础档：幂的正性、单位幂与正因子消去                               *)
(* ===================================================================== *)

(* 幂的非负性：0 ≤ z ⟹ 0 ≤ z^k（S03 之 q_pow_nonneg 的 Set 层见证转换） *)
Lemma zb2_dc_qp_ge0 : forall (k : nat) (z : Q), 0 <= z -> QleT' 0 (q_pow z k).
Proof.
  intros k z Hz. apply Qle_to_QleT'. apply q_pow_nonneg. exact Hz.
Qed.

(* 幂的严格正性：0 < z ⟹ 0 < z^k（对 k 归纳；步档为两个正因子之积） *)
Lemma zb2_dc_qp_pos : forall (k : nat) (z : Q), 0 < z -> QltT 0 (q_pow z k).
Proof.
  intros k z Hz. induction k as [| k IH].
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - apply Qlt_to_QltT. cbn [q_pow].
    apply (Qmult_lt_0_compat z (q_pow z k) Hz (QltT_to_Qlt _ _ IH)).
Qed.

(* 单位幂：1^k == 1 *)
Lemma zb2_dc_qp_one : forall k : nat, q_pow 1 k == 1.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qmult_1_l. exact IH.
Qed.

(* 正因子消去：0 < p 且 a·p ≤ p ⟹ a ≤ 1
   （若 1 < a，两侧乘 p 保严格序，与前提矛盾） *)
Lemma zb2_dc_cancel_one : forall a p : Q, 0 < p -> a * p <= p -> a <= 1.
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

(* ===================================================================== *)
(* §A 正性面：部分和与截断被积式族的非负性                               *)
(* ===================================================================== *)

(* 部分和非负性：0 ≤ t ⟹ 0 ≤ Σ_{m≤M} C(n+m,n)·t^m
   （对 M 归纳：零档为 1；步档为既有非负部分和与非负系数幂之积的和） *)
Lemma zb2_dc_ps_ge0 : forall (n M : nat) (t : Q), 0 <= t -> QleT' 0 (zb2_ps n M t).
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

(* 截断被积式族在方形上的非负性（逐点）：
   F = (x(1-x))^n (y(1-y))^n · Σ_{m≤M} C(n+m,n)(xy)^m，诸因子皆非负 *)
Lemma zb2_dc_carrier_ge0 : forall (n M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' 0 (zb2_beval_l (zb2_segl n M) x y).
Proof.
  intros n M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (HA : 0 <= q_pow (x * (1 - x)) n)
    by (apply q_pow_nonneg; apply (zb2_mult2_ge0 x (1 - x)); assumption).
  assert (HB : 0 <= q_pow (y * (1 - y)) n)
    by (apply q_pow_nonneg; apply (zb2_mult2_ge0 y (1 - y)); assumption).
  assert (HC : 0 <= zb2_ps n M (x * y)).
  { pose proof (zb2_dc_ps_ge0 n M (x * y) (Qmult_le_0_compat x y Hx1 Hy1)) as HCt.
    exact (QleT'_to_Qle _ _ HCt). }
  pose proof (zb2_beval_segl n M x y) as Hseg.
  apply Qle_to_QleT'. rewrite Hseg.
  assert (HAB : 0 <= q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
    by (apply Qmult_le_0_compat; assumption).
  apply (Qmult_le_0_compat (q_pow (x * (1 - x)) n * q_pow (y * (1 - y)) n)
                           (zb2_ps n M (x * y)) HAB HC).
Qed.

(* 权重非负：0 ≤ (1/4)·(1/10)^m *)
Lemma zb2_dc_weight_ge0 : forall m : nat, QleT' 0 ((1#4) * q_pow (1#10) m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply q_pow_nonneg. unfold Qle. simpl. lia.
Qed.

(* ===================================================================== *)
(* §B 锐权面：截断被积式族的逐点上界 (1/4)(1/10)^m                        *)
(* ===================================================================== *)

(* 主定理（锐权面）：对指数 n = m+1 档与一切 x y ∈ [0,1]²，
   截断被积式 F_{m+1,M}(x,y) ≤ (1/4)·(1/10)^m。
   证明链：部分和上界引理（(1-t)^(m+2)·Σ ≤ 1）与幂乘合并给出
   T^(m+2)·F ≤ N^(m+1)（T := 1−xy，N := x(1−x)y(1−y)）；既有逐点衰减
   4·10^m·N^(m+1) ≤ T^(m+2)；两式右乘 4·10^m 相乘后按 T 的符号分情况：
   T > 0 时以正因子消去律得 4·10^m·F ≤ 1，再乘权重 (1/4)(1/10)^m 收出
   F ≤ (1/4)(1/10)^m；T = 0 时联立 xy ≤ 1 得 x = y = 1，F = 0。 *)
Theorem zb2_dc_carrier_decay : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y) ((1#4) * q_pow (1#10) m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x * y) (conj Hxy0 Hxy1)) as HpsT.
  pose proof (QleT'_to_Qle _ _ HpsT) as Hps.
  pose proof (zb2_beval_segl (Datatypes.S m) M x y) as Hseg.
  assert (Hmerge : q_pow (x * (1 - x)) (Datatypes.S m) * q_pow (y * (1 - y)) (Datatypes.S m)
                == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { rewrite <- (zb2_q_pow_mul (x * (1 - x)) (y * (1 - y)) (Datatypes.S m)).
    apply q_pow_wd. ring. }
  rewrite Hmerge in Hseg.
  assert (HN0 : 0 <= x * (1 - x) * y * (1 - y))
    by (apply (zb2_mult4_ge0 x (1 - x) y (1 - y)); assumption).
  assert (HK0 : 0 <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
    by (apply q_pow_nonneg; exact HN0).
  (* (A)：T^(m+2)·F ≤ N^(m+1) *)
  assert (HA : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
            <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { assert (Hrw : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
               == (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_ps (Datatypes.S m) M (x * y))
                  * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
      by (rewrite Hseg; ring).
    rewrite Hrw.
    apply (Qle_trans _ (1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_ps (Datatypes.S m) M (x * y))
                               1 (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) Hps HK0).
    - assert (H1K : 1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                 == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) by ring.
      rewrite H1K. apply Qle_refl. }
  (* (B)：4·10^m·N^(m+1) ≤ T^(m+2)（既有逐点衰减，幂记号统一为 q_pow） *)
  assert (Hcv : forall (t : Q) (k : nat), zb2_pow t k == q_pow t k).
  { intros t k. induction k as [| k IH].
    - reflexivity.
    - cbn [zb2_pow q_pow]. rewrite IH. ring. }
  pose proof (zb2_pointwise_decay m x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as HdecT.
  pose proof (zb2_qle_to_Qle _ _ HdecT) as Hdec0.
  rewrite (Hcv 10 m) in Hdec0.
  rewrite (Hcv (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) in Hdec0.
  rewrite (Hcv (1 - x * y) (Datatypes.S (Datatypes.S m))) in Hdec0.
  assert (HK100 : 0 <= 4 * q_pow 10 m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  (* 组合：(A) 右乘 4·10^m 后与 (B) 串接 *)
  assert (HC : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
               * (4 * q_pow 10 m) <= q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))).
  { apply (Qle_trans _ (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) * (4 * q_pow 10 m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                               (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               (4 * q_pow 10 m) HA HK100).
    - assert (Hcomm : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) * (4 * q_pow 10 m)
                   == 4 * q_pow 10 m * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
        by ring.
      rewrite Hcomm. exact Hdec0. }
  (* 按 T = 1−xy 的符号分情况 *)
  destruct (Qlt_le_dec 0 (1 - x * y)) as [Hpos | Hneg].
  - (* 主情形：T > 0，正因子消去后乘权重 *)
    pose proof (QltT_to_Qlt _ _ (zb2_dc_qp_pos (Datatypes.S (Datatypes.S m)) (1 - x * y) Hpos)) as HPpos.
    assert (Hrg : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m)) * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                  * (4 * q_pow 10 m)
               == (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 10 m))
                  * q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) by ring.
    rewrite Hrg in HC.
    pose proof (zb2_dc_cancel_one (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 10 m))
                                  (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) HPpos HC) as H1.
    pose proof (QleT'_to_Qle _ _ (zb2_dc_weight_ge0 m)) as HW0.
    pose proof (Qmult_le_compat_r (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 10 m))
                                  1 ((1#4) * q_pow (1#10) m) H1 HW0) as Hmult.
    assert (Hunit : (4 * q_pow 10 m) * ((1#4) * q_pow (1#10) m) == 1).
    { assert (Hpm : q_pow 10 m * q_pow (1#10) m == 1).
      { rewrite <- (zb2_q_pow_mul 10 (1#10) m).
        assert (H1010 : 10 * (1#10) == 1) by ring.
        rewrite H1010. apply zb2_dc_qp_one. }
      assert (Hre : (4 * q_pow 10 m) * ((1#4) * q_pow (1#10) m)
                 == (4 * (1#4)) * (q_pow 10 m * q_pow (1#10) m)) by ring.
      rewrite Hre, Hpm. ring. }
    assert (Hlhs : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 10 m))
                   * ((1#4) * q_pow (1#10) m)
                == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
    { assert (Hre2 : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y * (4 * q_pow 10 m))
                     * ((1#4) * q_pow (1#10) m)
                  == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * ((4 * q_pow 10 m) * ((1#4) * q_pow (1#10) m))) by ring.
      rewrite Hre2, Hunit. ring. }
    assert (Hrhs : 1 * ((1#4) * q_pow (1#10) m) == (1#4) * q_pow (1#10) m) by ring.
    rewrite Hrhs in Hmult. rewrite Hlhs in Hmult.
    apply Qle_to_QleT'. exact Hmult.
  - (* 边界情形：T ≤ 0 与 xy ≤ 1 联立得 T = 0，进而 x = y = 1、F = 0 *)
    assert (HT0 : 0 <= 1 - x * y) by (apply (zb2_le_sub (x * y) 1); exact Hxy1).
    assert (HTeq : 1 - x * y == 0) by (apply Qle_antisym; [ exact Hneg | exact HT0 ]).
    assert (Hxyeq : x * y == 1).
    { assert (Ha : 1 - (1 - x * y) == 1 - 0) by (rewrite HTeq; ring).
      assert (Hb : 1 - (1 - x * y) == x * y) by ring.
      assert (Hc : 1 - 0 == 1) by ring.
      rewrite Hb, Hc in Ha. exact Ha. }
    assert (Hle1 : x * y <= x).
    { pose proof (Qmult_le_compat_r y 1 x Hy2 Hx1) as Hq.
      assert (Hd1 : y * x == x * y) by ring. assert (Hd2 : 1 * x == x) by ring.
      rewrite Hd1, Hd2 in Hq. exact Hq. }
    assert (Hle2 : x * y <= y).
    { pose proof (Qmult_le_compat_r x 1 y Hx2 Hy1) as Hq.
      assert (Hd2 : 1 * y == y) by ring. rewrite Hd2 in Hq. exact Hq. }
    assert (Hx1e : x == 1).
    { apply Qle_antisym.
      - exact Hx2.
      - apply (Qle_trans 1 (x * y) x).
        + apply (zb2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle1. }
    assert (Hy1e : y == 1).
    { apply Qle_antisym.
      - exact Hy2.
      - apply (Qle_trans 1 (x * y) y).
        + apply (zb2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle2. }
    assert (HN0e : x * (1 - x) * y * (1 - y) == 0) by (rewrite Hx1e, Hy1e; ring).
    assert (Hq0 : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) == 0)
      by (rewrite HN0e; cbn [q_pow]; apply Qmult_0_l).
    assert (Hc0 : zb2_beval_l (zb2_segl (Datatypes.S m) M) x y == 0)
      by (rewrite Hseg, Hq0; apply Qmult_0_l).
    apply Qle_to_QleT'. rewrite Hc0.
    apply QleT'_to_Qle. apply zb2_dc_weight_ge0.
Qed.

(* 数值基准：m = M = 1、x = y = 1/2 档的截断被积式值 = 3/32
   （= (1/4)(1/4)·(1 + 2·(1/4))，同时贯通截断展开与迭代积分承载机的引用链） *)
Lemma zb2_dc_anchor1 : zb2_beval_l (zb2_segl 1 1) (1#2) (1#2) == (3#32).
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* §C 竞争面：9^(m+1)·(1/4)(1/10)^m = (9/4)(9/10)^m < 1（m ≥ 8）          *)
(* ===================================================================== *)

(* 竞争恒等式：9^(m+1)·(1/4)·(1/10)^m = (9/4)·(9/10)^m *)
Lemma zb2_dc_comp_id : forall m : nat,
  q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#10) m) == (9#4) * q_pow (9#10) m.
Proof.
  intro m.
  assert (Hpm : q_pow 9 m * q_pow (1#10) m == q_pow (9#10) m).
  { rewrite <- (zb2_q_pow_mul 9 (1#10) m).
    assert (H910 : 9 * (1#10) == (9#10)) by ring.
    rewrite H910. reflexivity. }
  assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#10) m)
             == (9 * (1#4)) * (q_pow 9 m * q_pow (1#10) m)).
  { rewrite (q_pow_succ 9 m). ring. }
  rewrite Hre, Hpm. ring.
Qed.

(* 竞争基档：(9/4)·(9/10)^8 = 9^9/(4·10^8) = 387420489/400000000 < 1
   （全为字面有理数，Qlt_bool 可计算判定） *)
Lemma zb2_dc_comp_base : QltT ((9#4) * q_pow (9#10) 8) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (9#10) 8) 1)).
Qed.

(* 竞争步进：(9/4)·(9/10)^(m+1) ≤ (9/4)·(9/10)^m（两侧乘 (9/10) ≤ 1） *)
Lemma zb2_dc_comp_step : forall m : nat,
  QleT' ((9#4) * q_pow (9#10) (Datatypes.S m)) ((9#4) * q_pow (9#10) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (9#10) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  assert (H91 : (9#10) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (9#10) (Datatypes.S m)
             == (9#10) * ((9#4) * q_pow (9#10) m))
    by (rewrite (q_pow_succ (9#10) m); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (9#10) 1 ((9#4) * q_pow (9#10) m) H91 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (9#10) m) == (9#4) * q_pow (9#10) m) by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* 竞争平移：(9/4)·(9/10)^(m+d) ≤ (9/4)·(9/10)^m（对平移量 d 归纳） *)
Lemma zb2_dc_comp_drop : forall (d m : nat),
  QleT' ((9#4) * q_pow (9#10) (m + d)) ((9#4) * q_pow (9#10) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat) by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (9#10) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (9#10) (m + d))
                       ((9#4) * q_pow (9#10) m)).
    + apply zb2_dc_comp_step.
    + apply IH.
Qed.

(* 竞争判定：m ≥ 8 ⟹ (9/4)·(9/10)^m < 1
   （le_lt_dec 可判定分情况：m ≥ 8 时经步进回落至基档；
     m < 8 时与前提联立得 m+1 = 8，直接落基档） *)
Lemma zb2_dc_comp_verdict : forall m : nat, (8 <= m)%nat -> QltT ((9#4) * q_pow (9#10) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 8 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (9#10) (Datatypes.S m))
                           ((9#4) * q_pow (9#10) m) 1).
      * apply zb2_dc_comp_step.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 8)%nat) by lia.
      rewrite Heq. exact zb2_dc_comp_base.
Qed.

(* ===================================================================== *)
(* §D 整性分离面：d²·I_{m+1} < 1（显式前提形式）                          *)
(* ===================================================================== *)

(* 平方权：0 ≤ d ≤ 3^n ⟹ d² ≤ 9^n（= 3^n·3^n，幂乘合并） *)
Lemma zb2_dc_weight_sq : forall (n : nat) (d : Q),
  QleT' 0 d -> QleT' d (q_pow 3 n) -> QleT' (d * d) (q_pow 9 n).
Proof.
  intros n d Hd0 Hd.
  pose proof (QleT'_to_Qle _ _ Hd0) as Hd0q.
  pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
  assert (H30 : 0 <= q_pow 3 n) by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (H1 : d * d <= q_pow 3 n * d)
    by (apply (Qmult_le_compat_r d (q_pow 3 n) d); assumption).
  assert (H2 : q_pow 3 n * d <= q_pow 3 n * q_pow 3 n).
  { assert (H2' : d * q_pow 3 n <= q_pow 3 n * q_pow 3 n)
      by (apply (Qmult_le_compat_r d (q_pow 3 n) (q_pow 3 n)); assumption).
    assert (Hc : q_pow 3 n * d == d * q_pow 3 n) by ring.
    rewrite Hc. exact H2'. }
  assert (Hfin : d * d <= q_pow 3 n * q_pow 3 n)
    by (apply (Qle_trans _ (q_pow 3 n * d)); assumption).
  assert (Hsq : q_pow 3 n * q_pow 3 n == q_pow 9 n).
  { rewrite <- (zb2_q_pow_mul 3 3 n).
    assert (H33 : 3 * 3 == 9) by ring.
    rewrite H33. reflexivity. }
  rewrite Hsq in Hfin. apply Qle_to_QleT'. exact Hfin.
Qed.

(* 分离主定理（显式前提形式）：设 d 满足 0 ≤ d ≤ 3^(m+1)（d 的具体上界
   引理到位后按同型实例化），积分值 I_{m+1} 满足 I ≤ (1/4)(1/10)^m（逐点
   控制到积分上界的过渡到位后按同型实例化），则当 m ≥ 8 时
   d²·I_{m+1} < 1。积分值的非负性取自既有 Isum 严格正性引理。 *)
Theorem zb2_dc_sep_small : forall (m M : nat) (d : Q),
  (8 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (zb2_Isum (Datatypes.S m) M) ((1#4) * q_pow (1#10) m) ->
  QltT (d * d * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d Hm Hd0 Hd HI.
  pose proof (zb2_dc_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (zb2_Isum_pos (Datatypes.S m) M) as HposT.
  pose proof (QleT'_to_Qle _ _ (qltT_leT' _ _ HposT)) as HposI.
  pose proof (QleT'_to_Qle _ _ HI) as HIq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m)) by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * zb2_Isum (Datatypes.S m) M <= q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m)) (zb2_Isum (Datatypes.S m) M)
                                 Hsqq HposI)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#10) m)).
  { assert (H2' : zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)
               <= ((1#4) * q_pow (1#10) m) * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (zb2_Isum (Datatypes.S m) M) ((1#4) * q_pow (1#10) m)
                                   (q_pow 9 (Datatypes.S m)) HIq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
               == zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : ((1#4) * q_pow (1#10) m) * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#10) m)) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * zb2_Isum (Datatypes.S m) M <= (9#4) * q_pow (9#10) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#10) m))).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (zb2_le_eq _ _ (zb2_dc_comp_id m)). }
  pose proof (QltT_to_Qlt _ _ (zb2_dc_comp_verdict m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

Print Assumptions zb2_dc_qp_ge0.
Print Assumptions zb2_dc_qp_pos.
Print Assumptions zb2_dc_qp_one.
Print Assumptions zb2_dc_cancel_one.
Print Assumptions zb2_dc_ps_ge0.
Print Assumptions zb2_dc_carrier_ge0.
Print Assumptions zb2_dc_weight_ge0.
Print Assumptions zb2_dc_carrier_decay.
Print Assumptions zb2_dc_anchor1.
Print Assumptions zb2_dc_comp_id.
Print Assumptions zb2_dc_comp_base.
Print Assumptions zb2_dc_comp_step.
Print Assumptions zb2_dc_comp_drop.
Print Assumptions zb2_dc_comp_verdict.
Print Assumptions zb2_dc_weight_sq.
Print Assumptions zb2_dc_sep_small.
