(* ===================================================================== *)
(*  gcl_famsym.v —— 对称化截断族 Fam 槽供件                                 *)
(*  模块名：gcl_famsym。                                                   *)
(*  使命：承组论系数层遗产（gcl_coefficient 的 gcl_sep_generic 具名插槽），   *)
(*        铸对称化截断族——V4 轨道平均的 T-分母截断族实例序列，并以           *)
(*        机内证明消去插槽两前提（非负＋族界 ≤ (1/4)(1/12)^m），达成         *)
(*        gcl_sep_generic 实例化零前提收束（gcl_famseq_sep）。              *)
(*  数学核：                                                                *)
(*    · 族载体（Set 承载·Defined 可提取）：gcl_famv m M x y =               *)
(*        (1/2)·[T^(m+2)·F(x,y) + T̄^(m+2)·F(1−x,1−y)]，                    *)
(*      其中 F = zb2 段列逐点求值（zb2_beval_l ∘ zb2_segl），T=1−xy、       *)
(*      T̄=x+y−xy 为 DIG 双形 sup 证书的组论轨道两位（Gsw 轨两点重合）。      *)
(*    · A-侧闭式（截断母恒等式 zb2_master 的序面 zb2_ps_bound，两轨道       *)
(*      代表各档）：T^(m+2)·F(x,y) ≤ N^(m+1) 且                            *)
(*      T̄^(m+2)·F(1−x,1−y) ≤ N^(m+1)——故 gcl_famv ≤ N^(m+1)。              *)
(*    · 衰减侧（对称化算子 gcl_avg_cert）：12N ≤ Tavg 且                    *)
(*      Tavg ≤ 1（1−Tavg=((1−x)(1−y)+xy)/2 ≥ 0）⟹ N^(m+1) ≤ (1/12)^(m+1)   *)
(*      ≤ (1/4)(1/12)^m = gcl_weight_G m（1/12 ≤ 1/4）。                    *)
(*    · 具名序列 gcl_famseq m = gcl_famv m m (1/2,1/2)（τ-不动点锚）：      *)
(*      严格正＋族界全证——gcl_sep_generic 的 Fam 插槽以 gcl_famseq          *)
(*      供件确立，分离结论 d²·gcl_famseq m < 1（m≥3·0≤d≤3^(m+1)）无条件化。  *)
(*      锚点字面值：gcl_famseq 3 = 58077/4294967296，                      *)
(*      81²·famseq3 = 381059397/4294967296 < 1（独立复算一致）。            *)
(*  实现注记：QltT = Id (Qlt_bool …) true 的 bool 包裹下 setoid rewrite 无  *)
(*        Qlt_bool 抬升实例——凡 Qlt/QltT 层一律免 rewrite（cbn [q_pow] iota *)
(*        直约＋字面 lia＋Qlt_le_trans 链），rewrite 仅限裸 Q/Qle/QleT'。   *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；S01_BaseRing、          *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists；abl_z2_truncfam       *)
(*        （zb2_ps 母恒等式序面）、abl_z2_itg_carrier（段列求值）；          *)
(*        abl_dmw2_pointwise_sharp；dig_machine；gcl_coefficient            *)
(*        （gcl_sep_generic/gcl_avg_cert/gcl_weight_G/gcl_copl_invol_x）。  *)
(*  对标：Rhin–Viola 组结构置换群法（ζ(2) 双积分方法核）之对称化截断层。      *)
(*  构造性注记：全语句 Set 承载；Print Assumptions 全谱 Closed；             *)
(*        Separate Extraction Obj.magic=0；零实数层、零经典逻辑、零 Admitted。*)
(*  诚实边界：gcl_famseq 为族在 τ-不动点的实例值序列（插槽供件形）；族积分    *)
(*        值序列（Isum^sym）与分母链装配不在本件——μ_lib 为点wise/锚点刻形档。 *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" gcl_famsym.v            *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier abl_dmw2_pointwise_sharp dig_machine.
Require Import gcl_coefficient.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 小件舱：幂正性、幂单调、收缩界、Tavg 方块面、换位面                        *)
(* ============================================================ *)

(* 幂严格正：0 < a ⟹ 0 < a^k（Qlt 层·免 rewrite·cbn iota 直约） *)
Lemma gcl_q_pow_pos : forall (a : Q) (k : nat),
  Qlt 0 a -> Qlt 0 (q_pow a k).
Proof.
  intros a k H. induction k as [| k IH].
  - cbn [q_pow]. unfold Qlt; cbn [Qnum Qden]; lia.
  - cbn [q_pow]. apply Qmult_lt_0_compat; assumption.
Qed.

(* 幂单调：0 ≤ a ≤ b ⟹ a^k ≤ b^k *)
Lemma gcl_q_pow_mono : forall (a b : Q) (k : nat),
  0 <= a -> a <= b -> q_pow a k <= q_pow b k.
Proof.
  intros a b k Ha Hab. induction k as [| k IH].
  - cbn [q_pow]. apply Qle_refl.
  - cbn [q_pow].
    assert (Hb : 0 <= b) by (apply (Qle_trans 0 a b); assumption).
    assert (Hpa : 0 <= q_pow a k) by (apply q_pow_nonneg; exact Ha).
    apply (Qle_trans _ (b * q_pow a k)).
    + apply (Qmult_le_compat_r a b (q_pow a k) Hab Hpa).
    + assert (H2 : q_pow a k * b <= q_pow b k * b)
        by (apply (Qmult_le_compat_r (q_pow a k) (q_pow b k) b IH Hb)).
      assert (Hc1 : b * q_pow a k == q_pow a k * b) by ring.
      assert (Hc2 : b * q_pow b k == q_pow b k * b) by ring.
      rewrite Hc1, Hc2. exact H2.
Qed.

(* 收缩界：0 ≤ u ≤ 1、0 ≤ a ⟹ (a·u)^k ≤ a^k *)
Lemma gcl_q_pow_scale_le : forall (u a : Q) (k : nat),
  0 <= u -> u <= 1 -> 0 <= a -> q_pow (a * u) k <= q_pow a k.
Proof.
  intros u a k Hu Hua Ha. induction k as [| k IH].
  - cbn [q_pow]. apply Qle_refl.
  - cbn [q_pow].
    assert (Hp0 : 0 <= q_pow (a * u) k)
      by (apply q_pow_nonneg; apply Qmult_le_0_compat; assumption).
    apply (Qle_trans _ (a * q_pow (a * u) k)).
    + apply (Qmult_le_compat_r (a * u) a (q_pow (a * u) k)).
      * assert (Hau0 : u * a <= 1 * a) by (apply (Qmult_le_compat_r u 1 a Hua Ha)).
        assert (Hau : a * u <= a).
        { assert (E1 : a * u == u * a) by ring. rewrite E1.
          assert (E2 : 1 * a == a) by ring. rewrite E2 in Hau0.
          exact Hau0. }
        exact Hau.
      * exact Hp0.
    + assert (H2 : q_pow (a * u) k * a <= q_pow a k * a)
        by (apply (Qmult_le_compat_r (q_pow (a * u) k) (q_pow a k) a IH Ha)).
      assert (Hc1 : a * q_pow (a * u) k == q_pow (a * u) k * a) by ring.
      assert (Hc2 : a * q_pow a k == q_pow a k * a) by ring.
      rewrite Hc1, Hc2. exact H2.
Qed.

(* 换位面：0 ≤ x ⟹ 1−x ≤ 1；x ≤ 1 ⟹ 0 ≤ 1−x（Gco 生成元保方块） *)
Lemma gcl_le1_swap : forall x : Q, 0 <= x -> 1 - x <= 1.
Proof.
  intros x H. apply (dmw2_sub_ge0 (1 - x) 1).
  rewrite gcl_copl_invol_x. exact H.
Qed.

Lemma gcl_ge0_swap : forall x : Q, x <= 1 -> 0 <= 1 - x.
Proof.
  intros x H. apply (dmw2_le_sub x 1). exact H.
Qed.

(* 裸 Qle 换形桥：x == y、z ≤ x ⟹ z ≤ y（免 rewrite 过桥） *)
Lemma gcl_qle_wd : forall x y z : Q, x == y -> z <= x -> z <= y.
Proof.
  intros x y z Hxy Hz. apply (Qle_trans z x y).
  - exact Hz.
  - apply qeq_imp_qle. exact Hxy.
Qed.

(* Tavg 非负：1+x+y−2xy = 1+x(1−y)+y(1−x) ≥ 0 于方块 *)
Lemma gcl_Tavg_ge0 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> 0 <= gcl_Tavg x y.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2. unfold gcl_Tavg.
  assert (E : 1 + x + y - 2 * x * y == 1 + x * (1 - y) + y * (1 - x)) by ring.
  rewrite E.
  assert (HA : 0 <= x * (1 - y)).
  { apply Qmult_le_0_compat.
    - exact Hx1.
    - apply (dmw2_le_sub y 1). exact Hy2. }
  assert (HB : 0 <= y * (1 - x)).
  { apply Qmult_le_0_compat.
    - exact Hy1.
    - apply (dmw2_le_sub x 1). exact Hx2. }
  assert (Ec : (1#2) * (1 + x * (1 - y) + y * (1 - x))
            == (1 + x * (1 - y) + y * (1 - x)) * (1#2)) by ring.
  rewrite Ec.
  assert (H1' : 1 <= 1 + x * (1 - y) + y * (1 - x)).
  { assert (E4 : 1 + x * (1 - y) + y * (1 - x)
              == 1 + (x * (1 - y) + y * (1 - x))) by ring.
    rewrite E4.
    apply (dmw2_add_ge0_le 1 (x * (1 - y) + y * (1 - x))).
    apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
    - exact HA.
    - apply (dmw2_add_ge0_le (x * (1 - y)) (y * (1 - x))). exact HB. }
  apply Qmult_le_0_compat.
  - apply (Qle_trans 0 1 (1 + x * (1 - y) + y * (1 - x))).
    + unfold Qle. simpl. lia.
    + exact H1'.
  - unfold Qle. simpl. lia.
Qed.

(* Tavg ≤ 1：1−Tavg = ((1−x)(1−y)+xy)/2 ≥ 0 *)
Lemma gcl_Tavg_le_1 : forall x y : Q,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> gcl_Tavg x y <= 1.
Proof.
  intros x y Hx1 Hx2 Hy1 Hy2. unfold gcl_Tavg.
  apply (dmw2_sub_ge0 (gcl_Tavg x y) 1).
  assert (E : 1 - (1#2) * (1 + x + y - 2 * x * y)
           == ((1 - x) * (1 - y) + x * y) * (1#2)) by ring.
  rewrite E. apply Qmult_le_0_compat.
  - apply (Qle_trans 0 ((1 - x) * (1 - y)) ((1 - x) * (1 - y) + x * y)).
    + apply Qmult_le_0_compat.
      * apply (gcl_ge0_swap x Hx2).
      * apply (gcl_ge0_swap y Hy2).
    + apply (dmw2_add_ge0_le ((1 - x) * (1 - y)) (x * y)).
      apply Qmult_le_0_compat; assumption.
  - unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* §1 段列求值序面：部分和序面与锚点严格正                                      *)
(* ============================================================ *)

(* 部分和非负：逐项 C(n+k,n)·t^k ≥ 0（0 ≤ t） *)
Lemma gcl_ps_ge0 : forall n M t, 0 <= t -> QleT' 0 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply (zb2_qleT'_wd_r 1 (zb2_ps n 0 t) 0).
    + apply (Qeq_sym _ _ (zb2_ps_zero n t)).
    + apply Qle_to_QleT'. unfold Qle. simpl. lia.
  - apply (zb2_qleT'_wd_r (zb2_ps n M t
                             + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                               * q_pow t (Datatypes.S M))
                          (zb2_ps n (Datatypes.S M) t) 0).
    + apply (Qeq_sym _ _ (zb2_ps_unfold n M t)).
    + apply Qle_to_QleT'.
      assert (Hterm : 0 <= (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                           * q_pow t (Datatypes.S M)).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        - apply q_pow_nonneg. exact Ht. }
      apply (Qle_trans 0 (zb2_ps n M t)
               (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                                * q_pow t (Datatypes.S M))).
      * apply QleT'_to_Qle. exact IH.
      * apply (dmw2_add_ge0_le _ _ Hterm).
Qed.

(* 部分和下界 1：首项 C(n,n)=1（0 ≤ t 保尾项非负） *)
Lemma gcl_ps_ge1 : forall n M t, 0 <= t -> QleT' 1 (zb2_ps n M t).
Proof.
  intros n M t Ht. induction M as [| M IH].
  - apply (zb2_qleT'_wd_r 1 (zb2_ps n 0 t) 1).
    + apply (Qeq_sym _ _ (zb2_ps_zero n t)).
    + apply Qle_to_QleT'. apply Qle_refl.
  - apply (zb2_qleT'_wd_r (zb2_ps n M t
                             + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                               * q_pow t (Datatypes.S M))
                          (zb2_ps n (Datatypes.S M) t) 1).
    + apply (Qeq_sym _ _ (zb2_ps_unfold n M t)).
    + apply Qle_to_QleT'.
      assert (Htail : 0 <= (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                        * q_pow t (Datatypes.S M)).
      { apply Qmult_le_0_compat.
        - apply QleT'_to_Qle. apply zb2_bkC_Q_nonneg.
        - apply q_pow_nonneg. exact Ht. }
      pose proof (QleT'_to_Qle _ _ IH) as IHq.
      apply (Qle_trans 1 (zb2_ps n M t)
               (zb2_ps n M t + (Z.of_nat (bkC (n + Datatypes.S M) n) # 1)
                                * q_pow t (Datatypes.S M))).
      * exact IHq.
      * apply (dmw2_add_ge0_le _ _ Htail).
Qed.

(* 段列求值非负：Nx^n·Ny^n·ps ≥ 0 于全方块 *)
Lemma gcl_beval_seg_ge0 : forall n M x y,
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  0 <= zb2_beval_l (zb2_segl n M) x y.
Proof.
  intros n M x y Hx1 Hx2 Hy1 Hy2.
  pose proof (zb2_beval_segl n M x y) as Hseg.
  apply (gcl_qle_wd _ _ 0 (Qeq_sym _ _ Hseg)).
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (HNx : 0 <= x * (1 - x)) by (apply Qmult_le_0_compat; assumption).
  assert (HNy : 0 <= y * (1 - y)) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat.
    + apply q_pow_nonneg. exact HNx.
    + apply q_pow_nonneg. exact HNy.
  - apply QleT'_to_Qle. apply gcl_ps_ge0. exact Hxy0.
Qed.

(* 锚点段列求值下界：F(1/2,1/2) ≥ ((1/4)·(1/4))^n = (1/16)^n *)
Lemma gcl_beval_seg_anchor_ge : forall n M,
  q_pow ((1#4)*(1#4)) n <= zb2_beval_l (zb2_segl n M) (1#2) (1#2).
Proof.
  intros n M.
  assert (Hq2 : (1#2)*(1#2) == (1#4)) by reflexivity.
  assert (Ht4 : 0 <= (1#2)*(1#2)) by (rewrite Hq2; unfold Qle; cbn [Qnum Qden]; lia).
  pose proof (QleT'_to_Qle _ _ (gcl_ps_ge1 n M ((1#2)*(1#2)) Ht4)) as HP.
  assert (Hps0 : 0 <= zb2_ps n M ((1#2)*(1#2))).
  { apply (Qle_trans 0 1 _).
    - unfold Qle. simpl. lia.
    - exact HP. }
  pose proof (zb2_beval_segl n M (1#2) (1#2)) as Hseg.
  apply (gcl_qle_wd _ (zb2_beval_l (zb2_segl n M) (1#2) (1#2))
           (q_pow ((1#4)*(1#4)) n) (Qeq_sym _ _ Hseg)).
  assert (Hr1 : q_pow ((1#4)*(1#4)) n == q_pow ((1#4)*(1#4)) n * 1) by ring.
  apply (Qle_trans _ (q_pow ((1#4)*(1#4)) n * 1)).
  - apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n) (q_pow ((1#4)*(1#4)) n * 1)
                      (q_pow ((1#4)*(1#4)) n) Hr1).
    apply Qle_refl.
  - assert (Hq : (1#2) * (1 - (1#2)) == (1#4)) by reflexivity.
    rewrite Hq.
    assert (HX4 : 0 <= q_pow (1#4) n)
      by (apply q_pow_nonneg; unfold Qle; simpl; lia).
    assert (HXX0 : 0 <= q_pow (1#4) n * q_pow (1#4) n)
      by (apply Qmult_le_0_compat; exact HX4).
    assert (Ht2 : 1 * (q_pow (1#4) n * q_pow (1#4) n)
               <= zb2_ps n M ((1#2)*(1#2)) * (q_pow (1#4) n * q_pow (1#4) n))
      by (apply (Qmult_le_compat_r 1 (zb2_ps n M ((1#2)*(1#2)))
                   (q_pow (1#4) n * q_pow (1#4) n))
           ; [ exact HP | exact HXX0 ]).
    assert (E5 : 1 * (q_pow (1#4) n * q_pow (1#4) n)
              == q_pow (1#4) n * q_pow (1#4) n * 1) by ring.
    assert (E6 : zb2_ps n M ((1#2)*(1#2)) * (q_pow (1#4) n * q_pow (1#4) n)
              == q_pow (1#4) n * q_pow (1#4) n * zb2_ps n M ((1#2)*(1#2))) by ring.
    rewrite E5, E6 in Ht2.
    assert (Hle1 : q_pow ((1#4)*(1#4)) n * 1 <= q_pow ((1#4)*(1#4)) n).
    { apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n * 1)
                        (q_pow ((1#4)*(1#4)) n)
                        (q_pow ((1#4)*(1#4)) n * 1)
             (Qeq_sym _ _ Hr1)).
      apply Qle_refl. }
    assert (Hax : q_pow ((1#4)*(1#4)) n
               == q_pow (1#4) n * q_pow (1#4) n * 1).
    { pose proof (zb2_q_pow_mul (1#4) (1#4) n) as Hpm.
      rewrite Hpm. ring. }
    apply (Qle_trans _ (q_pow (1#4) n * q_pow (1#4) n * 1)).
    + apply (gcl_qle_wd (q_pow ((1#4)*(1#4)) n)
                        (q_pow (1#4) n * q_pow (1#4) n * 1)
                        (q_pow ((1#4)*(1#4)) n * 1) Hax Hle1).
    + exact Ht2.
Qed.

(* 锚点段列求值严格正：F(1/2,1/2) > 0 *)
Lemma gcl_beval_seg_anchor_pos : forall n M,
  Qlt 0 (zb2_beval_l (zb2_segl n M) (1#2) (1#2)).
Proof.
  intros n M.
  assert (Hpos : Qlt 0 (q_pow ((1#4)*(1#4)) n))
    by (apply gcl_q_pow_pos; unfold Qlt; cbn [Qnum Qden Qmult Pos.mul]; lia).
  apply (Qlt_le_trans 0 (q_pow ((1#4)*(1#4)) n)).
  - exact Hpos.
  - apply gcl_beval_seg_anchor_ge.
Qed.

(* ============================================================ *)
(* §2 A-侧闭式：截断母恒等式两轨道代表（T 档与 T̄ 档）                            *)
(* ============================================================ *)

(* 主代表：T^(m+2)·F(x,y) ≤ N^(m+1)（zb2_ps_bound 于 t=xy） *)
Lemma gcl_famv_A : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
  <= q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  rewrite (zb2_beval_segl (Datatypes.S m) M x y).
  assert (HN : x*(1-x)*y*(1-y) == (x*(1-x))*(y*(1-y))) by ring.
  rewrite HN.
  rewrite <- (zb2_q_pow_mul (x*(1-x)) (y*(1-y)) (Datatypes.S m)).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x*y)
        (conj (Qmult_le_0_compat x y Hx1 Hy1)
              (dmw2_xy_le_1 x y Hx1 Hx2 Hy1 Hy2))) as Hps.
  pose proof (QleT'_to_Qle _ _ Hps) as Hpsq.
  assert (HN0 : 0 <= q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)).
  { apply q_pow_nonneg.
    assert (HNn : 0 <= x*(1-x)*y*(1-y))
      by (apply (dmw2_mult4_ge0 x (1-x) y (1-y)); assumption).
    apply (gcl_qle_wd (x*(1-x)*y*(1-y)) ((x*(1-x))*(y*(1-y))) 0 HN).
    exact HNn. }
  assert (E : q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                * (q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
                   * zb2_ps (Datatypes.S m) M (x*y))
           == (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                * zb2_ps (Datatypes.S m) M (x*y))
              * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)) by ring.
  rewrite E.
  apply (Qle_trans _ (1 * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))).
  - apply (Qmult_le_compat_r (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                                * zb2_ps (Datatypes.S m) M (x*y))
                             1
                             (q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))
                          Hpsq HN0).
  - assert (H1 : 1 * q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
              == q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)) by ring.
    rewrite H1. apply Qle_refl.
Qed.

(* 共轭代表：T̄^(m+2)·F(1−x,1−y) ≤ N^(m+1)（主代表于 (1−x,1−y) 的实例） *)
Lemma gcl_famv_A_copl : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
    * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y)
  <= q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hx' : 0 <= 1 - x) by (apply (gcl_ge0_swap x Hx2)).
  assert (Hx'1 : 1 - x <= 1) by (apply (gcl_le1_swap x Hx1)).
  assert (Hy' : 0 <= 1 - y) by (apply (gcl_ge0_swap y Hy2)).
  assert (Hy'1 : 1 - y <= 1) by (apply (gcl_le1_swap y Hy1)).
  pose proof (gcl_famv_A m M (1-x) (1-y) Hx' Hx'1 Hy' Hy'1) as H.
  assert (E2 : q_pow ((1-x)*(1-(1-x))*(1-y)*(1-(1-y))) (Datatypes.S m)
            == q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m))
    by (apply q_pow_wd; ring).
  rewrite E2 in H.
  assert (E3 : q_pow ((x*(1-x))*(y*(1-y))) (Datatypes.S m)
            == q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
    by (apply q_pow_wd; ring).
  rewrite E3 in H. exact H.
Qed.

(* ============================================================ *)
(* §3 族定义与族界主定理（插槽前提 II）                                          *)
(* ============================================================ *)

(* 对称化截断族载体（Set 承载·Defined 可提取）：
   V4 轨道平均（Gsw 轨两点重合）的 T-分母截断族实例。 *)
Definition gcl_famv (m M : nat) (x y : Q) : Q :=
  (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
             * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
           + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
             * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y)).

(* 具名实例序列：τ-不动点锚 (1/2,1/2) 档（gcl_sep_generic 的 Fam 供件形） *)
Definition gcl_famseq (m : nat) : Q := gcl_famv m m (1#2) (1#2).

(* 族界主定理：gcl_famv ≤ (1/4)(1/12)^m 于全方块。
   链：均值 ≤ N^(m+1)（A-侧双代表）≤ (1/12)^(m+1)（12N ≤ Tavg·Tavg ≤ 1）
   ≤ (1/4)(1/12)^m。 *)
Theorem gcl_famv_le_weight : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' (gcl_famv m M x y) (gcl_weight_G m).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2.
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  unfold gcl_famv.
  pose proof (gcl_famv_A m M x y Hx1 Hx2 Hy1 Hy2) as HA.
  pose proof (gcl_famv_A_copl m M x y Hx1 Hx2 Hy1 Hy2) as HB.
  (* 均值 ≤ N^(m+1) *)
  assert (Havg : (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                              * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                            + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                              * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
              <= q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)).
  { apply (Qle_trans _
             ((1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                       + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)))).
    - assert (H2 : (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                         * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                       + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                         * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                     * (1#2)
                  <= (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                      + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) * (1#2))
        by (apply (Qmult_le_compat_r
                     (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                        * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                      + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                        * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                     (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                      + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) (1#2))
          ; [ apply Qplus_le_compat; assumption | unfold Qle; simpl; lia ]).
      assert (Hc1 : (1#2) * (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                                * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                              + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                                * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                 == (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                       * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                       * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y))
                      * (1#2)) by ring.
      assert (Hc2 : (1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                             + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
                 == (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                     + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) * (1#2)) by ring.
      rewrite Hc1, Hc2. exact H2.
    - assert (Hr : (1#2) * (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
                            + q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))
              == q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)) by ring.
      rewrite Hr. apply Qle_refl. }
  (* 衰减侧：12N ≤ Tavg ⟹ N ≤ Tavg·(1/12) *)
  pose proof (gcl_avg_cert x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hcert.
  assert (Hcert' : QleT' (12 * (x*(1-x)*y*(1-y))) (gcl_Tavg x y)).
  { pose proof (QleT'_to_Qle _ _ Hcert) as HCq.
    assert (E0 : 12 * x * (1 - x) * y * (1 - y) == 12 * (x*(1-x)*y*(1-y))) by ring.
    rewrite E0 in HCq.
    apply Qle_to_QleT'. exact HCq. }
  pose proof (QleT'_to_Qle _ _ Hcert') as Hcq.
  assert (HNle : x*(1-x)*y*(1-y) <= gcl_Tavg x y * (1#12)).
  { pose proof (Qmult_le_compat_r (12 * (x*(1-x)*y*(1-y))) (gcl_Tavg x y) (1#12)
                  Hcq ltac:(unfold Qle; simpl; lia)) as Hm.
    assert (E : (12 * (x*(1-x)*y*(1-y))) * (1#12) == x*(1-x)*y*(1-y)) by ring.
    rewrite E in Hm. exact Hm. }
  (* 幂链：N^(m+1) ≤ ((1/12)·Tavg)^(m+1) ≤ (1/12)^(m+1) = (1/12)·(1/12)^m *)
  assert (Ern : gcl_Tavg x y * (1#12) == (1#12) * gcl_Tavg x y) by ring.
  rewrite Ern in HNle.
  assert (Hpow : q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m)
              <= (1#12) * q_pow (1#12) m).
  { apply (Qle_trans _ (q_pow ((1#12) * gcl_Tavg x y) (Datatypes.S m))).
    - apply gcl_q_pow_mono.
      + apply (dmw2_mult4_ge0 x (1-x) y (1-y)); assumption.
      + exact HNle.
    - apply (Qle_trans _ (q_pow (1#12) (Datatypes.S m))).
      + apply gcl_q_pow_scale_le.
        * apply gcl_Tavg_ge0; assumption.
        * apply gcl_Tavg_le_1; assumption.
        * unfold Qle. simpl. lia.
      + rewrite (q_pow_succ (1#12) m). apply Qle_refl. }
  unfold gcl_weight_G. apply Qle_to_QleT'.
  apply (Qle_trans _ (q_pow (x*(1-x)*y*(1-y)) (Datatypes.S m))).
  - exact Havg.
  - apply (Qle_trans _ ((1#12) * q_pow (1#12) m)).
    + exact Hpow.
    + apply Qmult_le_compat_r.
      * unfold Qle. simpl. lia.
      * apply q_pow_nonneg. unfold Qle. simpl. lia.
Qed.

(* 插槽前提 I：族非负 *)
Theorem gcl_famv_ge0 : forall (m M : nat) (x y : Q),
  0 <= x -> x <= 1 -> 0 <= y -> y <= 1 ->
  QleT' 0 (gcl_famv m M x y).
Proof.
  intros m M x y Hx1 Hx2 Hy1 Hy2. unfold gcl_famv.
  apply Qle_to_QleT'.
  assert (HA0 : 0 <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                  * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
  { apply Qmult_le_0_compat.
    - apply q_pow_nonneg.
      apply (gcl_ge0_swap (x*y) (dmw2_xy_le_1 x y Hx1 Hx2 Hy1 Hy2)).
    - apply gcl_beval_seg_ge0; assumption. }
  assert (HB0 : 0 <= q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                  * zb2_beval_l (zb2_segl (Datatypes.S m) M) (1-x) (1-y)).
  { apply Qmult_le_0_compat.
    - apply q_pow_nonneg.
      apply (gcl_ge0_swap ((1-x)*(1-y))
               (dmw2_xy_le_1 (1-x) (1-y)
                  (gcl_ge0_swap x Hx2) (gcl_le1_swap x Hx1)
                  (gcl_ge0_swap y Hy2) (gcl_le1_swap y Hy1))).
    - apply gcl_beval_seg_ge0
        ; [ apply (gcl_ge0_swap x Hx2) | apply (gcl_le1_swap x Hx1)
          | apply (gcl_ge0_swap y Hy2) | apply (gcl_le1_swap y Hy1) ]. }
  apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply (Qle_trans 0 (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                       (q_pow (1 - x*y) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                         + q_pow (1 - (1-x)*(1-y)) (Datatypes.S (Datatypes.S m))
                           * zb2_beval_l (zb2_segl (Datatypes.S m) M)
                               (1-x) (1-y))).
    + exact HA0.
    + apply (dmw2_add_ge0_le _ _ HB0).
Qed.

(* ============================================================ *)
(* §4 具名序列：τ-不动点锚档严格正＋插槽收束                                     *)
(* ============================================================ *)

(* 具名序列严格正：A 档 (3/4)^(m+2)·F_anchor > 0（gcl_q_pow_pos 于 3/4
   与 gcl_beval_seg_anchor_pos 的 Qmult_lt_0_compat），B 档 ≥ 0，和 > 0。 *)
Theorem gcl_famseq_pos : forall m : nat, QltT 0 (gcl_famseq m).
Proof.
  intro m. unfold gcl_famseq, gcl_famv.
  assert (Hh : 0 <= 1 - (1#2))
    by exact (proj1 (Qle_bool_iff 0 (1 - (1#2))) eq_refl).
  assert (Hh1 : 1 - (1#2) <= 1)
    by (apply gcl_le1_swap; exact (proj1 (Qle_bool_iff 0 (1 - (1#2))) eq_refl)).
  assert (HA : 0 < q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) m) (1#2) (1#2)).
  { apply Qmult_lt_0_compat.
    - apply gcl_q_pow_pos.
      apply (Qlt_le_trans 0 (3#4)).
      + apply QltT_to_Qlt.
        exact (id_refl (A:=bool) (x:=Qlt_bool 0 (3#4))).
      + assert (Hq3 : (1 - (1#2)*(1#2)) == (3#4)) by reflexivity.
        rewrite Hq3. apply Qle_refl.
    - apply gcl_beval_seg_anchor_pos. }
  assert (HB : 0 <= q_pow (1 - (1 - (1#2))*(1 - (1#2))) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                     (1 - (1#2)) (1 - (1#2))).
  { apply Qmult_le_0_compat.
    - apply q_pow_nonneg.
      exact (proj1 (Qle_bool_iff 0 (1 - (1 - (1#2))*(1 - (1#2)))) eq_refl).
    - apply gcl_beval_seg_ge0; assumption. }
  assert (Hsum : 0 < q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                   * zb2_beval_l (zb2_segl (Datatypes.S m) m) (1#2) (1#2)
                 + q_pow (1 - (1 - (1#2))*(1 - (1#2))) (Datatypes.S (Datatypes.S m))
                   * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                       (1 - (1#2)) (1 - (1#2))).
  { apply (Qlt_le_trans 0 (q_pow (1 - (1#2)*(1#2)) (Datatypes.S (Datatypes.S m))
                             * zb2_beval_l (zb2_segl (Datatypes.S m) m)
                                 (1#2) (1#2))).
    - exact HA.
    - apply (dmw2_add_ge0_le _ _ HB). }
  apply Qlt_to_QltT. apply Qmult_lt_0_compat.
  - unfold Qlt; cbn [Qnum Qden]; lia.
  - exact Hsum.
Qed.

(* 插槽收束（主定理）：gcl_sep_generic 以 Fam := gcl_famseq 实例化——
   两前提由 §3/§4 供件消去，分离结论无条件化。 *)
Theorem gcl_famseq_sep : forall (m : nat) (d : Q),
  (3 <= m)%nat -> QleT' 0 d -> QleT' d (q_pow 3 (Datatypes.S m)) ->
  QltT (d * d * gcl_famseq m) 1.
Proof.
  intros m d Hm Hd0 Hd.
  apply (gcl_sep_generic (fun m0 : nat => gcl_famseq m0) m d Hm Hd0 Hd).
  - unfold gcl_famseq. apply gcl_famv_ge0
      ; [ unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia ].
  - unfold gcl_famseq. apply gcl_famv_le_weight
      ; [ unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia
        | unfold Qle; cbn [Qnum Qden]; lia ].
Qed.

(* 数值锚（独立复算⑤一致·vm_compute 字面） *)
Lemma gcl_famseq_val0 : gcl_famseq 0 == (9#256).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_famseq_val3 : gcl_famseq 3 == (58077#4294967296).
Proof. vm_compute. reflexivity. Qed.

Lemma gcl_famseq_sep_concrete : QltT (81 * 81 * gcl_famseq 3) 1.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 提取与假设审计                                                            *)
(* ============================================================ *)

Separate Extraction gcl_famv gcl_famseq.

Print Assumptions gcl_famv_le_weight.
Print Assumptions gcl_famv_ge0.
Print Assumptions gcl_famseq_pos.
Print Assumptions gcl_famseq_sep.
Print Assumptions gcl_famseq_val3.
Print Assumptions gcl_famseq_sep_concrete.
