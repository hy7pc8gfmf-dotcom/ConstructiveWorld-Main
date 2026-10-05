(* ============================================================ *)
(* abl_div_chisq_twopoint.v                                       *)
(* 模块名：abl_div_chisq_twopoint                                  *)
(* 数学使命：两点分布 χ² 散度载件与代数桥——载件 div2_cs 定义为      *)
(*   (p−q)²/q + (p−q)²/(1−q)，配套闭式恒等（纯环）、Bishop 形非负、  *)
(*   无条件下臂（四倍 TV 平方不超过 χ²）与条件上臂（最小质量 m 证书   *)
(*   下 χ² 不超过二倍 TV 平方除 m），全件零对数、零指数、零分支。    *)
(* 依赖清单：S01_BaseRing、S02_CauchyComplete、S03_QExp、           *)
(*   S07_RealSetoidExpLog、PinskerTwoPoint（p2_tvsq/p2_one_minus/    *)
(*   p2_diff/p2_ring_eq）、UpRealLeB（real_le_b/平方非负完成件）、    *)
(*   UpRealLeB2（Bishop 和兼容件）、UpRealLeB3（Bishop 运输件族）。   *)
(* 构造性注记：全件 Set 层出口；非严格序取 Bishop 形 real_le_b       *)
(*   （与在役 pnk2_pinsker_one 同款出口，零 Or 形平方非负位）；       *)
(*   零承认式语句、零经典公理、全部 Qed 闭合；正性证书位显式随行。    *)
(* 编译配方：                                                       *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*   ulimit -s 65532 && cd <池> && nice -19 rocq c -native-compiler  *)
(*   no -Q <缓存根> "" abl_div_chisq_twopoint.v                      *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import PinskerTwoPoint.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ---- 0. 数值常数：二与四（以壹累加显式构造） ---- *)

Definition d2_two : Real := real_plus real_one real_one.
Definition d2_four : Real := real_plus d2_two d2_two.

Lemma d2_two_pos : real_lt real_zero d2_two.
Proof.
  exact (real_plus_positive real_one real_one real_lt_zero_one real_lt_zero_one).
Qed.

Lemma d2_four_pos : real_lt real_zero d2_four.
Proof.
  exact (real_plus_positive d2_two d2_two d2_two_pos d2_two_pos).
Qed.

(* ---- 1. 载件定义：χ²(P‖Q) := (p−q)²/q + (p−q)²/(1−q) ---- *)

Definition div2_cs (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
            (real_mult (p2_tvsq p q) (real_inv_pos (p2_one_minus q) Hq1)).

(* ---- 2. 消去与倍加小件（全后文公用） ---- *)

(* x·y·inv(y) == x（inv_correct 右消去，real_eq 链） *)
Lemma d2_mult_inv_r : forall (x y : Real) (Hy : real_lt real_zero y),
  real_eq (real_mult (real_mult x y) (real_inv_pos y Hy)) x.
Proof.
  intros x y Hy.
  apply (real_eq_trans (real_mult (real_mult x y) (real_inv_pos y Hy))
                       (real_mult x (real_mult y (real_inv_pos y Hy))) x).
  - apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans (real_mult x (real_mult y (real_inv_pos y Hy)))
             (real_mult x real_one) x).
    + apply (RealSetoid.real_eq_mult_compat x
               (real_mult y (real_inv_pos y Hy)) x real_one).
      * apply real_eq_refl.
      * exact (real_inv_pos_correct y Hy).
    + apply real_mult_one.
Qed.

(* 任意 X 的倍加恒等：X+X == 二·X（逐点纯环，X 可含任意不透明项） *)
Lemma d2_double : forall X : Real,
  real_eq (real_plus X X) (real_mult (real_plus real_one real_one) X).
Proof.
  intros X.
  apply real_eq_of_zero_diff. intro n0.
  repeat match goal with [ x : Real |- _ ] => destruct x end.
  cbn [projT1 real_plus real_mult real_one real_zero].
  ring.
Qed.

(* ---- 3. 部分分式与闭式恒等（件 1a） ---- *)

(* 乘法重组：(a·b)·c == b·(a·c)（纯环链） *)
Lemma d2_swap_assoc : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult b (real_mult a c)).
Proof.
  intros a b c.
  apply (real_eq_trans (real_mult (real_mult a b) c)
                       (real_mult a (real_mult b c))
                       (real_mult b (real_mult a c))).
  - apply real_eq_sym. apply real_mult_assoc.
  - apply (real_eq_trans (real_mult a (real_mult b c))
                         (real_mult (real_mult b a) c)
                         (real_mult b (real_mult a c))).
    + apply (real_eq_trans (real_mult a (real_mult b c))
                           (real_mult (real_mult a b) c)
                           (real_mult (real_mult b a) c)).
      * apply real_mult_assoc.
      * apply (RealSetoid.real_eq_mult_compat (real_mult a b) c
                 (real_mult b a) c).
        -- apply real_mult_comm.
        -- apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* 部分分式核：inv(q·(1−q)) == inv(q)+inv(1−q)。
   路线：inv_unique——q·q1 作公共乘子，两侧均乘出壹。 *)
Lemma d2_inv_split : forall (q : Real) (Hq : real_lt real_zero q)
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
          (real_plus (real_inv_pos q Hq)
                     (real_inv_pos (p2_one_minus q) Hq1)).
Proof.
  intros q Hq Hq1 Hqq1.
  apply (real_inv_unique (real_mult q (p2_one_minus q))
           (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
           (real_plus (real_inv_pos q Hq)
                      (real_inv_pos (p2_one_minus q) Hq1))).
  - apply real_inv_pos_correct.
  - apply (real_eq_trans
             (real_mult (real_mult q (p2_one_minus q))
                (real_plus (real_inv_pos q Hq)
                           (real_inv_pos (p2_one_minus q) Hq1)))
             (real_plus
                (real_mult (p2_one_minus q)
                           (real_mult q (real_inv_pos q Hq)))
                (real_mult q
                   (real_mult (p2_one_minus q)
                              (real_inv_pos (p2_one_minus q) Hq1))))
             real_one).
    + apply (real_eq_trans
               (real_mult (real_mult q (p2_one_minus q))
                  (real_plus (real_inv_pos q Hq)
                             (real_inv_pos (p2_one_minus q) Hq1)))
               (real_plus
                  (real_mult (real_mult q (p2_one_minus q))
                             (real_inv_pos q Hq))
                  (real_mult (real_mult q (p2_one_minus q))
                             (real_inv_pos (p2_one_minus q) Hq1)))
               (real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult q (real_inv_pos q Hq)))
                  (real_mult q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))))).
      * apply real_distrib.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_mult q (p2_one_minus q)) (real_inv_pos q Hq))
                 (real_mult (real_mult q (p2_one_minus q))
                            (real_inv_pos (p2_one_minus q) Hq1))
                 (real_mult (p2_one_minus q) (real_mult q (real_inv_pos q Hq)))
                 (real_mult q
                    (real_mult (p2_one_minus q)
                               (real_inv_pos (p2_one_minus q) Hq1)))).
        -- exact (d2_swap_assoc q (p2_one_minus q) (real_inv_pos q Hq)).
        -- apply real_eq_sym. apply real_mult_assoc.
    + apply (real_eq_trans
               (real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult q (real_inv_pos q Hq)))
                  (real_mult q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))))
               (real_plus (p2_one_minus q) q)
               real_one).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (p2_one_minus q) (real_mult q (real_inv_pos q Hq)))
                 (real_mult q
                    (real_mult (p2_one_minus q)
                               (real_inv_pos (p2_one_minus q) Hq1)))
                 (p2_one_minus q) q).
        -- apply (real_eq_trans
                     (real_mult (p2_one_minus q)
                                (real_mult q (real_inv_pos q Hq)))
                     (real_mult (p2_one_minus q) real_one)
                     (p2_one_minus q)).
        ++ apply (RealSetoid.real_eq_mult_compat (p2_one_minus q)
                     (real_mult q (real_inv_pos q Hq))
                     (p2_one_minus q) real_one).
        ** apply real_eq_refl.
        ** exact (real_inv_pos_correct q Hq).
        ++ apply real_mult_one.
        -- apply (real_eq_trans
                     (real_mult q
                        (real_mult (p2_one_minus q)
                                   (real_inv_pos (p2_one_minus q) Hq1)))
                     (real_mult q real_one)
                     q).
        ++ apply (RealSetoid.real_eq_mult_compat q
                     (real_mult (p2_one_minus q)
                                (real_inv_pos (p2_one_minus q) Hq1))
                     q real_one).
        ** apply real_eq_refl.
        ** exact (real_inv_pos_correct (p2_one_minus q) Hq1).
        ++ apply real_mult_one.
      * p2_ring_eq.
Qed.

(* 件 1a：闭式恒等 div2_cs == (p−q)²·inv(q·(1−q))（纯分配+部分分式） *)
Theorem div2_cs_closed : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (div2_cs p q Hq Hq1)
          (real_mult (p2_tvsq p q)
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
Proof.
  intros p q Hq Hq1 Hqq1.
  unfold div2_cs.
  apply (real_eq_trans
           (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                      (real_mult (p2_tvsq p q)
                                 (real_inv_pos (p2_one_minus q) Hq1)))
           (real_mult (p2_tvsq p q)
              (real_plus (real_inv_pos q Hq)
                         (real_inv_pos (p2_one_minus q) Hq1)))
           (real_mult (p2_tvsq p q)
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
  - apply real_eq_sym. apply real_distrib.
  - apply (RealSetoid.real_eq_mult_compat (p2_tvsq p q)
             (real_plus (real_inv_pos q Hq)
                        (real_inv_pos (p2_one_minus q) Hq1))
             (p2_tvsq p q)
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
    + apply real_eq_refl.
    + apply real_eq_sym. exact (d2_inv_split q Hq Hq1 Hqq1).
Qed.

(* ---- 4. Bishop 缩放主件与件 1b（非负） ---- *)

(* Bishop 形缩放主件：Or 形 a≤b 与 Bishop 形 0≤c 给 c·a ≤_B c·b。
   等支：乘法兼容 + 严格平移；严支：b−a>0，c·(b−a) Bishop 非负，
   以严格项 e 直接实例其逐项余量得 c·(b−a)+e>0，平移换形闭合——
   全程无 Or 形平方非负位、无 c 严性要求。 *)
Lemma d2_scaled_le_b : forall (a b c : Real),
  real_le a b -> real_le_b real_zero c ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hab HC. unfold real_le_b. intros e He.
  destruct Hab as [Hlt | Heq].
  - (* 严支 *)
    assert (Hgpos : real_lt real_zero (real_plus b (real_opp a))).
    { exact (p2_diff_pos_of_lt a b Hlt). }
    assert (HA : real_lt real_zero
                   (real_plus (real_mult c (real_plus b (real_opp a))) e)).
    { apply (RealSetoid.real_lt_id_l real_zero
               (real_mult real_zero (real_plus b (real_opp a)))
               (real_plus (real_mult c (real_plus b (real_opp a))) e)).
      - exact (real_eq_sym
                 (real_mult real_zero (real_plus b (real_opp a))) real_zero
                 (real_eq_trans
                    (real_mult real_zero (real_plus b (real_opp a)))
                    (real_mult (real_plus b (real_opp a)) real_zero)
                    real_zero
                    (real_mult_comm real_zero (real_plus b (real_opp a)))
                    (real_mult_zero (real_plus b (real_opp a))))).
      - exact (leb3_le_b_pos_scale real_zero c (real_plus b (real_opp a))
                 HC Hgpos e He). }
    assert (Heqc : real_eq (real_mult c b)
                   (real_plus (real_mult c a)
                              (real_mult c (real_plus b (real_opp a))))).
    { apply (real_eq_trans (real_mult c b)
               (real_mult c (real_plus a (real_plus b (real_opp a))))
               (real_plus (real_mult c a)
                          (real_mult c (real_plus b (real_opp a))))).
      - apply real_eq_of_zero_diff. intro n0.
        repeat match goal with [ x : Real |- _ ] => destruct x end.
        cbn [projT1 real_plus real_mult real_opp real_one real_zero].
        ring.
      - exact (real_distrib c a (real_plus b (real_opp a))). }
    apply (RealSetoid.real_lt_id_r (real_mult c a)
             (real_plus
                (real_plus (real_mult c a)
                           (real_mult c (real_plus b (real_opp a)))) e)
             (real_plus (real_mult c b) e)).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult c a)
                          (real_mult c (real_plus b (real_opp a))))
               e (real_mult c b) e).
      * exact (real_eq_sym (real_mult c b)
                 (real_plus (real_mult c a)
                            (real_mult c (real_plus b (real_opp a))))
                 Heqc).
      * apply real_eq_refl.
    + apply (RealSetoid.real_lt_id_l (real_mult c a)
               (real_plus (real_mult c a) real_zero)
               (real_plus
                  (real_plus (real_mult c a)
                             (real_mult c (real_plus b (real_opp a)))) e)).
      * exact (real_eq_sym (real_plus (real_mult c a) real_zero)
                 (real_mult c a) (real_plus_zero (real_mult c a))).
      * apply (RealSetoid.real_lt_id_r
                 (real_plus (real_mult c a) real_zero)
                 (real_plus (real_mult c a)
                            (real_plus
                               (real_mult c (real_plus b (real_opp a))) e))
                 (real_plus
                    (real_plus (real_mult c a)
                               (real_mult c (real_plus b (real_opp a)))) e)).
        -- apply real_plus_assoc.
        -- apply (real_lt_plus_translate (real_mult c a) real_zero
                     (real_plus (real_mult c (real_plus b (real_opp a))) e)).
           exact HA.
  - (* 等支：a==b 换形 + 严格平移 *)
    apply (RealSetoid.real_lt_id_l (real_mult c a) (real_mult c b)
             (real_plus (real_mult c b) e)).
    + exact (RealSetoid.real_eq_mult_compat c a c b (real_eq_refl c) Heq).
    + apply (real_lt_plus_r_zero (real_mult c b) e). exact He.
Qed.

(* 件 1b：χ² 载件 Bishop 形非负——平方非负完成件逐项缩放后求和 *)
Theorem div2_cs_nonneg : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b real_zero (div2_cs p q Hq Hq1).
Proof.
  intros p q Hq Hq1.
  assert (HD : real_le_b real_zero (p2_tvsq p q)).
  { exact (real_square_nonneg_B (p2_diff p q)). }
  assert (HT1 : real_le_b real_zero
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
  { apply (leb3_le_b_eq_l (real_mult real_zero (real_inv_pos q Hq))
             real_zero (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
    - exact (real_eq_trans
               (real_mult real_zero (real_inv_pos q Hq))
               (real_mult (real_inv_pos q Hq) real_zero)
               real_zero
               (real_mult_comm real_zero (real_inv_pos q Hq))
               (real_mult_zero (real_inv_pos q Hq))).
    - apply (leb3_le_b_pos_scale real_zero (p2_tvsq p q)
               (real_inv_pos q Hq) HD (real_inv_pos_pos q Hq)). }
  assert (HT2 : real_le_b real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))).
  { apply (leb3_le_b_eq_l
             (real_mult real_zero (real_inv_pos (p2_one_minus q) Hq1))
             real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))).
    - exact (real_eq_trans
               (real_mult real_zero (real_inv_pos (p2_one_minus q) Hq1))
               (real_mult (real_inv_pos (p2_one_minus q) Hq1) real_zero)
               real_zero
               (real_mult_comm real_zero
                  (real_inv_pos (p2_one_minus q) Hq1))
               (real_mult_zero (real_inv_pos (p2_one_minus q) Hq1))).
    - apply (leb3_le_b_pos_scale real_zero (p2_tvsq p q)
               (real_inv_pos (p2_one_minus q) Hq1) HD
               (real_inv_pos_pos (p2_one_minus q) Hq1)). }
  apply (leb3_le_b_eq_l (real_plus real_zero real_zero) real_zero
           (div2_cs p q Hq Hq1)).
  - apply real_plus_zero.
  - exact (real_le_b_plus_compat real_zero
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
             real_zero
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (p2_one_minus q) Hq1))
             HT1 HT2).
Qed.

(* ---- 5. 件 1c：无条件下臂 四·TV² ≤_B χ² ---- *)

(* 本件纯多项式恒等消解（含 d2 常数展开） *)
Ltac d2_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  cbn [projT1 p2_diff p2_one_minus p2_tvsq d2_two d2_four
       real_plus real_mult real_opp real_one real_zero];
  ring.

(* Bishop 右加件：x ≤_B y 且 0 ≤_B z 给 x ≤_B y+z
   （real_le_b_plus_compat 与零右加换形；z 取 Bishop 形以容平方项） *)
Lemma d2_le_b_add_r : forall (x y z : Real),
  real_le_b x y -> real_le_b real_zero z ->
  real_le_b x (real_plus y z).
Proof.
  intros x y z H HZ.
  apply (leb3_le_b_eq_l (real_plus x real_zero) x (real_plus y z)).
  - apply real_plus_zero.
  - exact (real_le_b_plus_compat x y real_zero z H HZ).
Qed.

(* 右分配：((x)+(y))·z == x·z + y·z（comm-distrib-comm 链） *)
Lemma d2_left_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z)
          (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z.
  apply (real_eq_trans (real_mult (real_plus x y) z)
                       (real_mult z (real_plus x y))
                       (real_plus (real_mult x z) (real_mult y z))).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult z (real_plus x y))
                         (real_plus (real_mult z x) (real_mult z y))
                         (real_plus (real_mult x z) (real_mult y z))).
    + apply real_distrib.
    + apply (RealSetoid.real_eq_plus_compat (real_mult z x)
               (real_mult z y) (real_mult x z) (real_mult y z)).
      * apply real_mult_comm.
      * apply real_mult_comm.
Qed.

(* 关键代数恒等：(p−q)² == (q·(1−q))·四·(p−q)² + ((p−q)·(贰q−壹))²
   （纯多项式逐点恒等，即 (贰q−壹)² == 壹−四·q·(壹−q) 的平方重排） *)
Lemma d2_split_core : forall p q : Real,
  real_eq (p2_tvsq p q)
          (real_plus
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_mult
                (real_mult (p2_diff p q)
                           (real_plus (real_plus q q) (real_opp real_one)))
                (real_mult (p2_diff p q)
                           (real_plus (real_plus q q)
                                      (real_opp real_one))))).
Proof.
  intros p q. d2_ring_eq.
Qed.

(* 四倍消去件：(qq1·四·D)·inv(qq1) == 四·D（环重排 + inv 右消去） *)
Lemma d2_quad_scale : forall (p q : Real)
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_eq (real_mult
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
          (real_mult d2_four (p2_tvsq p q)).
Proof.
  intros p q Hqq1.
  apply (real_eq_trans
           (real_mult
              (real_mult
                 (real_mult (real_mult q (p2_one_minus q)) d2_four)
                 (p2_tvsq p q))
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
           (real_mult
              (real_mult (real_mult d2_four (p2_tvsq p q))
                         (real_mult q (p2_one_minus q)))
              (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
           (real_mult d2_four (p2_tvsq p q))).
  - apply (RealSetoid.real_eq_mult_compat
             (real_mult
                (real_mult (real_mult q (p2_one_minus q)) d2_four)
                (p2_tvsq p q))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
             (real_mult (real_mult d2_four (p2_tvsq p q))
                        (real_mult q (p2_one_minus q)))
             (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
    + apply real_eq_of_zero_diff. intro n0.
      repeat match goal with [ x : Real |- _ ] => destruct x end.
      cbn [projT1 p2_diff p2_one_minus p2_tvsq d2_two d2_four
           real_plus real_mult real_opp real_one real_zero].
      ring.
    + apply real_eq_refl.
  - exact (d2_mult_inv_r
             (real_mult d2_four (p2_tvsq p q))
             (real_mult q (p2_one_minus q)) Hqq1).
Qed.

(* 件 1c：无条件下臂 四·TV² ≤_B χ²。
   路线：闭式恒等 + 平方重排核 d2_split_core（(贰q−壹)² == 壹−四·qq1）
   给 χ² == 四·D + ((p−q)·(贰q−壹))²·inv(qq1)，余项为平方项乘严格正
   inv 的 Bishop 非负项，右加闭合——零 log、零分支、零 Or 形平方位。 *)
Theorem div2_cs_ge_four_tvsq : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hqq1 : real_lt real_zero (real_mult q (p2_one_minus q))),
  real_le_b (real_mult d2_four (p2_tvsq p q)) (div2_cs p q Hq Hq1).
Proof.
  intros p q Hq Hq1 Hqq1.
  assert (HEQ : real_eq (div2_cs p q Hq Hq1)
                   (real_plus (real_mult d2_four (p2_tvsq p q))
                              (real_mult
                                 (real_mult
                                    (real_mult (p2_diff p q)
                                               (real_plus (real_plus q q)
                                                          (real_opp real_one)))
                                    (real_mult (p2_diff p q)
                                               (real_plus (real_plus q q)
                                                          (real_opp real_one))))
                                 (real_inv_pos (real_mult q (p2_one_minus q))
                                               Hqq1)))).
  { apply (real_eq_trans (div2_cs p q Hq Hq1)
             (real_mult (p2_tvsq p q)
                        (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
             (real_plus (real_mult d2_four (p2_tvsq p q))
                        (real_mult
                           (real_mult
                              (real_mult (p2_diff p q)
                                         (real_plus (real_plus q q)
                                                    (real_opp real_one)))
                              (real_mult (p2_diff p q)
                                         (real_plus (real_plus q q)
                                                    (real_opp real_one))))
                           (real_inv_pos (real_mult q (p2_one_minus q))
                                         Hqq1)))).
    - exact (div2_cs_closed p q Hq Hq1 Hqq1).
    - apply (real_eq_trans
               (real_mult (p2_tvsq p q)
                          (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult
                  (real_plus
                     (real_mult
                        (real_mult (real_mult q (p2_one_minus q)) d2_four)
                        (p2_tvsq p q))
                     (real_mult
                        (real_mult (p2_diff p q)
                                   (real_plus (real_plus q q)
                                              (real_opp real_one)))
                        (real_mult (p2_diff p q)
                                   (real_plus (real_plus q q)
                                              (real_opp real_one)))))
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_plus (real_mult d2_four (p2_tvsq p q))
                          (real_mult
                             (real_mult
                                (real_mult (p2_diff p q)
                                           (real_plus (real_plus q q)
                                                      (real_opp real_one)))
                                (real_mult (p2_diff p q)
                                           (real_plus (real_plus q q)
                                                      (real_opp real_one))))
                             (real_inv_pos (real_mult q (p2_one_minus q))
                                           Hqq1)))).
      + apply (RealSetoid.real_eq_mult_compat (p2_tvsq p q)
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                 (real_plus
                    (real_mult
                       (real_mult (real_mult q (p2_one_minus q)) d2_four)
                       (p2_tvsq p q))
                    (real_mult
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
        * apply (d2_split_core p q).
        * apply real_eq_refl.
      + apply (real_eq_trans
                 (real_mult
                    (real_plus
                       (real_mult
                          (real_mult (real_mult q (p2_one_minus q)) d2_four)
                          (p2_tvsq p q))
                       (real_mult
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))))
                    (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                 (real_plus
                    (real_mult
                       (real_mult
                          (real_mult (real_mult q (p2_one_minus q)) d2_four)
                          (p2_tvsq p q))
                       (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                    (real_mult
                       (real_mult
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one)))
                          (real_mult (p2_diff p q)
                                     (real_plus (real_plus q q)
                                                (real_opp real_one))))
                       (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)))
                 (real_plus (real_mult d2_four (p2_tvsq p q))
                            (real_mult
                               (real_mult
                                  (real_mult (p2_diff p q)
                                             (real_plus (real_plus q q)
                                                        (real_opp real_one)))
                                  (real_mult (p2_diff p q)
                                             (real_plus (real_plus q q)
                                                        (real_opp real_one))))
                               (real_inv_pos (real_mult q (p2_one_minus q))
                                             Hqq1)))).
        * exact (d2_left_distrib_r
                   (real_mult
                      (real_mult (real_mult q (p2_one_minus q)) d2_four)
                      (p2_tvsq p q))
                   (real_mult
                      (real_mult (p2_diff p q)
                                 (real_plus (real_plus q q)
                                            (real_opp real_one)))
                      (real_mult (p2_diff p q)
                                 (real_plus (real_plus q q)
                                            (real_opp real_one))))
                   (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult
                      (real_mult
                         (real_mult (real_mult q (p2_one_minus q)) d2_four)
                         (p2_tvsq p q))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                   (real_mult
                      (real_mult
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one)))
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one))))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
                   (real_mult d2_four (p2_tvsq p q))
                   (real_mult
                      (real_mult
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one)))
                         (real_mult (p2_diff p q)
                                    (real_plus (real_plus q q)
                                               (real_opp real_one))))
                      (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
          -- exact (d2_quad_scale p q Hqq1).
          -- apply real_eq_refl. }
  assert (HR : real_le_b real_zero
                 (real_mult
                    (real_mult
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one)))
                       (real_mult (p2_diff p q)
                                  (real_plus (real_plus q q)
                                             (real_opp real_one))))
                    (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
  { apply (leb3_le_b_eq_l
             (real_mult real_zero
                (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
             real_zero
             (real_mult
                (real_mult
                   (real_mult (p2_diff p q)
                              (real_plus (real_plus q q)
                                         (real_opp real_one)))
                   (real_mult (p2_diff p q)
                              (real_plus (real_plus q q)
                                         (real_opp real_one))))
                (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
    - exact (real_eq_trans
               (real_mult real_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                          real_zero)
               real_zero
               (real_mult_comm real_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
               (real_mult_zero
                  (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))).
    - exact (leb3_le_b_pos_scale real_zero
                 (real_mult
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one)))
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)
                 (real_square_nonneg_B
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos_pos (real_mult q (p2_one_minus q)) Hqq1)). }
  exact (leb3_le_b_eq_r (real_mult d2_four (p2_tvsq p q))
           (real_plus (real_mult d2_four (p2_tvsq p q))
                      (real_mult
                         (real_mult
                            (real_mult (p2_diff p q)
                                       (real_plus (real_plus q q)
                                                  (real_opp real_one)))
                            (real_mult (p2_diff p q)
                                       (real_plus (real_plus q q)
                                                  (real_opp real_one))))
                         (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1)))
           (div2_cs p q Hq Hq1)
           (d2_le_b_add_r (real_mult d2_four (p2_tvsq p q))
              (real_mult d2_four (p2_tvsq p q))
              (real_mult
                 (real_mult
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one)))
                    (real_mult (p2_diff p q)
                               (real_plus (real_plus q q)
                                          (real_opp real_one))))
                 (real_inv_pos (real_mult q (p2_one_minus q)) Hqq1))
              (leb3_le_b_refl (real_mult d2_four (p2_tvsq p q))) HR)
           (real_eq_sym (div2_cs p q Hq Hq1)
              (real_plus (real_mult d2_four (p2_tvsq p q))
                         (real_mult
                            (real_mult
                               (real_mult (p2_diff p q)
                                          (real_plus (real_plus q q)
                                                     (real_opp real_one)))
                               (real_mult (p2_diff p q)
                                          (real_plus (real_plus q q)
                                                     (real_opp real_one))))
                            (real_inv_pos (real_mult q (p2_one_minus q))
                                          Hqq1)))
              HEQ)).
Qed.

(* ---- 6. 件 1d：条件上臂 χ² ≤_B 二·TV²/m ---- *)

(* inv 反序（Or 形 le 出口）：0<a、0<b、a≤b 给 inv(b) ≤ inv(a)。
   严支取 inv 反单调在役件；等支以 b 为公共乘子用 inv 唯一性闭合。 *)
Lemma d2_inv_antitone_le : forall (a b : Real)
  (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_le a b -> real_le (real_inv_pos b Hb) (real_inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab. unfold real_le in Hab.
  destruct Hab as [Hlt | Heq].
  - left. exact (real_inv_pos_lt_contra a b Ha Hb Hlt).
  - right.
    apply (real_inv_unique b (real_inv_pos b Hb) (real_inv_pos a Ha)).
    + apply real_inv_pos_correct.
    + apply (real_eq_trans (real_mult b (real_inv_pos a Ha))
                           (real_mult a (real_inv_pos a Ha))
                           real_one).
      * exact (RealSetoid.real_eq_mult_compat b (real_inv_pos a Ha) a
                 (real_inv_pos a Ha)
                 (real_eq_sym a b Heq) (real_eq_refl (real_inv_pos a Ha))).
      * exact (real_inv_pos_correct a Ha).
Qed.

(* 件 1d：条件上臂 m≤q ∧ m≤(1−q) ∧ 0<m 给 χ² ≤_B 二·TV²/m。
   路线：inv 反序两支 + Bishop 缩放主件逐项闭合后求和，右端以倍加
   恒等换形至二·(D·inv m)——零 log、零分支、零 Or 形平方位。 *)
Theorem div2_cs_le_tvsq_over_m : forall (p q m : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hm : real_lt real_zero m)
  (Hmq : real_le m q) (Hmq1 : real_le m (p2_one_minus q)),
  real_le_b (div2_cs p q Hq Hq1)
            (real_mult d2_two
               (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
Proof.
  intros p q m Hq Hq1 Hm Hmq Hmq1.
  assert (HC : real_le_b real_zero (p2_tvsq p q)).
  { exact (real_square_nonneg_B (p2_diff p q)). }
  assert (Hleq : real_le (real_inv_pos q Hq) (real_inv_pos m Hm)).
  { exact (d2_inv_antitone_le m q Hm Hq Hmq). }
  assert (Hleq1 : real_le (real_inv_pos (p2_one_minus q) Hq1)
                          (real_inv_pos m Hm)).
  { exact (d2_inv_antitone_le m (p2_one_minus q) Hm Hq1 Hmq1). }
  assert (T1 : real_le_b
                 (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                 (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
  { exact (d2_scaled_le_b (real_inv_pos q Hq) (real_inv_pos m Hm)
             (p2_tvsq p q) Hleq HC). }
  assert (T2 : real_le_b
                 (real_mult (p2_tvsq p q)
                            (real_inv_pos (p2_one_minus q) Hq1))
                 (real_mult (p2_tvsq p q) (real_inv_pos m Hm))).
  { exact (d2_scaled_le_b (real_inv_pos (p2_one_minus q) Hq1)
             (real_inv_pos m Hm) (p2_tvsq p q) Hleq1 HC). }
  apply (leb3_le_b_eq_l
           (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                      (real_mult (p2_tvsq p q)
                                 (real_inv_pos (p2_one_minus q) Hq1)))
           (div2_cs p q Hq Hq1)
           (real_mult d2_two
              (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).
  - apply real_eq_refl.
  - exact (leb3_le_b_eq_r
             (real_plus (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                        (real_mult (p2_tvsq p q)
                                   (real_inv_pos (p2_one_minus q) Hq1)))
             (real_plus (real_mult (p2_tvsq p q) (real_inv_pos m Hm))
                        (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))
             (real_mult d2_two
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))
             (real_le_b_plus_compat
                (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm))
                (real_mult (p2_tvsq p q)
                           (real_inv_pos (p2_one_minus q) Hq1))
                (real_mult (p2_tvsq p q) (real_inv_pos m Hm)) T1 T2)
             (d2_double (real_mult (p2_tvsq p q) (real_inv_pos m Hm)))).
Qed.

(* ---- 7. Q 层闭式档（件 1e 第一期：恒等与非负，零分析层） ---- *)

(* Q 层 χ² 闭式：(p−q)²·inv(q·(1−q))——纯有理式，零 log 零极限 *)
Definition cs2q (p q : Q) : Q := (p - q) * (p - q) * / (q * (1 - q)).

(* 件 1e-i：Q 层逐项闭式恒等 cs2q == (p−q)²·inv(q) + (p−q)²·inv(1−q)
   （域消解 field 一跳，分母非零证书显式随行） *)
Theorem cs2q_split : forall p q : Q,
  (q == 0 -> False) -> ((1 - q)%Q == 0 -> False) ->
  cs2q p q == (p - q) * (p - q) * (/ q)
            + (p - q) * (p - q) * (/ (1 - q))%Q.
Proof.
  intros p q Hq Hq1. unfold cs2q.
  field.
  split.
  - exact Hq1.
  - exact Hq.
Qed.

(* 件 1e-ii：Q 层非负——平方非负在册件乘以正 inv 保序直取 *)
Theorem cs2q_nonneg : forall p q : Q,
  Qlt 0 (q * (1 - q)) -> Qle 0 (cs2q p q).
Proof.
  intros p q Hmass. unfold cs2q.
  apply Qmult_le_0_compat.
  - exact (Qsquare_nonneg (p - q)).
  - exact (Qlt_le_weak _ _ (Qinv_lt_0_compat (q * (1 - q)) Hmass)).
Qed.

(* ---- 99. 尾检 ---- *)
Print Assumptions div2_cs_closed.
Print Assumptions div2_cs_nonneg.
Print Assumptions div2_cs_ge_four_tvsq.
Print Assumptions div2_cs_le_tvsq_over_m.
Print Assumptions cs2q_split.
Print Assumptions cs2q_nonneg.
