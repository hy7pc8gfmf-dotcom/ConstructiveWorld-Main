(* ============================================================ *)
(* WeakTriangleClose.v — 席位 CZH13（批次 E-STAGING-CZH13）      *)
(* T61b C6 收口件：UpReqWeakTriangle G3 CS 权渡真形（挂账实形：  *)
(*   UpReqWeakTriangle.v:28-29 注释位「G3 CS 权渡形/unique-max    *)
(*   特例：挂账（需 Real 平方族引擎）」——槽位为纯注释挂账，无    *)
(*   逐字 .v 语句；EXPD3 报告已离树（attn 仅 _taa7_bak），故按    *)
(*   任务书授权取「(Σab)² ≤ Σa²·Σb² 库内对应形」二元 Gram 核      *)
(*   定向，如实登记选择。                                        *)
(*                                                               *)
(* 【引擎链（全只读消费，签名逐一实读核验）】                     *)
(*   Q 层：Stdlib QArith/Qring——Qmult_le_0_compat / Qplus_le_     *)
(*   compat / Qle_trans / Qle_refl / Qle_bool_iff / Qnot_le_lt /  *)
(*   Qopp_le_compat / Qlt_le_weak + Qring 的 ring（真证 tactic，  *)
(*   Qeq setoid）；real 层：S01_BaseRing 字段与全局件——distrib   *)
(*   （S01:150）/mult_comm/assoc/zero、plus_comm/assoc/zero/opp、 *)
(*   opp_mult_r（S01:399）/opp_mult_l（S01:413）、le_refl/le_id_l/*)
(*   le_id_r/le_trans/le_plus_compat、le_mult_compat_weak、       *)
(*   plus_inv_unique、fa53_compat_abs 的 DO 三分投影定式           *)
(*   （fa53_lt_dec：Id 中腿三分，wtc_sq_nonneg 负支消费）。        *)
(*                                                               *)
(* 【倒墙定格（候闸登记）】T61b 建议的 AbsSqClose（asc_ 平方/abs  *)
(*   族）消费路线在本席窗口倒墙：AbsSqClose Require 链经          *)
(*   TempSoftmaxInstantiation/UpReqSumD 指向聚合件                *)
(*   CW_ConstructiveWorld_219（= S01..S10 全链 Export），vo_901   *)
(*   新纪元正本 57/256 缺 S05+/TSI/SumD 座；侧编试探四件全断       *)
(*   （S07 缺 S05_AlignmentGRPO、TSI/SumD 缺 219、AbsSqClose 缺    *)
(*   TSI，日志 /tmp/czh13_side/log_*.txt 四份定格）；全链自编 =    *)
(*   自建基座，触信任缓存红线禁。故平方非负引擎按 AbsSqClose #42  *)
(*   （asc_sq_nonneg）与其环小件（asc_opp_opp/asc_sq_opp）逐件    *)
(*   同型在 DO 强化层以 wtc_ 前缀自证为候闸换装形（零语句弱化；   *)
(*   候闸后可逐件 exact 换装 asc_ 件）。                          *)
(*                                                               *)
(* 【四要素逐件核销宣言】                                        *)
(*   G1①  wtc_qle_of_qeq       Q 层 Qeq→Qle 换装    [机械运河]    *)
(*   G1①  wtc_q_sq_nonneg     Q 层平方非负          [非平凡低]    *)
(*   G1②  wtc_cs2_q            Q 层二元 CS 核        [非平凡中]    *)
(*   G1①  wtc_sq4/sq_plus/plus4/opp_opp/K1/K2/sq_opp              *)
(*                             real 层环运河模板族 [运河+对合小件] *)
(*   G1③  wtc_sq_nonneg       real 平方非负（asc 换装形）[非平凡中] *)
(*   G2    wtc_gram_id         Gram 恒等式（八项展开 K 双消）       *)
(*                                                [非平凡高]     *)
(*   G2    wtc_cs2_real        real 层二元 CS 装载    [非平凡中]    *)
(*   G2    wtc_weak_triangle_load 主收口定理（库内诚实变体直给形）  *)
(*   G2    wtc_family          sigT 两级封口账       [装配]        *)
(*                                                               *)
(* 纪律：主收口语句面全 Set 层（le/Id 载 Set；Q 层引擎级 Qle 载    *)
(*   Prop 与库内 wtl_ 件 Qlt 前提位同口径先例，主账 real 腿全     *)
(*   Set）；零 公理/承认件/弃证/Hypothesis；文尾 Print        *)
(*   Assumptions 审计。wtc_ 前缀全库零撞名（与 CZG13 席           *)
(*   EngelWeighted 加权 sum 路线零交叠：本席无加权 sum 件）。      *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring.
Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ================================================================ *)
(* Q 层引擎（第一级：Q 平方族 + 二元 CS 核）                          *)
(* ================================================================ *)

(* ---- Qeq→Qle 换装：Qeq/Qle 均展开 Z 层（Qnum 交叉积），Z.le_refl。 *)
Lemma wtc_qle_of_qeq : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. unfold Qle, Qeq in *.
  rewrite H. apply Z.le_refl.
Qed.

(* ---- Q 平方非负（AbsSqClose #42 asc_sq_nonneg 的 Q 层同型）：      *)
(*      Qle_bool 三分 0?q——正支 Qmult_le_0_compat 直给；负支          *)
(*      Qnot_le_lt 翻严格 + Qopp_le_compat 升 le，(−q)²==q² ring      *)
(*      换装 + Qle_trans。 ---- *)
Lemma wtc_q_sq_nonneg : forall q : Q, 0 <= q * q.
Proof.
  intro q.
  destruct (Qle_bool 0 q) eqn:E.
  - apply (proj1 (Qle_bool_iff 0 q)) in E.
    exact (Qmult_le_0_compat q q E E).
  - assert (Hne : ~ 0 <= q).
    { intro Hle. apply (proj2 (Qle_bool_iff 0 q)) in Hle.
      rewrite E in Hle. discriminate Hle. }
    assert (Hneg : q < 0) by (exact (Qnot_le_lt 0 q Hne)).
    assert (Hop : 0 <= - q).
    { exact (Qopp_le_compat q 0 (Qlt_le_weak q 0 Hneg)). }
    assert (Hpos : 0 <= - q * - q) by (exact (Qmult_le_0_compat (- q) (- q) Hop Hop)).
    apply (Qle_trans 0 (- q * - q) (q * q) Hpos).
    apply wtc_qle_of_qeq. ring.
Qed.

(* ---- Q 层二元 CS 核（挂账「Σa²·Σb² ≥ (Σab)²」Q 引擎级）：          *)
(*      Lagrange 二元恒等式 (a²+b²)(c²+d²) == (ac+bd)²+(ad−bc)²       *)
(*      ring 一击展开，平方非负双腿 + 加法保序收口。 ---- *)
Theorem wtc_cs2_q : forall a b c d : Q,
  (a * c + b * d) * (a * c + b * d) <= (a * a + b * b) * (c * c + d * d).
Proof.
  intros a b c d.
  assert (HT := wtc_q_sq_nonneg (a * d - b * c)).
  apply (Qle_trans ((a * c + b * d) * (a * c + b * d))
                   ((a * c + b * d) * (a * c + b * d)
                    + (a * d - b * c) * (a * d - b * c))
                   ((a * a + b * b) * (c * c + d * d))).
  - apply (Qle_trans ((a * c + b * d) * (a * c + b * d))
                     ((a * c + b * d) * (a * c + b * d) + 0)
                     ((a * c + b * d) * (a * c + b * d)
                      + (a * d - b * c) * (a * d - b * c))).
    + apply wtc_qle_of_qeq. ring.
    + apply Qplus_le_compat. apply Qle_refl. exact HT.
  - apply wtc_qle_of_qeq. ring.
Qed.

(* ================================================================ *)
(* real 层装载（第二级：S01 载体 Gram 展开 + 平方非负直收）            *)
(* ================================================================ *)

Section WeakTriangleLoad.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* fa53 投影别名定式：类字段名 lt_dec 被 Stdlib Compare_dec 遮蔽       *)
(* （fa53/AbsSqClose 同款 match 投影）。 ---- *)
Definition wtc_lt_dec_id :
  forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ---- 运河模板①：(x·y)(x·y) == (x·x)(y·y)（assoc/comm 五步，        *)
(*      ac/ad/bd/bc 四项平方归位复用）。 ---- *)
Lemma wtc_sq4 : forall x y : R,
  Id (mult (mult x y) (mult x y)) (mult (mult x x) (mult y y)).
Proof.
  intros x y.
    exact (id_trans (id_sym (mult_assoc x y (mult x y)))
           (id_trans (id_cong (fun w => mult x w) (mult_assoc y x y))
             (id_trans (id_cong (fun w => mult x (mult w y)) (mult_comm y x))
               (id_trans (id_cong (fun w => mult x w) (id_sym (mult_assoc x y y)))
                         (mult_assoc x x (mult y y)))))).
Qed.

(* ---- 运河模板②：(u+v)² 展开前段（distrib 双段运河）。 ---- *)
Lemma wtc_sq_plus : forall u v : R,
  Id (mult (plus u v) (plus u v))
     (plus (plus (mult u u) (mult v u)) (plus (mult u v) (mult v v))).
Proof.
  intros u v.
  exact (id_trans (distrib (plus u v) u v)
           (id_trans (id_cong (fun w => plus w (mult (plus u v) v))
                              (mult_plus_distr_r u v u))
                     (id_cong (fun w => plus (plus (mult u u) (mult v u)) w)
                              (mult_plus_distr_r u v v)))).
Qed.

(* ---- 运河模板③：四项和交换 plus(A+B)+(C+D) == plus(A+C)+(B+D)。 *)
Lemma wtc_plus4 : forall A B C D : R,
  Id (plus (plus A B) (plus C D)) (plus (plus A C) (plus B D)).
Proof.
  intros A B C D.
  exact (id_trans (id_sym (plus_assoc A B (plus C D)))
           (id_trans (id_cong (fun w => plus A w) (plus_assoc B C D))
             (id_trans (id_cong (fun w => plus A (plus w D)) (plus_comm B C))
               (id_trans (id_cong (fun w => plus A w) (id_sym (plus_assoc C B D)))
                         (plus_assoc A C (plus B D)))))).
Qed.

(* ---- 运河模板④：opp 对合 −−a == a（AbsSqClose asc_opp_opp          *)
(*      候闸换装形：plus_inv_unique 两侧右逆对齐）。 ---- *)
Lemma wtc_opp_opp : forall a : R, Id (opp (opp a)) a.
Proof.
  intro a.
  exact (plus_inv_unique (opp a) (opp (opp a)) a
           (plus_opp (opp a))
           (id_trans (id_sym (plus_comm a (opp a))) (plus_opp a))).
Qed.

(* ---- 运河模板⑤：(−t)² == t²（AbsSqClose asc_sq_opp 候闸换装形：    *)
(*      opp_mult_r/l 移 opp + opp 对合收尾）。 ---- *)
Lemma wtc_sq_opp : forall t : R, Id (mult t t) (mult (opp t) (opp t)).
Proof.
  intro t.
  exact (id_sym (id_trans (opp_mult_r t (opp t))
                  (id_trans (id_cong opp (opp_mult_l t t))
                            (wtc_opp_opp (mult t t))))).
Qed.

(* ---- 运河模板⑥：K 统一形换装——(a·c)(b·d) == (a·b)(c·d)            *)
(*      （assoc/comm 五步；bd·ac、bc·ad 由 comm 一击先归此形）。 ---- *)
Lemma wtc_K1 : forall a b c d : R,
  Id (mult (mult a c) (mult b d)) (mult (mult a b) (mult c d)).
Proof.
  intros a b c d.
  exact (id_trans (id_sym (mult_assoc a c (mult b d)))
           (id_trans (id_cong (fun w => mult a w) (mult_assoc c b d))
             (id_trans (id_cong (fun w => mult a (mult w d)) (mult_comm c b))
               (id_trans (id_cong (fun w => mult a w) (id_sym (mult_assoc b c d)))
                         (mult_assoc a b (mult c d)))))).
Qed.

(* ---- 运河模板⑦：(a·d)(b·c) == K 形（同款五步）。 ---- *)
Lemma wtc_K2 : forall a b c d : R,
  Id (mult (mult a d) (mult b c)) (mult (mult a b) (mult c d)).
Proof.
  intros a b c d.
  assert (H1 : Id (mult (mult a d) (mult b c)) (mult a (mult d (mult b c)))).
  { exact (id_sym (mult_assoc a d (mult b c))). }
  assert (H2 : Id (mult a (mult d (mult b c))) (mult a (mult (mult d b) c))).
  { exact (id_cong (fun w => mult a w) (mult_assoc d b c)). }
  assert (H3 : Id (mult a (mult (mult d b) c)) (mult a (mult (mult b d) c))).
  { exact (id_cong (fun w => mult a (mult w c)) (mult_comm d b)). }
  assert (H4 : Id (mult a (mult (mult b d) c)) (mult a (mult b (mult d c)))).
  { exact (id_cong (fun w => mult a w) (id_sym (mult_assoc b d c))). }
  assert (H5 : Id (mult a (mult b (mult d c))) (mult a (mult b (mult c d)))).
  { exact (id_cong (fun w => mult a (mult b w)) (mult_comm d c)). }
  assert (H6 : Id (mult a (mult b (mult c d))) (mult (mult a b) (mult c d))).
  { exact (mult_assoc a b (mult c d)). }
  exact (id_trans H1 (id_trans H2 (id_trans H3 (id_trans H4 (id_trans H5 H6))))).
Qed.

(* ---- G1③：real 平方非负（AbsSqClose #42 asc_sq_nonneg 候闸换装形，  *)
(*      逐件同型三分：正支零乘链 + le_mult_compat_weak；零支平方归零；  *)
(*      负支 −t>0 支 + (−t)²==t² 环换装。 ---- *)
Theorem wtc_sq_nonneg : forall t : R, le zero (mult t t).
Proof.
  intro t.
  destruct (wtc_lt_dec_id zero t) as [H0t | [H0eq | Htl]].
  - (* 0 < t：0·t == 0 链 + 双 le zero t 弱乘单调 *)
    assert (Hge : le zero t) by (exact (lt_le_iff zero t (inl H0t))).
    exact (le_id_l zero (mult zero t) (mult t t)
             (id_sym (id_trans (mult_comm zero t) (mult_zero t)))
             (le_mult_compat_weak zero t t Hge Hge)).
  - (* 0 == t：t² == 0² == 0 *)
    assert (Htz : Id (mult t t) zero).
    { exact (id_trans (id_cong (fun w => mult w t) (id_sym H0eq))
                      (id_trans (mult_comm zero t) (mult_zero t))). }
    exact (le_id_r zero zero (mult t t) (id_sym Htz) (le_refl zero)).
  - (* t < 0：−t > 0 支 + (−t)²==t² 换装 *)
    assert (Ht0 : lt zero (opp t)).
    { exact (lt_id_l zero (opp zero) (opp t)
               (id_sym (plus_inv_unique zero (opp zero) zero
                          (plus_opp zero) (plus_zero zero)))
               (opp_lt_compat t zero Htl)). }
    exact (le_id_r zero (mult (opp t) (opp t)) (mult t t)
             (id_sym (wtc_sq_opp t))
             (le_id_l zero (mult zero (opp t)) (mult (opp t) (opp t))
                (id_sym (id_trans (mult_comm zero (opp t))
                                  (mult_zero (opp t))))
                (le_mult_compat_weak zero (opp t) (opp t)
                   (lt_le_iff zero (opp t) (inl Ht0))
                   (lt_le_iff zero (opp t) (inl Ht0))))).
Qed.

(* ---- G2 主件：Gram 二元恒等式——                                    *)
(*   (a²+b²)(c²+d²) == (ac+bd)² + (ad−bc)²。                          *)
(*   展开账：X 双 distrib 归 P=(s1t1+s2t1)+(s1t2+s2t2)；                *)
(*   m² 四项 s1t1 K K s2t2、n² 四项 s1t2 oppK oppK s2t1；               *)
(*   M+N 经 plus4 双层归位使 K/oppK 相邻，plus_opp 双消 + 零归位。      *)
Theorem wtc_gram_id : forall a b c d : R,
  Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
     (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
           (mult (plus (mult a d) (opp (mult b c)))
                 (plus (mult a d) (opp (mult b c))))).
Proof.
  intros a b c d.
  (* 段 1：X 归 P' =(s1t1+s2t1)+(s1t2+s2t2) *)
  assert (A1 : Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                  (plus (mult (plus (mult a a) (mult b b)) (mult c c))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))).
  { exact (distrib (plus (mult a a) (mult b b)) (mult c c) (mult d d)). }
  assert (A2 : Id (mult (plus (mult a a) (mult b b)) (mult c c))
                  (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))).
  { exact (mult_plus_distr_r (mult a a) (mult b b) (mult c c)). }
  assert (A3 : Id (mult (plus (mult a a) (mult b b)) (mult d d))
                  (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d)))).
  { exact (mult_plus_distr_r (mult a a) (mult b b) (mult d d)). }
  assert (A4 : Id (plus (mult (plus (mult a a) (mult b b)) (mult c c))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))).
  { exact (id_cong (fun w => plus w (mult (plus (mult a a) (mult b b)) (mult d d))) A2). }
  assert (A5 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (mult (plus (mult a a) (mult b b)) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c))) w) A3). }
  assert (H1 : Id (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans A1 (id_trans A4 A5)). }
  (* 段 2：m*2 归 M =(s1t1+K)+(K+s2t2) *)
  assert (B1 : Id (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                  (plus (plus (mult (mult a c) (mult a c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (wtc_sq_plus (mult a c) (mult b d)). }
  assert (B3 : Id (mult (mult b d) (mult a c)) (mult (mult a b) (mult c d))).
  { exact (id_trans (mult_comm (mult b d) (mult a c)) (wtc_K1 a b c d)). }
  assert (B6 : Id (plus (plus (mult (mult a c) (mult a c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus w (mult (mult b d) (mult a c))) (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                   (wtc_sq4 a c)). }
  assert (B7 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b d) (mult a c)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) w) (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                   B3). }
  assert (B8 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a c) (mult b d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b d) (mult b d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))) (plus w (mult (mult b d) (mult b d))))
                   (wtc_K1 a b c d)). }
  assert (B9 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b d) (mult b d))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))) (plus (mult (mult a b) (mult c d)) w))
                   (wtc_sq4 b d)). }
  assert (H2 : Id (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                        (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans B1 (id_trans B6 (id_trans B7 (id_trans B8 B9)))). }
  (* 段 3：n*2 归 N =(s1t2+oppK)+(oppK+s2t1) *)
  assert (C1 : Id (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                  (plus (plus (mult (mult a d) (mult a d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (wtc_sq_plus (mult a d) (opp (mult b c))). }
  assert (C3 : Id (mult (opp (mult b c)) (mult a d)) (opp (mult (mult a b) (mult c d)))).
  { exact (id_trans (opp_mult_r (mult b c) (mult a d))
                    (id_cong opp (id_trans (mult_comm (mult b c) (mult a d)) (wtc_K2 a b c d)))). }
  assert (C4 : Id (mult (mult a d) (opp (mult b c))) (opp (mult (mult a b) (mult c d)))).
  { exact (id_trans (opp_mult_l (mult a d) (mult b c))
                    (id_cong opp (wtc_K2 a b c d))). }
  assert (C5 : Id (mult (opp (mult b c)) (opp (mult b c))) (mult (mult b b) (mult c c))).
  { exact (id_trans (opp_mult_r (mult b c) (opp (mult b c)))
             (id_trans (id_cong opp (opp_mult_l (mult b c) (mult b c)))
               (id_trans (wtc_opp_opp (mult (mult b c) (mult b c)))
                         (wtc_sq4 b c)))). }
  assert (C6 : Id (plus (plus (mult (mult a d) (mult a d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus w (mult (opp (mult b c)) (mult a d))) (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                   (wtc_sq4 a d)). }
  assert (C7 : Id (plus (plus (mult (mult a a) (mult d d)) (mult (opp (mult b c)) (mult a d)))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) w) (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                   C3). }
  assert (C8 : Id (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (mult (mult a d) (opp (mult b c))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (opp (mult b c)) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))) (plus w (mult (opp (mult b c)) (opp (mult b c)))))
                   C4). }
  assert (C9 : Id (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (opp (mult b c)) (opp (mult b c)))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))) (plus (opp (mult (mult a b) (mult c d))) w))
                   C5). }
  assert (H3 : Id (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                  (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                        (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c))))).
  { exact (id_trans C1 (id_trans C6 (id_trans C7 (id_trans C8 C9)))). }
  (* 段 4：M+N 归 P'（plus4 双层 + K/oppK 双消 + 零归位 + comm） *)
  assert (D1 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                              (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (wtc_plus4 (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                     (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                     (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                     (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))). }
  assert (D2 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus w (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                                          (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                   (wtc_plus4 (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d))
                              (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))). }
  assert (D3 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))
                              (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                                        (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))) w)
                   (wtc_plus4 (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))
                              (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))). }
  assert (D4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                              (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d)))))
                        (plus (plus (mult (mult a b) (mult c d)) (opp (mult (mult a b) (mult c d))))
                              (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) zero)
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                                  (plus w (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                   (plus_opp (mult (mult a b) (mult c d)))). }
  assert (D5 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) zero)
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))).
  { exact (id_cong (fun w => plus w (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                   (plus_zero (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))))). }
  assert (D6 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))).
  { exact (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                   (id_trans (plus_comm zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                             (plus_zero (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c)))))). }
  assert (D7 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d)))
                        (plus (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans (id_cong (fun w => plus (plus (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))) w)
                                (plus_comm (mult (mult b b) (mult d d)) (mult (mult b b) (mult c c))))
                   (wtc_plus4 (mult (mult a a) (mult c c)) (mult (mult a a) (mult d d))
                              (mult (mult b b) (mult c c)) (mult (mult b b) (mult d d)))). }
  assert (H4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))).
  { exact (id_trans D1 (id_trans D2 (id_trans D3 (id_trans D4 (id_trans D5 (id_trans D6 D7)))))). }
  (* 主链：X == P'；P' == m2+N（H4 反 + H2 反 cong）；== m2+n2（H3 反 cong） *)
  assert (E1 : Id (plus (plus (mult (mult a a) (mult c c)) (mult (mult b b) (mult c c)))
                        (plus (mult (mult a a) (mult d d)) (mult (mult b b) (mult d d))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                              (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))).
  { exact (id_sym H4). }  assert (E3 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                  (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus w (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                   (id_sym H2)). }
  assert (E4 : Id (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                                   (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                              (plus (plus (mult (mult a a) (mult d d)) (opp (mult (mult a b) (mult c d))))
                                    (plus (opp (mult (mult a b) (mult c d))) (mult (mult b b) (mult c c)))))
                  (plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                             (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d))))
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))).
  { exact (id_cong (fun w => plus (plus (plus (mult (mult a a) (mult c c)) (mult (mult a b) (mult c d)))
                                            (plus (mult (mult a b) (mult c d)) (mult (mult b b) (mult d d)))) w)
                   (id_sym H3)). }
  exact (id_trans H1 (id_trans E1 (id_trans E4 E3))).
Qed.

(* ---- G2：real 层二元 CS 装载——(ac+bd)² ≤ (a²+b²)(c²+d²)。          *)
(*      Gram 恒等式换装 + 平方非负腿 + 加法保序。 ---- *)
Theorem wtc_cs2_real : forall a b c d : R,
  le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
     (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof.
  intros a b c d.
  assert (Hsq := wtc_sq_nonneg (plus (mult a d) (opp (mult b c)))).
  apply (le_id_r (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                       (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                 (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d)))
                 (id_sym (wtc_gram_id a b c d))).
  apply (le_id_l (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d))) zero)
                 (plus (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                       (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c)))))
                 (id_sym (plus_zero (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))))).
  exact (le_plus_compat (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
                        zero
                        (mult (plus (mult a d) (opp (mult b c))) (plus (mult a d) (opp (mult b c))))
                        (le_refl (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d))))
                        Hsq).
Qed.

(* ---- 主收口定理（挂账 :28 库内诚实变体直给形，对账锚定照            *)
(*      fa53_bs_abs_shape 模式）：结论面 = wtc_cs2_real 逐字。 ---- *)
Theorem wtc_weak_triangle_load : forall a b c d : R,
  le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
     (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof.
  exact wtc_cs2_real.
Qed.

(* ---- G2 封口件：wtc 族 sigT 两级账（Q 引擎腿 + real 装载腿，        *)
(*      照 wtl_family 模式）。 ---- *)
Definition wtc_leg_q_cs2 : Type :=
  forall a b c d : Q,
    (a * c + b * d) * (a * c + b * d) <= (a * a + b * b) * (c * c + d * d).

Definition wtc_leg_r_cs2 : Type :=
  forall a b c d : R,
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).

Theorem wtc_family : sigT (fun _ : wtc_leg_q_cs2 => wtc_leg_r_cs2).
Proof.
  exact (existT _ wtc_cs2_q wtc_cs2_real).
Qed.

End WeakTriangleLoad.

(* ---- 审计位（零 magic 检查） ---- *)
Print Assumptions wtc_qle_of_qeq.
Print Assumptions wtc_q_sq_nonneg.
Print Assumptions wtc_cs2_q.
Print Assumptions wtc_sq_nonneg.
Print Assumptions wtc_gram_id.
Print Assumptions wtc_cs2_real.
Print Assumptions wtc_weak_triangle_load.
Print Assumptions wtc_family.
