(* ============================================================ *)
(* abl_div_fdiv2_skeleton.v                                       *)
(* 模块名：abl_div_fdiv2_skeleton                                  *)
(* 数学使命：两点 f-散度 Section 泛型骨架（统摄手法消化件）——不参数化    *)
(*   凸 f 函数本体（W-KLTEMP-01 禁入守约），参数化「基底比值数据+三点 f   *)
(*   显式数据+线性照管差分正性证书」，一个 Section 统摄 χ²/Hellinger/KL   *)
(*   三实例。泛型定理 df2_j_nonneg（J_f ≥ 0，Bishop 形出口）与            *)
(*   df2_j_le_cs（J_f−照管 ≤_B χ²-比值形）；实例核对节（陈述级对照，      *)
(*   实例定理不重证）：χ² 实例（df2_cs_inst==div2_cs）、KL₂ 实例（excess *)
(*   形数据，双面经骨架复现件 2 主件 dkc_kl2_le_cs）、Hellinger 实例      *)
(*   （见证平方形，双面经骨架闭合）；TV 下界=开放申报接口（见尾注）。     *)
(* 依赖清单：S01/S02/S03/S07/S08 基座、PinskerTwoPoint、UpRealLeB/B2/B3、 *)
(*   UpReqTrainingEquiv、G07_KLWall、G08_Gibbs、UpReqPinskerTransport、   *)
(*   件 1 abl_div_chisq_twopoint、件 2 abl_div_kl_chisq_twopoint、        *)
(*   件 3 abl_div_hellinger_twopoint（所用引理随正文引用）。              *)
(* 构造性注记：骨架层=Real 层（三实例口径核实均 Real 层；件 1 Q 面为      *)
(*   附录分期档）；非严格序一律 Bishop 形 real_le_b（零 Or 形平方非负位）；*)
(*   凸性类条件取「线性照管差分正性」可构造形态（禁经典二阶导）：         *)
(*   f ≥ cdown·(u−1) 于两点比值处（Bishop 形证书）；f(1)=0（Hf1）为散度   *)
(*   对角零条件面，不入 df2_j_nonneg 证明体（照管和经归一化对消自动       *)
(*   成立）；三实例照管斜率均取零；inv/log 证书逐点显式穿线；              *)
(*   零承认式语句、零经典公理、全部 Qed 闭合。                            *)
(* 编译配方（四件按序，同池）：                                            *)
(*   source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s     *)
(*   65532 && nice -19 rocq c -native-compiler no -Q <缓存根> ""，依序：   *)
(*   件 1 abl_div_chisq_twopoint → 件 2 abl_div_kl_chisq_twopoint →        *)
(*   件 3 abl_div_hellinger_twopoint → 本件。                              *)
(* ============================================================ *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring QArith.Qfield.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import PinskerTwoPoint.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G07_KLWall.
Require Import G08_Gibbs.
Require Import UpReqTrainingEquiv.
Require Import UpReqPinskerTransport.
Require Import abl_div_chisq_twopoint.
Require Import abl_div_kl_chisq_twopoint.
Require Import abl_div_hellinger_twopoint.

(* 环闭卫生：含 inv/log 内联原子的环闭位一律 remember 化
   （实测判定：cbn 经 projT1 投影 delta-展开其 cauchy 证书机件会令
   ring 拒闭；Opaque 反使 cbn 重折叠空转，弃用） *)

(* ---- 0. 泛型支承件：单位元缩放消去（inv 系，证书 Hu : w·u==1） ---- *)

(* 缩放消去：w·u==1 给 w·(D·u) == D（环原子重排 + compat + mult_one） *)
Lemma df2_unit_scale : forall (w u D : Real),
  real_eq (real_mult w u) real_one ->
  real_eq (real_mult w (real_mult D u)) D.
Proof.
  intros w u D Hu.
  apply (real_eq_trans
           (real_mult w (real_mult D u))
           (real_mult D (real_mult w u))
           D).
  - apply real_eq_of_zero_diff. intro n0.
    repeat match goal with [ x : Real |- _ ] => destruct x end.
    cbn [projT1 real_plus real_mult real_opp real_one real_zero]. ring.
  - apply (real_eq_trans
             (real_mult D (real_mult w u))
             (real_mult D real_one)
             D).
    + apply (RealSetoid.real_eq_mult_compat D (real_mult w u) D real_one
               (real_eq_refl D) Hu).
    + apply real_mult_one.
Qed.

(* 平方缩放消去：w·u==1 给 w·((D·u)·(D·u)) == (D·D)·u *)
Lemma df2_unit_scale_sq : forall (w u D : Real),
  real_eq (real_mult w u) real_one ->
  real_eq (real_mult w (real_mult (real_mult D u) (real_mult D u)))
          (real_mult (real_mult D D) u).
Proof.
  intros w u D Hu.
  apply (real_eq_trans
           (real_mult w (real_mult (real_mult D u) (real_mult D u)))
           (real_mult (real_mult (real_mult D D) u) (real_mult w u))
           (real_mult (real_mult D D) u)).
  - apply real_eq_of_zero_diff. intro n0.
    repeat match goal with [ x : Real |- _ ] => destruct x end.
    cbn [projT1 real_plus real_mult real_opp real_one real_zero]. ring.
  - apply (real_eq_trans
             (real_mult (real_mult (real_mult D D) u) (real_mult w u))
             (real_mult (real_mult (real_mult D D) u) real_one)
             (real_mult (real_mult D D) u)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult (real_mult D D) u) (real_mult w u)
               (real_mult (real_mult D D) u) real_one
               (real_eq_refl (real_mult (real_mult D D) u)) Hu).
    + apply real_mult_one.
Qed.

(* ---- 0.5 照管和零恒等（归一化消耗；节外 4 变量形） ---- *)
(*   AL 勘正吸收：节内 7 Real 变量的 destruct+ring 指数爆炸
   （Timeout 实测判定）——按测试件
   结论改节外泛型件：destruct+ring 只碰 4 变量，Hnorm 经
   RealSetoid 兼容链在环外消耗。 *)

Lemma df2_care_sum_zero : forall (q s s' cdown : Real),
  real_eq (real_plus (real_mult q s) (real_mult (p2_one_minus q) s')) real_one ->
  real_eq (real_plus
             (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
             (real_mult (p2_one_minus q)
                        (real_mult cdown (real_plus s' (real_opp real_one)))))
          real_zero.
Proof.
  intros q s s' cdown Hnorm.
  apply (real_eq_trans
           (real_plus
              (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
              (real_mult (p2_one_minus q)
                         (real_mult cdown (real_plus s' (real_opp real_one)))))
           (real_mult cdown
              (real_plus
                 (real_plus (real_mult q s) (real_mult (p2_one_minus q) s'))
                 (real_opp real_one)))
           real_zero).
  - apply real_eq_of_zero_diff. intro n0.
    repeat match goal with [ x : Real |- _ ] => destruct x end.
    cbn [projT1 p2_one_minus real_plus real_mult real_opp real_one real_zero].
    ring.
  - apply (real_eq_trans
             (real_mult cdown
                (real_plus
                   (real_plus (real_mult q s) (real_mult (p2_one_minus q) s'))
                   (real_opp real_one)))
             (real_mult cdown (real_plus real_one (real_opp real_one)))
             real_zero).
    + apply (RealSetoid.real_eq_mult_compat cdown
               (real_plus
                  (real_plus (real_mult q s) (real_mult (p2_one_minus q) s'))
                  (real_opp real_one))
               cdown
               (real_plus real_one (real_opp real_one))).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_mult q s) (real_mult (p2_one_minus q) s'))
                 (real_opp real_one)
                 real_one (real_opp real_one)).
        -- exact Hnorm.
        -- apply real_eq_refl.
    + apply (real_eq_trans
               (real_mult cdown (real_plus real_one (real_opp real_one)))
               (real_mult cdown real_zero)
               real_zero).
      * apply (RealSetoid.real_eq_mult_compat cdown
                 (real_plus real_one (real_opp real_one)) cdown real_zero
                 (real_eq_refl cdown) (real_plus_opp real_one)).
      * exact (real_mult_zero cdown).
Qed.

(* ============================================================ *)
(* ---- 1. Section FDivTwoPoint：两点 f-散度泛型骨架 ----           *)
(* ============================================================ *)

Section FDivTwoPoint.

(* 承载数据：权重 q 与两比值 s s'（归一化 q·s+(1−q)·s'==1；
   实例位 s := p/q、s' := (1−p)/(1−q) 的抽象化） *)
Variable q s s' : Real.
Variable Hq  : real_lt real_zero q.
Variable Hq1 : real_lt real_zero (p2_one_minus q).
Variable Hs  : real_lt real_zero s.
Variable Hs1 : real_lt real_zero s'.
Variable Hnorm : real_eq (real_plus (real_mult q s)
                                    (real_mult (p2_one_minus q) s'))
                        real_one.

(* f 的三点显式数据（f 函数本体不参数化——W-KLTEMP-01 禁入守约）：
   fa := f(s)、fb := f(s')、f1 := f(1) *)
Variable fa fb f1 : Real.
Variable Hf1 : real_eq f1 real_zero.

(* 凸性类条件·可构造形态：线性照管差分正性（禁经典二阶导）——
   下照管斜率 cdown：cdown·(u−1) ≤_B f(u) 于两点 s s'（Bishop 形） *)
Variable cdown : Real.
Variable Hlow_s  : real_le_b (real_mult cdown (real_plus s (real_opp real_one))) fa.
Variable Hlow_s1 : real_le_b (real_mult cdown (real_plus s' (real_opp real_one))) fb.

(* ---- 1.1 载件定义：两点 f-散度闭式和形 ---- *)

Definition df2_j : Real :=
  real_plus (real_mult q fa) (real_mult (p2_one_minus q) fb).

(* 比值形 χ² 载件（p := q·s 显式代入后的 χ²(P‖Q)，零 inv 形） *)
Definition df2_cs_inst : Real :=
  real_plus (real_mult q (real_mult (real_plus s (real_opp real_one))
                                    (real_plus s (real_opp real_one))))
            (real_mult (p2_one_minus q)
                       (real_mult (real_plus s' (real_opp real_one))
                                  (real_plus s' (real_opp real_one)))).

(* ---- 1.2 泛型定理一（主目标）：J_f ≥ 0 ---- *)
(*   路线：双照管证书按正权 Bishop 缩放求和，照管和重组为
   cdown·(归一化复合 − 1) 后消耗 Hnorm 对消为零——零分支零经典逻辑。 *)

Theorem df2_j_nonneg : real_le_b real_zero df2_j.
Proof.
  assert (T1 : real_le_b
                 (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
                 (real_mult q fa)).
  { exact (leb3_le_b_pos_scale_l
             (real_mult cdown (real_plus s (real_opp real_one))) fa q Hlow_s Hq). }
  assert (T2 : real_le_b
                 (real_mult (p2_one_minus q)
                            (real_mult cdown (real_plus s' (real_opp real_one))))
                 (real_mult (p2_one_minus q) fb)).
  { exact (leb3_le_b_pos_scale_l
             (real_mult cdown (real_plus s' (real_opp real_one))) fb
             (p2_one_minus q) Hlow_s1 Hq1). }
  assert (HS : real_le_b
                 (real_plus
                    (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
                    (real_mult (p2_one_minus q)
                               (real_mult cdown (real_plus s' (real_opp real_one)))))
                 (real_plus (real_mult q fa) (real_mult (p2_one_minus q) fb))).
  { exact (real_le_b_plus_compat
             (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
             (real_mult q fa)
             (real_mult (p2_one_minus q)
                        (real_mult cdown (real_plus s' (real_opp real_one))))
             (real_mult (p2_one_minus q) fb) T1 T2). }
  (* 照管和 == 0：节外泛型件 df2_care_sum_zero 直取（复活续建·AL 勘正
   吸收——节内 7 变量 destruct+ring 指数爆炸，Timeout 实测判定） *)
  assert (HEQ := df2_care_sum_zero q s s' cdown Hnorm).
  exact (leb3_le_b_eq_l
           (real_plus
              (real_mult q (real_mult cdown (real_plus s (real_opp real_one))))
              (real_mult (p2_one_minus q)
                         (real_mult cdown (real_plus s' (real_opp real_one)))))
           real_zero df2_j HEQ HS).
Qed.

(* ---- 1.3 泛型定理二（P 草案 Part A 容器）：超额证书直取 ≤ χ²-比值形 ---- *)
(*   上照管斜率 cup：q·(f 值 − cup·(u−1)) ≤_B q·(u−1)² 逐项证书直取，
   结论一步 plus_compat——件 2 gap 形（dkc_gap_le_term）的泛型容器。 *)

Variable cup : Real.
Variable Hup_s  : real_le_b
                    (real_plus (real_mult q fa)
                               (real_opp (real_mult q
                                            (real_mult cup (real_plus s (real_opp real_one))))))
                    (real_mult q (real_mult (real_plus s (real_opp real_one))
                                            (real_plus s (real_opp real_one)))).
Variable Hup_s1 : real_le_b
                    (real_plus (real_mult (p2_one_minus q) fb)
                               (real_opp (real_mult (p2_one_minus q)
                                                    (real_mult cup (real_plus s' (real_opp real_one))))))
                    (real_mult (p2_one_minus q)
                               (real_mult (real_plus s' (real_opp real_one))
                                          (real_plus s' (real_opp real_one)))).

Theorem df2_j_le_cs :
  real_le_b
    (real_plus
       (real_plus (real_mult q fa)
                  (real_opp (real_mult q
                               (real_mult cup (real_plus s (real_opp real_one))))))
       (real_plus (real_mult (p2_one_minus q) fb)
                  (real_opp (real_mult (p2_one_minus q)
                                       (real_mult cup (real_plus s' (real_opp real_one)))))))
    df2_cs_inst.
Proof.
  exact (real_le_b_plus_compat
           (real_plus (real_mult q fa)
                      (real_opp (real_mult q
                                   (real_mult cup (real_plus s (real_opp real_one))))))
           (real_mult q (real_mult (real_plus s (real_opp real_one))
                                   (real_plus s (real_opp real_one))))
           (real_plus (real_mult (p2_one_minus q) fb)
                      (real_opp (real_mult (p2_one_minus q)
                                           (real_mult cup (real_plus s' (real_opp real_one))))))
           (real_mult (p2_one_minus q)
                      (real_mult (real_plus s' (real_opp real_one))
                                 (real_plus s' (real_opp real_one))))
           Hup_s Hup_s1).
Qed.

End FDivTwoPoint.

(* ============================================================ *)
(* ---- 2. 实例核对节（陈述级对照；实例定理已闭，不重证） ----        *)
(* ============================================================ *)

(* ---- 2.0 归一化恒等的实例化：s := p/q、s' := (1−p)/(1−q) ---- *)

Lemma df2_norm_inst : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (real_plus
             (real_mult q (real_mult p (real_inv_pos q Hq)))
             (real_mult (p2_one_minus q)
                        (real_mult (p2_one_minus p)
                                   (real_inv_pos (p2_one_minus q) Hq1))))
          real_one.
Proof.
  intros p q Hp Hq Hp1 Hq1.
  apply (real_eq_trans
           (real_plus
              (real_mult q (real_mult p (real_inv_pos q Hq)))
              (real_mult (p2_one_minus q)
                         (real_mult (p2_one_minus p)
                                    (real_inv_pos (p2_one_minus q) Hq1))))
           (real_plus p (p2_one_minus p))
           real_one).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult q (real_mult p (real_inv_pos q Hq)))
             (real_mult (p2_one_minus q)
                        (real_mult (p2_one_minus p)
                                   (real_inv_pos (p2_one_minus q) Hq1)))
             p (p2_one_minus p)).
    + exact (df2_unit_scale q (real_inv_pos q Hq) p
               (real_inv_pos_correct q Hq)).
    + exact (df2_unit_scale (p2_one_minus q)
               (real_inv_pos (p2_one_minus q) Hq1) (p2_one_minus p)
               (real_inv_pos_correct (p2_one_minus q) Hq1)).
  - apply real_eq_of_zero_diff. intro n0.
    repeat match goal with [ x : Real |- _ ] => destruct x end.
    cbn [projT1 p2_one_minus real_plus real_mult real_opp real_one real_zero].
    ring.
Qed.

(* ---- 2.0b 比值平移恒等对：(x·inv y)−1 == (x−y)·inv y ---- *)
(*   （复活续建增补：unit 事实 q·inv q==1 经 real_inv_pos_correct 兼容链
   入换形，环闭只吃纯多项式——原稿 EC/EC1 的点式 ring 不可达此形态） *)

Lemma df2_ratio_minus_one_eq : forall (p q : Real) (Hq : real_lt real_zero q),
  real_eq (real_plus (real_mult p (real_inv_pos q Hq)) (real_opp real_one))
          (real_mult (real_plus p (real_opp q)) (real_inv_pos q Hq)).
Proof.
  intros p q Hq.
  apply (real_eq_trans
           (real_plus (real_mult p (real_inv_pos q Hq)) (real_opp real_one))
           (real_plus (real_mult p (real_inv_pos q Hq))
                      (real_opp (real_mult q (real_inv_pos q Hq))))
           (real_mult (real_plus p (real_opp q)) (real_inv_pos q Hq))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult p (real_inv_pos q Hq)) (real_opp real_one)
             (real_mult p (real_inv_pos q Hq))
             (real_opp (real_mult q (real_inv_pos q Hq)))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat real_one
               (real_mult q (real_inv_pos q Hq))).
      apply real_eq_sym. exact (real_inv_pos_correct q Hq).
  - (remember (real_inv_pos q Hq) as iq; d2_ring_eq).
Qed.

Lemma df2_ratio1_minus_one_eq : forall (p q : Real)
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (real_plus (real_mult (p2_one_minus p)
                                (real_inv_pos (p2_one_minus q) Hq1))
                     (real_opp real_one))
          (real_mult (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))
                     (real_inv_pos (p2_one_minus q) Hq1)).
Proof.
  intros p q Hq1.
  apply (real_eq_trans
           (real_plus (real_mult (p2_one_minus p)
                                 (real_inv_pos (p2_one_minus q) Hq1))
                      (real_opp real_one))
           (real_plus (real_mult (p2_one_minus p)
                                 (real_inv_pos (p2_one_minus q) Hq1))
                      (real_opp (real_mult (p2_one_minus q)
                                           (real_inv_pos (p2_one_minus q) Hq1))))
           (real_mult (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))
                      (real_inv_pos (p2_one_minus q) Hq1))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (p2_one_minus p) (real_inv_pos (p2_one_minus q) Hq1))
             (real_opp real_one)
             (real_mult (p2_one_minus p) (real_inv_pos (p2_one_minus q) Hq1))
             (real_opp (real_mult (p2_one_minus q)
                                  (real_inv_pos (p2_one_minus q) Hq1)))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat real_one
               (real_mult (p2_one_minus q) (real_inv_pos (p2_one_minus q) Hq1))).
      apply real_eq_sym.
      exact (real_inv_pos_correct (p2_one_minus q) Hq1).
  - (remember (real_inv_pos (p2_one_minus q) Hq1) as iq1; d2_ring_eq).
Qed.

(* 比值平方消去：(x·inv y−1)²·权 == (x−y)²·inv y（unit_scale_sq 直取） *)
Lemma df2_ratio_sq_eq : forall (q w D : Real) (Hq : real_lt real_zero q)
  (Hu : real_eq (real_mult w (real_inv_pos q Hq)) real_one)
  (EC : real_eq (real_plus (real_mult D (real_inv_pos q Hq)) (real_opp real_one))
                (real_mult (real_plus D (real_opp q)) (real_inv_pos q Hq))),
  real_eq (real_mult w
             (real_mult (real_plus (real_mult D (real_inv_pos q Hq))
                                   (real_opp real_one))
                        (real_plus (real_mult D (real_inv_pos q Hq))
                                   (real_opp real_one))))
          (real_mult (real_mult (real_plus D (real_opp q))
                                (real_plus D (real_opp q)))
                     (real_inv_pos q Hq)).
Proof.
  intros q w D Hq Hu EC.
  apply (real_eq_trans
           (real_mult w
              (real_mult (real_plus (real_mult D (real_inv_pos q Hq))
                                    (real_opp real_one))
                         (real_plus (real_mult D (real_inv_pos q Hq))
                                    (real_opp real_one))))
           (real_mult w
              (real_mult (real_mult (real_plus D (real_opp q))
                                    (real_inv_pos q Hq))
                         (real_mult (real_plus D (real_opp q))
                                    (real_inv_pos q Hq))))
           (real_mult (real_mult (real_plus D (real_opp q))
                                 (real_plus D (real_opp q)))
                      (real_inv_pos q Hq))).
  - apply (RealSetoid.real_eq_mult_compat w
             (real_mult (real_plus (real_mult D (real_inv_pos q Hq))
                                   (real_opp real_one))
                        (real_plus (real_mult D (real_inv_pos q Hq))
                                   (real_opp real_one)))
             w
             (real_mult (real_mult (real_plus D (real_opp q))
                                   (real_inv_pos q Hq))
                        (real_mult (real_plus D (real_opp q))
                                   (real_inv_pos q Hq)))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_mult_compat
               (real_plus (real_mult D (real_inv_pos q Hq)) (real_opp real_one))
               (real_plus (real_mult D (real_inv_pos q Hq)) (real_opp real_one))
               (real_mult (real_plus D (real_opp q)) (real_inv_pos q Hq))
               (real_mult (real_plus D (real_opp q)) (real_inv_pos q Hq)) EC EC).
  - exact (df2_unit_scale_sq w (real_inv_pos q Hq) (real_plus D (real_opp q)) Hu).
Qed.

(* ---- 2.1 χ² 实例：比值替换数据与替换恒等 ---- *)

(* 比值数据 s := p·inv q、s' := (1−p)·inv(1−q)（inv 证书显式随行） *)
Definition df2_inst_chisq_s (p q : Real) (Hq : real_lt real_zero q) : Real :=
  real_mult p (real_inv_pos q Hq).

Definition df2_inst_chisq_s1 (p q : Real)
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_mult (p2_one_minus p) (real_inv_pos (p2_one_minus q) Hq1).

(* χ² 的 f 数据：f(u) := (u−1)²（Pearson 形，按件 1 载件 div2_cs 对应） *)
Definition df2_inst_chisq_fa (x : Real) : Real :=
  real_mult (real_plus x (real_opp real_one)) (real_plus x (real_opp real_one)).

(* 替换恒等：df2_cs_inst 于 χ² 比值数据处 == 件 1 载件 div2_cs
   （复活续建重修：S1/S2 走 df2_ratio_sq_eq 泛型件（unit 事实
   real_inv_pos_correct 兼容入链），real_inv_pos 项直取，无 remember；
   第二项余 (q−p)²==(p−q)² 环原子闭合） *)
Lemma df2_inst_chisq_eq : forall (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (df2_cs_inst q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1))
          (div2_cs p q Hq Hq1).
Proof.
  intros p q Hq Hq1.
  unfold df2_cs_inst, div2_cs, df2_inst_chisq_s, df2_inst_chisq_s1,
         df2_inst_chisq_fa.
  cbn [p2_diff p2_one_minus p2_tvsq].
  apply (RealSetoid.real_eq_plus_compat
           (real_mult q
              (real_mult (real_plus (real_mult p (real_inv_pos q Hq))
                                    (real_opp real_one))
                         (real_plus (real_mult p (real_inv_pos q Hq))
                                    (real_opp real_one))))(real_mult (real_plus real_one (real_opp q))
              (real_mult
                 (real_plus (real_mult (real_plus real_one (real_opp p))
                                       (real_inv_pos (real_plus real_one (real_opp q)) Hq1))
                            (real_opp real_one))
                 (real_plus (real_mult (real_plus real_one (real_opp p))
                                       (real_inv_pos (real_plus real_one (real_opp q)) Hq1))
                            (real_opp real_one))))(real_mult
              (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
              (real_inv_pos q Hq))
           (real_mult
              (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
              (real_inv_pos (real_plus real_one (real_opp q)) Hq1))).
  - (* S1：q·(s−1)² == (p−q)²·inv q（df2_ratio_sq_eq 直取） *)
    exact (df2_ratio_sq_eq q q p Hq (real_inv_pos_correct q Hq)
             (df2_ratio_minus_one_eq p q Hq)).
  - (* S2：(1−q)·(s'−1)² == (q−p)²·inv(1−q) → (p−q)²·inv(1−q) *)
    apply (real_eq_trans
             (real_mult (real_plus real_one (real_opp q))
                (real_mult
                   (real_plus (real_mult (real_plus real_one (real_opp p))
                                         (real_inv_pos (real_plus real_one (real_opp q)) Hq1))
                              (real_opp real_one))
                   (real_plus (real_mult (real_plus real_one (real_opp p))
                                         (real_inv_pos (real_plus real_one (real_opp q)) Hq1))
                              (real_opp real_one))))
             (real_mult
                (real_mult (real_plus (real_plus real_one (real_opp p))
                                      (real_opp (real_plus real_one (real_opp q))))
                           (real_plus (real_plus real_one (real_opp p))
                                      (real_opp (real_plus real_one (real_opp q)))))
                (real_inv_pos (real_plus real_one (real_opp q)) Hq1))
             (real_mult
                (real_mult (real_plus p (real_opp q)) (real_plus p (real_opp q)))
                (real_inv_pos (real_plus real_one (real_opp q)) Hq1))).
    + exact (df2_ratio_sq_eq (real_plus real_one (real_opp q))
               (real_plus real_one (real_opp q)) (real_plus real_one (real_opp p))
               Hq1
               (real_inv_pos_correct (real_plus real_one (real_opp q)) Hq1)
               (df2_ratio1_minus_one_eq p q Hq1)).
    + (remember (real_inv_pos (real_plus real_one (real_opp q)) Hq1) as iq1;
       d2_ring_eq).
Qed.

(* χ² 实例的 J 形（f 数据代入 df2_j；df2_j 节消去只收 q fa fb 三元——
   复活续建勘正：原稿五元调用错配节消去语义） *)
Definition df2_inst_chisq_j (p q : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  df2_j q
        (df2_inst_chisq_fa (df2_inst_chisq_s p q Hq))
        (df2_inst_chisq_fa (df2_inst_chisq_s1 p q Hq1)).

(* χ² 实例零照管证书：0·(u−1) == 0 ≤_B (u−1)²（cdown := 0——
   (u−1)² 形数据在 u=1 的真切距斜率即零） *)
Lemma df2_inst_chisq_hlow (x : Real) :
  real_le_b (real_mult real_zero (real_plus x (real_opp real_one)))
            (df2_inst_chisq_fa x).
Proof.
  (* 复活续建勘正：leb3_le_b_eq_l 语义为 x1==x2 → x1≤y → x2≤y，
   原稿 apply 方向倒置——x1:=real_zero、x2:=0·(x−1) 重排 *)
  apply (leb3_le_b_eq_l real_zero
           (real_mult real_zero (real_plus x (real_opp real_one)))
           (df2_inst_chisq_fa x)).
  - apply real_eq_sym. d2_ring_eq.
  - exact (real_square_nonneg_B (real_plus x (real_opp real_one))).
Qed.

(* ---- 2.2 χ² 实例核对·非负面：骨架复现件 1b 面 ---- *)

Corollary df2_inst_chisq_nonneg : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b real_zero (div2_cs p q Hq Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  (* 复活续建勘正：leb3_le_b_eq_r 语义为 x≤y1 → y1==y2 → x≤y2，
   原稿 eq_l 方向倒置——nonneg 弹经骨架 df2_j_nonneg 复现件 1b 面 *)
  apply (leb3_le_b_eq_r real_zero
           (df2_inst_chisq_j p q Hq Hq1) (div2_cs p q Hq Hq1)).
  - exact (df2_j_nonneg q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1)
             Hq Hq1
             (df2_norm_inst p q Hp Hq Hp1 Hq1)
             (df2_inst_chisq_fa (df2_inst_chisq_s p q Hq))
             (df2_inst_chisq_fa (df2_inst_chisq_s1 p q Hq1))
             real_zero
             (df2_inst_chisq_hlow (df2_inst_chisq_s p q Hq))
             (df2_inst_chisq_hlow (df2_inst_chisq_s1 p q Hq1))).
  - exact (df2_inst_chisq_eq p q Hq Hq1).
Qed.

(* ============================================================ *)
(* ---- 3. KL₂ 实例：excess 形 f 数据 s·log s−(s−1)（镜照管） ----    *)
(* ============================================================ *)

(* ---- 3.0b 零差尾消去：X − c·(0·S) == X（cup := 0 的尾项蒸发件） ---- *)

Lemma df2_sub_zero_r : forall (X c S : Real),
  real_eq (real_plus X (real_opp (real_mult c (real_mult real_zero S)))) X.
Proof.
  intros X c S.
  apply (real_eq_trans
           (real_plus X (real_opp (real_mult c (real_mult real_zero S))))
           (real_plus X (real_opp real_zero))
           X).
  - apply (RealSetoid.real_eq_plus_compat X
             (real_opp (real_mult c (real_mult real_zero S)))
             X (real_opp real_zero)).
    + apply real_eq_refl.
    + apply (RealSetoid.real_eq_opp_compat
               (real_mult c (real_mult real_zero S)) real_zero).
      d2_ring_eq.
  - apply (real_eq_trans
             (real_plus X (real_opp real_zero))
             (real_plus X real_zero)
             X).
    + apply (RealSetoid.real_eq_plus_compat X (real_opp real_zero) X real_zero).
      * apply real_eq_refl.
      * d2_ring_eq.
    + apply real_plus_zero.
Qed.

(* ---- 3.0c 扇出纯环件：q·(P−(S−1)) == q·P + (q−q·S) ---- *)
(*   全变量形独立纯环小件（沿用 dtv_swap_scale 先例同款：复合项不拆解，
   q S P 作哑变量整体 destruct，点式环闭不遇不透明 log/inv 定义原子——
   kl 上臂两处的 remember+d2_ring_eq 受阻位（df2_inst_kl_Ls·df2_inst_kl_Ls1
   不透明应用留在 projT1 下成 match 结构，ring 拒闭）由此直取代参闭合） *)
Lemma df2_fanout_ring : forall (q S P : Real),
  real_eq (real_mult q (real_plus P (real_opp (real_plus S (real_opp real_one)))))
          (real_plus (real_mult q P)
                     (real_plus q (real_opp (real_mult q S)))).
Proof.
  intros q S P.
  apply real_eq_of_zero_diff; intro n0.
  repeat match goal with [ x : Real |- _ ] => destruct x end.
  cbn [projT1 real_plus real_mult real_opp real_one real_zero].
  ring.
Qed.

(* ---- 3.0 镜面 E 非负：0 ≤_B (inv x − 1) − log(inv x) ---- *)
(*   dkc_E_nonneg 于 (p·inv q) 处给出 0 ≤_B (s−1)−log s；KL excess 形
   f 数据的非负需对偶不等式（log x ≥ 1−inv x，即镜面 E(1/x) ≥ 0）：
   于 inv x 处逐字重跑同一 eps 推理步（real_log_le_linear_B 单引擎，
   real_lt_id_l/real_lt_id_r/平移对消；证书 real_inv_pos_pos 全程匹配）。 *)

Lemma df2_E_mirror_nonneg : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b real_zero
    (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
               (real_opp (real_log (real_inv_pos x Hx)
                                   (real_inv_pos_pos x Hx)))).
Proof.
  intros x Hx.
  unfold real_le_b. intros e He.
  assert (HBe : real_lt (real_log (real_inv_pos x Hx)
                                  (real_inv_pos_pos x Hx))
                        (real_plus (real_plus (real_inv_pos x Hx)
                                              (real_opp real_one)) e)).
  { exact (real_log_le_linear_B (real_inv_pos x Hx)
                                (real_inv_pos_pos x Hx) e He). }
  assert (Hlt0 : real_lt real_zero
                   (real_plus
                      (real_opp (real_log (real_inv_pos x Hx)
                                          (real_inv_pos_pos x Hx)))
                      (real_plus (real_plus (real_inv_pos x Hx)
                                            (real_opp real_one)) e))).
  { apply (RealSetoid.real_lt_id_l real_zero
             (real_plus
                (real_opp (real_log (real_inv_pos x Hx)
                                    (real_inv_pos_pos x Hx)))
                (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
             (real_plus
                (real_opp (real_log (real_inv_pos x Hx)
                                    (real_inv_pos_pos x Hx)))
                (real_plus (real_plus (real_inv_pos x Hx)
                                      (real_opp real_one)) e))).
    - apply real_eq_sym.
      apply (real_eq_trans
               (real_plus
                  (real_opp (real_log (real_inv_pos x Hx)
                                      (real_inv_pos_pos x Hx)))
                  (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
               (real_plus
                  (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                  (real_opp (real_log (real_inv_pos x Hx)
                                      (real_inv_pos_pos x Hx))))
               real_zero).
      + apply real_plus_comm.
      + apply real_plus_opp.
    - exact (real_lt_plus_translate
               (real_opp (real_log (real_inv_pos x Hx)
                                   (real_inv_pos_pos x Hx)))
               (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
               (real_plus (real_plus (real_inv_pos x Hx)
                                     (real_opp real_one)) e) HBe). }
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus
              (real_opp (real_log (real_inv_pos x Hx)
                                  (real_inv_pos_pos x Hx)))
              (real_plus (real_plus (real_inv_pos x Hx)
                                    (real_opp real_one)) e))
           (real_plus
              (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                         (real_opp (real_log (real_inv_pos x Hx)
                                             (real_inv_pos_pos x Hx))))
              e)).
  - apply (real_eq_trans
             (real_plus
                (real_opp (real_log (real_inv_pos x Hx)
                                    (real_inv_pos_pos x Hx)))
                (real_plus (real_plus (real_inv_pos x Hx)
                                      (real_opp real_one)) e))
             (real_plus
                (real_plus
                   (real_opp (real_log (real_inv_pos x Hx)
                                       (real_inv_pos_pos x Hx)))
                   (real_plus (real_inv_pos x Hx) (real_opp real_one)))
                e)
             (real_plus
                (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                           (real_opp (real_log (real_inv_pos x Hx)
                                               (real_inv_pos_pos x Hx))))
                e)).
    + apply real_plus_assoc.
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus
                  (real_opp (real_log (real_inv_pos x Hx)
                                      (real_inv_pos_pos x Hx)))
                  (real_plus (real_inv_pos x Hx) (real_opp real_one)))
               e
               (real_plus
                  (real_plus (real_inv_pos x Hx) (real_opp real_one))
                  (real_opp (real_log (real_inv_pos x Hx)
                                      (real_inv_pos_pos x Hx))))
               e).
      * apply real_plus_comm.
      * apply real_eq_refl.
  - exact Hlt0.
Qed.

(* ---- 3.1 excess 形 f 数据点态非负：0 ≤_B x·log x − (x−1) ---- *)
(*   镜面 E ≥ 0 经 log(inv x) == −log x（real_log_inv_pos_opp，证书匹配）
   换形、leb3 正缩放（c := x > 0）、x·inv x == 1 消去重组（df2_unit_scale
   + real_opp_opp）闭合——KL₂ 照管证书核（cdown := 0 供弹）。 *)

Lemma df2_inst_kl_f_nonneg : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b real_zero
    (real_plus (real_mult x (real_log x Hx))
               (real_opp (real_plus x (real_opp real_one)))).
Proof.
  intros x Hx.
  assert (LOGM : real_eq (real_log (real_inv_pos x Hx)
                                   (real_inv_pos_pos x Hx))
                         (real_opp (real_log x Hx)))
    by exact (real_log_inv_pos_opp x Hx).
  assert (EM' : real_le_b real_zero
                  (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                             (real_log x Hx))).
  { apply (leb3_le_b_eq_r real_zero
             (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                        (real_opp (real_log (real_inv_pos x Hx)
                                            (real_inv_pos_pos x Hx))))
             (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                        (real_log x Hx))).
    - exact (df2_E_mirror_nonneg x Hx).
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_inv_pos x Hx) (real_opp real_one))
               (real_opp (real_log (real_inv_pos x Hx)
                                   (real_inv_pos_pos x Hx)))
               (real_plus (real_inv_pos x Hx) (real_opp real_one))
               (real_log x Hx)).
      + apply real_eq_refl.
      + apply (real_eq_trans
                 (real_opp (real_log (real_inv_pos x Hx)
                                     (real_inv_pos_pos x Hx)))
                 (real_opp (real_opp (real_log x Hx)))
                 (real_log x Hx)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                   (real_opp (real_log x Hx)) LOGM).
        * exact (real_opp_opp (real_log x Hx)). }
  assert (SCL : real_le_b (real_mult x real_zero)
                  (real_mult x
                     (real_plus (real_plus (real_inv_pos x Hx)
                                           (real_opp real_one))
                                (real_log x Hx)))).
  { exact (leb3_le_b_pos_scale_l real_zero
             (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                        (real_log x Hx)) x EM' Hx). }
  apply (leb3_le_b_eq_r real_zero
           (real_mult x
              (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                         (real_log x Hx)))
           (real_plus (real_mult x (real_log x Hx))
                      (real_opp (real_plus x (real_opp real_one))))).
  - apply (leb3_le_b_eq_l (real_mult x real_zero) real_zero
             (real_mult x
                (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                           (real_log x Hx)))).
    + apply real_mult_zero.
    + exact SCL.
  - apply (real_eq_trans
             (real_mult x
                (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                           (real_log x Hx)))
             (real_plus
                (real_plus (real_mult x (real_inv_pos x Hx))
                           (real_mult x (real_opp real_one)))
                (real_mult x (real_log x Hx)))
             (real_plus (real_mult x (real_log x Hx))
                        (real_opp (real_plus x (real_opp real_one))))).
    + assert (HR1 : real_eq
                 (real_mult x
                    (real_plus (real_plus (real_inv_pos x Hx) (real_opp real_one))
                               (real_log x Hx)))
                 (real_plus
                    (real_plus (real_mult x (real_inv_pos x Hx))
                               (real_mult x (real_opp real_one)))
                    (real_mult x (real_log x Hx))))
        by (clear LOGM;
            remember (real_inv_pos x Hx) as ix;
            remember (real_log x Hx) as Lx;
            d2_ring_eq).
      exact HR1.
    + apply (real_eq_trans
               (real_plus
                  (real_plus (real_mult x (real_inv_pos x Hx))
                             (real_mult x (real_opp real_one)))
                  (real_mult x (real_log x Hx)))
               (real_plus
                  (real_plus real_one (real_mult x (real_opp real_one)))
                  (real_mult x (real_log x Hx)))
               (real_plus (real_mult x (real_log x Hx))
                          (real_opp (real_plus x (real_opp real_one))))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus (real_mult x (real_inv_pos x Hx))
                            (real_mult x (real_opp real_one)))
                 (real_mult x (real_log x Hx))
                 (real_plus real_one (real_mult x (real_opp real_one)))
                 (real_mult x (real_log x Hx))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult x (real_inv_pos x Hx))
                     (real_mult x (real_opp real_one))
                     real_one
                     (real_mult x (real_opp real_one))).
           ++ exact (real_inv_pos_correct x Hx).
           ++ apply real_eq_refl.
        -- apply real_eq_refl.
      * assert (HR2 : real_eq
                   (real_plus
                      (real_plus real_one (real_mult x (real_opp real_one)))
                      (real_mult x (real_log x Hx)))
                   (real_plus (real_mult x (real_log x Hx))
                              (real_opp (real_plus x (real_opp real_one)))))
          by (clear LOGM; remember (real_log x Hx) as Lx; d2_ring_eq).
         exact HR2.
Qed.

(* ---- 3.2 KL₂ 比值数据与 excess 形 f 数据 ---- *)
(*   比值数据复用 χ² 件（df2_inst_chisq_s/s1）；log 证书逐点显式随行
   （AR 坑卡同款）；J 形走三元 df2_j（复活续建勘正④）。 *)

Definition df2_inst_kl_Ls (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) : Real :=
  real_log (real_mult p (real_inv_pos q Hq))
           (real_mult_positive p (real_inv_pos q Hq) Hp
              (real_inv_pos_pos q Hq)).

Definition df2_inst_kl_fa (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) : Real :=
  real_plus (real_mult (df2_inst_chisq_s p q Hq) (df2_inst_kl_Ls p q Hp Hq))
            (real_opp (real_plus (df2_inst_chisq_s p q Hq)
                                 (real_opp real_one))).

Definition df2_inst_kl_Ls1 (p q : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_log (real_mult (p2_one_minus p) (real_inv_pos (p2_one_minus q) Hq1))
           (real_mult_positive (p2_one_minus p)
                               (real_inv_pos (p2_one_minus q) Hq1) Hp1
                               (real_inv_pos_pos (p2_one_minus q) Hq1)).

Definition df2_inst_kl_fb (p q : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_plus (real_mult (df2_inst_chisq_s1 p q Hq1)
                       (df2_inst_kl_Ls1 p q Hp1 Hq1))
            (real_opp (real_plus (df2_inst_chisq_s1 p q Hq1)
                                 (real_opp real_one))).

Definition df2_inst_kl_j (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  df2_j q (df2_inst_kl_fa p q Hp Hq) (df2_inst_kl_fb p q Hp1 Hq1).

(* ---- 3.3 镜照管证书：0·(s−1) ≤_B f(s)、0·(s'−1) ≤_B f(s') ---- *)

Lemma df2_inst_kl_hlow : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_le_b (real_mult real_zero
                       (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one)))
            (df2_inst_kl_fa p q Hp Hq).
Proof.
  intros p q Hp Hq.
  apply (leb3_le_b_eq_l real_zero
           (real_mult real_zero
              (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one)))
           (df2_inst_kl_fa p q Hp Hq)).
  - (remember (df2_inst_chisq_s p q Hq) as S;
      apply real_eq_sym; d2_ring_eq).
  - exact (df2_inst_kl_f_nonneg (df2_inst_chisq_s p q Hq)
             (real_mult_positive p (real_inv_pos q Hq) Hp
                (real_inv_pos_pos q Hq))).
Qed.

Lemma df2_inst_kl_hlow1 : forall (p q : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b (real_mult real_zero
                       (real_plus (df2_inst_chisq_s1 p q Hq1)
                                  (real_opp real_one)))
            (df2_inst_kl_fb p q Hp1 Hq1).
Proof.
  intros p q Hp1 Hq1.
  apply (leb3_le_b_eq_l real_zero
           (real_mult real_zero
              (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one)))
           (df2_inst_kl_fb p q Hp1 Hq1)).
  - (remember (df2_inst_chisq_s1 p q Hq1) as S1;
      apply real_eq_sym; d2_ring_eq).
  - exact (df2_inst_kl_f_nonneg (df2_inst_chisq_s1 p q Hq1)
             (real_mult_positive (p2_one_minus p)
                                 (real_inv_pos (p2_one_minus q) Hq1) Hp1
                                 (real_inv_pos_pos (p2_one_minus q) Hq1))).
Qed.

(* ---- 3.4 kl 项恒等对：q·(s·log s) == kl 项（左右臂公用） ---- *)
(*   核：环原子换位 + df2_unit_scale（q·inv q==1）+ dkc_log_split
   + real_kl_term_expand（镜回 −log(q·inv p) 形）。 *)

(* 因子级 log 镜面恒等：(log x − log y) == −log(y·inv x)（dkc_log_split 反向
   + opp_compat；供 kl 项恒等对的 mult_compat 因子槽） *)
Lemma df2_log_split_mirror : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_eq (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
          (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                              (real_mult_positive q (real_inv_pos p Hp)
                                 Hq (real_inv_pos_pos p Hp)))).
Proof.
  intros p q Hp Hq.
  apply (real_eq_trans
           (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
           (real_opp (real_plus (real_log q Hq) (real_opp (real_log p Hp))))
           (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                               (real_mult_positive q (real_inv_pos p Hp)
                                  Hq (real_inv_pos_pos p Hp))))).
  - (remember (real_log p Hp) as LP;
      remember (real_log q Hq) as LQ;
      apply real_eq_of_zero_diff; intro n0;
      repeat match goal with [ x : Real |- _ ] => destruct x end;
      cbn [projT1 real_plus real_opp];
      ring).
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
             (real_log (real_mult q (real_inv_pos p Hp))
                       (real_mult_positive q (real_inv_pos p Hp)
                          Hq (real_inv_pos_pos p Hp)))).
    exact (real_eq_sym
             (real_log (real_mult q (real_inv_pos p Hp))
                       (real_mult_positive q (real_inv_pos p Hp)
                          Hq (real_inv_pos_pos p Hp)))
             (real_plus (real_log q Hq) (real_opp (real_log p Hp)))
             (dkc_log_split q p Hq Hp)).
Qed.

Lemma df2_inst_kl_term_eq : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_eq (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                  (df2_inst_kl_Ls p q Hp Hq)))
          (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                           (real_mult_positive q
                                              (real_inv_pos p Hp) Hq
                                              (real_inv_pos_pos p Hp))))).
Proof.
  intros p q Hp Hq.
  apply (real_eq_trans
           (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                   (df2_inst_kl_Ls p q Hp Hq)))
           (real_mult p (real_plus (real_log p Hp)
                                   (real_opp (real_log q Hq))))
           (real_mult p (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                            (real_mult_positive q
                                               (real_inv_pos p Hp) Hq
                                               (real_inv_pos_pos p Hp)))))).
  - apply (real_eq_trans
             (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                     (df2_inst_kl_Ls p q Hp Hq)))
             (real_mult p (df2_inst_kl_Ls p q Hp Hq))
             (real_mult p (real_plus (real_log p Hp)
                                     (real_opp (real_log q Hq))))).
    + apply (real_eq_trans
               (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                       (df2_inst_kl_Ls p q Hp Hq)))
               (real_mult q (real_mult (real_mult p (df2_inst_kl_Ls p q Hp Hq))
                                       (real_inv_pos q Hq)))
               (real_mult p (df2_inst_kl_Ls p q Hp Hq))).
      * (unfold df2_inst_chisq_s;
         remember (real_inv_pos q Hq) as iq;
         remember (df2_inst_kl_Ls p q Hp Hq) as Ls;
         d2_ring_eq).
      * exact (df2_unit_scale q (real_inv_pos q Hq)
                 (real_mult p (df2_inst_kl_Ls p q Hp Hq))
                 (real_inv_pos_correct q Hq)).
    + apply (RealSetoid.real_eq_mult_compat p (df2_inst_kl_Ls p q Hp Hq)
               p (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
               (real_eq_refl p) (dkc_log_split p q Hp Hq)).
  - apply (RealSetoid.real_eq_mult_compat p
             (real_plus (real_log p Hp) (real_opp (real_log q Hq)))
             p
             (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                 (real_mult_positive q (real_inv_pos p Hp)
                                    Hq (real_inv_pos_pos p Hp))))
             (real_eq_refl p)
             (df2_log_split_mirror p q Hp Hq)).
Qed.

Lemma df2_inst_kl_term1_eq : forall (p q : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (real_mult (p2_one_minus q)
                     (real_mult (df2_inst_chisq_s1 p q Hq1)
                                (df2_inst_kl_Ls1 p q Hp1 Hq1)))
          (real_mult (p2_one_minus p)
                     (real_opp (real_log
                                  (real_mult (p2_one_minus q)
                                             (real_inv_pos (p2_one_minus p) Hp1))
                                  (real_mult_positive (p2_one_minus q)
                                     (real_inv_pos (p2_one_minus p) Hp1) Hq1
                                     (real_inv_pos_pos (p2_one_minus p) Hp1))))).
Proof.
  intros p q Hp1 Hq1.
  apply (real_eq_trans
           (real_mult (p2_one_minus q)
              (real_mult (df2_inst_chisq_s1 p q Hq1)
                         (df2_inst_kl_Ls1 p q Hp1 Hq1)))
           (real_mult (p2_one_minus p)
              (real_plus (real_log (p2_one_minus p) Hp1)
                         (real_opp (real_log (p2_one_minus q) Hq1))))
           (real_mult (p2_one_minus p)
              (real_opp (real_log
                           (real_mult (p2_one_minus q)
                                      (real_inv_pos (p2_one_minus p) Hp1))
                           (real_mult_positive (p2_one_minus q)
                              (real_inv_pos (p2_one_minus p) Hp1) Hq1
                              (real_inv_pos_pos (p2_one_minus p) Hp1)))))).
  - apply (real_eq_trans
             (real_mult (p2_one_minus q)
                (real_mult (df2_inst_chisq_s1 p q Hq1)
                           (df2_inst_kl_Ls1 p q Hp1 Hq1)))
             (real_mult (p2_one_minus p) (df2_inst_kl_Ls1 p q Hp1 Hq1))
             (real_mult (p2_one_minus p)
                (real_plus (real_log (p2_one_minus p) Hp1)
                           (real_opp (real_log (p2_one_minus q) Hq1))))).
    + apply (real_eq_trans
               (real_mult (p2_one_minus q)
                  (real_mult (df2_inst_chisq_s1 p q Hq1)
                             (df2_inst_kl_Ls1 p q Hp1 Hq1)))
               (real_mult (p2_one_minus q)
                  (real_mult (real_mult (p2_one_minus p)
                                        (df2_inst_kl_Ls1 p q Hp1 Hq1))
                             (real_inv_pos (p2_one_minus q) Hq1)))
               (real_mult (p2_one_minus p) (df2_inst_kl_Ls1 p q Hp1 Hq1))).
      * (unfold df2_inst_chisq_s1;
         remember (real_inv_pos (p2_one_minus q) Hq1) as iq1;
         remember (df2_inst_kl_Ls1 p q Hp1 Hq1) as Ls1;
         d2_ring_eq).
      * exact (df2_unit_scale (p2_one_minus q)
                 (real_inv_pos (p2_one_minus q) Hq1)
                 (real_mult (p2_one_minus p) (df2_inst_kl_Ls1 p q Hp1 Hq1))
                 (real_inv_pos_correct (p2_one_minus q) Hq1)).
    + apply (RealSetoid.real_eq_mult_compat (p2_one_minus p)
               (df2_inst_kl_Ls1 p q Hp1 Hq1)
               (p2_one_minus p)
               (real_plus (real_log (p2_one_minus p) Hp1)
                          (real_opp (real_log (p2_one_minus q) Hq1)))
               (real_eq_refl (p2_one_minus p))
               (dkc_log_split (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)).
  - apply (RealSetoid.real_eq_mult_compat (p2_one_minus p)
             (real_plus (real_log (p2_one_minus p) Hp1)
                        (real_opp (real_log (p2_one_minus q) Hq1)))
             (p2_one_minus p)
             (real_opp (real_log
                          (real_mult (p2_one_minus q)
                                     (real_inv_pos (p2_one_minus p) Hp1))
                          (real_mult_positive (p2_one_minus q)
                             (real_inv_pos (p2_one_minus p) Hp1) Hq1
                             (real_inv_pos_pos (p2_one_minus p) Hp1))))
             (real_eq_refl (p2_one_minus p))
             (df2_log_split_mirror (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)).
Qed.

(* ---- 3.5 替换恒等：J_KL == p2_kl2（归一化对消 + kl 项恒等对组装） ---- *)

Lemma df2_inst_kl_eq : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (df2_inst_kl_j p q Hp Hq Hp1 Hq1) (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  assert (HN := df2_norm_inst p q Hp Hq Hp1 Hq1).
  unfold df2_inst_kl_j, df2_j, df2_inst_kl_fa, df2_inst_kl_fb,
         df2_inst_chisq_s, df2_inst_chisq_s1, p2_kl2, real_kl_term.
  apply (real_eq_trans
           (real_plus
              (real_mult q
                 (real_plus (real_mult (real_mult p (real_inv_pos q Hq))
                                       (df2_inst_kl_Ls p q Hp Hq))
                            (real_opp (real_plus (real_mult p (real_inv_pos q Hq))
                                                 (real_opp real_one)))))
              (real_mult (p2_one_minus q)
                 (real_plus (real_mult (real_mult (p2_one_minus p)
                                                   (real_inv_pos (p2_one_minus q) Hq1))
                                       (df2_inst_kl_Ls1 p q Hp1 Hq1))
                            (real_opp (real_plus (real_mult (p2_one_minus p)
                                                            (real_inv_pos (p2_one_minus q) Hq1))
                                                 (real_opp real_one))))))
           (real_plus
              (real_mult q
                 (real_mult (real_mult p (real_inv_pos q Hq))
                            (df2_inst_kl_Ls p q Hp Hq)))
              (real_plus
                 (real_mult (p2_one_minus q)
                            (real_mult (real_mult (p2_one_minus p)
                                                  (real_inv_pos (p2_one_minus q) Hq1))
                                       (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                 (real_plus real_one
                            (real_opp
                               (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                          (real_mult (p2_one_minus q)
                                                     (real_mult (p2_one_minus p)
                                                                (real_inv_pos (p2_one_minus q) Hq1))))))))
           (real_plus
              (real_mult p
                 (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                     (real_mult_positive q (real_inv_pos p Hp)
                                        Hq (real_inv_pos_pos p Hp)))))
              (real_mult (p2_one_minus p)
                 (real_opp (real_log (real_mult (p2_one_minus q)
                                                (real_inv_pos (p2_one_minus p) Hp1))
                                     (real_mult_positive (p2_one_minus q)
                                        (real_inv_pos (p2_one_minus p) Hp1)
                                        Hq1 (real_inv_pos_pos (p2_one_minus p) Hp1))))))).
  - (remember (real_inv_pos q Hq) as iq;
      remember (real_inv_pos (p2_one_minus q) Hq1) as iq1;
      remember (df2_inst_kl_Ls p q Hp Hq) as Ls;
      remember (df2_inst_kl_Ls1 p q Hp1 Hq1) as Ls1;
      d2_ring_eq).
  - apply (real_eq_trans
             (real_plus
                (real_mult q
                   (real_mult (real_mult p (real_inv_pos q Hq))
                              (df2_inst_kl_Ls p q Hp Hq)))
                (real_plus
                   (real_mult (p2_one_minus q)
                              (real_mult (real_mult (p2_one_minus p)
                                                    (real_inv_pos (p2_one_minus q) Hq1))
                                         (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                   (real_plus real_one
                              (real_opp
                                 (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                            (real_mult (p2_one_minus q)
                                                       (real_mult (p2_one_minus p)
                                                                  (real_inv_pos (p2_one_minus q) Hq1))))))))
             (real_plus
                (real_mult q
                   (real_mult (real_mult p (real_inv_pos q Hq))
                              (df2_inst_kl_Ls p q Hp Hq)))
                (real_plus
                   (real_mult (p2_one_minus q)
                              (real_mult (real_mult (p2_one_minus p)
                                                    (real_inv_pos (p2_one_minus q) Hq1))
                                         (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                   real_zero))
             (real_plus
                (real_mult p
                   (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                       (real_mult_positive q (real_inv_pos p Hp)
                                          Hq (real_inv_pos_pos p Hp)))))
                (real_mult (p2_one_minus p)
                   (real_opp (real_log (real_mult (p2_one_minus q)
                                                  (real_inv_pos (p2_one_minus p) Hp1))
                                       (real_mult_positive (p2_one_minus q)
                                          (real_inv_pos (p2_one_minus p) Hp1)
                                          Hq1 (real_inv_pos_pos (p2_one_minus p) Hp1))))))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult q
                  (real_mult (real_mult p (real_inv_pos q Hq))
                             (df2_inst_kl_Ls p q Hp Hq)))(real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult (real_mult (p2_one_minus p)
                                                   (real_inv_pos (p2_one_minus q) Hq1))
                                        (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                  (real_plus real_one
                             (real_opp
                                (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                           (real_mult (p2_one_minus q)
                                                      (real_mult (p2_one_minus p)
                                                                 (real_inv_pos (p2_one_minus q) Hq1)))))))(real_mult q
                  (real_mult (real_mult p (real_inv_pos q Hq))
                             (df2_inst_kl_Ls p q Hp Hq)))
               (real_plus
                  (real_mult (p2_one_minus q)
                             (real_mult (real_mult (p2_one_minus p)
                                                   (real_inv_pos (p2_one_minus q) Hq1))
                                        (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                  real_zero)).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (p2_one_minus q)
                    (real_mult (real_mult (p2_one_minus p)
                                          (real_inv_pos (p2_one_minus q) Hq1))
                               (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                 (real_plus real_one
                            (real_opp
                               (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                          (real_mult (p2_one_minus q)
                                                     (real_mult (p2_one_minus p)
                                                                (real_inv_pos (p2_one_minus q) Hq1))))))
                 (real_mult (p2_one_minus q)
                    (real_mult (real_mult (p2_one_minus p)
                                          (real_inv_pos (p2_one_minus q) Hq1))
                               (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                 real_zero).
        -- apply real_eq_refl.
        -- apply (real_eq_trans
                    (real_plus real_one
                               (real_opp
                                  (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                             (real_mult (p2_one_minus q)
                                                        (real_mult (p2_one_minus p)
                                                                   (real_inv_pos (p2_one_minus q) Hq1))))))
                    (real_plus real_one (real_opp real_one))
                    real_zero).
           ++ apply (RealSetoid.real_eq_plus_compat real_one
                       (real_opp
                          (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                     (real_mult (p2_one_minus q)
                                                (real_mult (p2_one_minus p)
                                                           (real_inv_pos (p2_one_minus q) Hq1)))))
                       real_one (real_opp real_one)).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_opp_compat
                          (real_plus (real_mult q (real_mult p (real_inv_pos q Hq)))
                                     (real_mult (p2_one_minus q)
                                                (real_mult (p2_one_minus p)
                                                           (real_inv_pos (p2_one_minus q) Hq1))))
                          real_one).
                 exact HN.
           ++ apply real_plus_opp.
    + apply (real_eq_trans
               (real_plus
                  (real_mult q
                     (real_mult (real_mult p (real_inv_pos q Hq))
                                (df2_inst_kl_Ls p q Hp Hq)))
                  (real_plus
                     (real_mult (p2_one_minus q)
                                (real_mult (real_mult (p2_one_minus p)
                                                      (real_inv_pos (p2_one_minus q) Hq1))
                                           (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                     real_zero))
               (real_plus
                  (real_mult q
                     (real_mult (real_mult p (real_inv_pos q Hq))
                                (df2_inst_kl_Ls p q Hp Hq)))
                  (real_mult (p2_one_minus q)
                             (real_mult (real_mult (p2_one_minus p)
                                                   (real_inv_pos (p2_one_minus q) Hq1))
                                        (df2_inst_kl_Ls1 p q Hp1 Hq1))))
               (real_plus
                  (real_mult p
                     (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                         (real_mult_positive q (real_inv_pos p Hp)
                                            Hq (real_inv_pos_pos p Hp)))))
                  (real_mult (p2_one_minus p)
                     (real_opp (real_log (real_mult (p2_one_minus q)
                                                    (real_inv_pos (p2_one_minus p) Hp1))
                                         (real_mult_positive (p2_one_minus q)
                                            (real_inv_pos (p2_one_minus p) Hp1)
                                            Hq1 (real_inv_pos_pos (p2_one_minus p) Hp1))))))).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult q
                    (real_mult (real_mult p (real_inv_pos q Hq))
                               (df2_inst_kl_Ls p q Hp Hq)))
                 (real_plus
                    (real_mult (p2_one_minus q)
                               (real_mult (real_mult (p2_one_minus p)
                                                     (real_inv_pos (p2_one_minus q) Hq1))
                                          (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                    real_zero)
                 (real_mult q
                    (real_mult (real_mult p (real_inv_pos q Hq))
                               (df2_inst_kl_Ls p q Hp Hq)))
                 (real_mult (p2_one_minus q)
                    (real_mult (real_mult (p2_one_minus p)
                                          (real_inv_pos (p2_one_minus q) Hq1))
                               (df2_inst_kl_Ls1 p q Hp1 Hq1)))).
        -- apply real_eq_refl.
        -- apply real_plus_zero.
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult q
                    (real_mult (real_mult p (real_inv_pos q Hq))
                               (df2_inst_kl_Ls p q Hp Hq)))(real_mult (p2_one_minus q)
                    (real_mult (real_mult (p2_one_minus p)
                                          (real_inv_pos (p2_one_minus q) Hq1))
                               (df2_inst_kl_Ls1 p q Hp1 Hq1)))(real_mult p
                    (real_opp (real_log (real_mult q (real_inv_pos p Hp))
                                        (real_mult_positive q (real_inv_pos p Hp)
                                           Hq (real_inv_pos_pos p Hp)))))
                 (real_mult (p2_one_minus p)
                    (real_opp (real_log (real_mult (p2_one_minus q)
                                                   (real_inv_pos (p2_one_minus p) Hp1))
                                        (real_mult_positive (p2_one_minus q)
                                           (real_inv_pos (p2_one_minus p) Hp1)
                                           Hq1 (real_inv_pos_pos (p2_one_minus p) Hp1)))))).
        -- exact (df2_inst_kl_term_eq p q Hp Hq).
        -- exact (df2_inst_kl_term1_eq p q Hp1 Hq1).
Qed.

(* ---- 3.6 cup 证书（cup := 0；dkc_gap_le_term 供弹）与双面复现 ---- *)
(*   上臂：q·f(s) − q·0·(s−1) == kl + (q−p) ≤_B (p−q)²·inv q
   （dkc_gap_le_term），右端 q·(s−1)² 换形走 df2_ratio_sq_eq 对称件。 *)

Lemma df2_inst_kl_up : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q),
  real_le_b
    (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
               (real_opp (real_mult q
                            (real_mult real_zero
                                       (real_plus (df2_inst_chisq_s p q Hq)
                                                  (real_opp real_one))))))
    (real_mult q (real_mult (real_plus (df2_inst_chisq_s p q Hq)
                                       (real_opp real_one))
                            (real_plus (df2_inst_chisq_s p q Hq)
                                       (real_opp real_one)))).
Proof.
  intros p q Hp Hq.
  apply (leb3_le_b_eq_r
           (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
                      (real_opp (real_mult q
                                 (real_mult real_zero
                                            (real_plus (df2_inst_chisq_s p q Hq)
                                                       (real_opp real_one))))))
           (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
           (real_mult q (real_mult (real_plus (df2_inst_chisq_s p q Hq)
                                              (real_opp real_one))
                                   (real_plus (df2_inst_chisq_s p q Hq)
                                              (real_opp real_one))))).
  - apply (leb3_le_b_eq_l
             (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
             (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
                        (real_opp (real_mult q
                                   (real_mult real_zero
                                              (real_plus (df2_inst_chisq_s p q Hq)
                                                         (real_opp real_one))))))
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
                          (real_opp (real_mult q
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s p q Hq)
                                                           (real_opp real_one))))))
               (real_mult q (df2_inst_kl_fa p q Hp Hq))
               (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
      * exact (df2_sub_zero_r (real_mult q (df2_inst_kl_fa p q Hp Hq)) q
                 (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one))).
      * unfold df2_inst_kl_fa.
        apply (real_eq_trans
                 (real_mult q
                    (real_plus (real_mult (df2_inst_chisq_s p q Hq)
                                          (df2_inst_kl_Ls p q Hp Hq))
                               (real_opp (real_plus (df2_inst_chisq_s p q Hq)
                                                    (real_opp real_one)))))
                 (real_plus
                    (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                            (df2_inst_kl_Ls p q Hp Hq)))
                    (real_plus q
                               (real_opp (real_mult q (df2_inst_chisq_s p q Hq)))))
                 (real_plus (real_kl_term p q Hp Hq)
                            (real_plus q (real_opp p)))).
        -- apply df2_fanout_ring.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult q (real_mult (df2_inst_chisq_s p q Hq)
                                             (df2_inst_kl_Ls p q Hp Hq)))(real_plus q (real_opp (real_mult q (df2_inst_chisq_s p q Hq))))(real_kl_term p q Hp Hq)
                     (real_plus q (real_opp p))).
           ++ exact (df2_inst_kl_term_eq p q Hp Hq).
           ++ apply (RealSetoid.real_eq_plus_compat q
                       (real_opp (real_mult q (df2_inst_chisq_s p q Hq)))
                       q (real_opp p)).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_opp_compat
                          (real_mult q (df2_inst_chisq_s p q Hq)) p).
                 exact (df2_unit_scale q (real_inv_pos q Hq) p
                          (real_inv_pos_correct q Hq)).
    + exact (dkc_gap_le_term p q Hp Hq).
  - apply real_eq_sym.
    exact (df2_ratio_sq_eq q q p Hq (real_inv_pos_correct q Hq)
             (df2_ratio_minus_one_eq p q Hq)).
Qed.

Lemma df2_inst_kl_up1 : forall (p q : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b
    (real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
               (real_opp (real_mult (p2_one_minus q)
                            (real_mult real_zero
                                       (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                  (real_opp real_one))))))
    (real_mult (p2_one_minus q)
               (real_mult (real_plus (df2_inst_chisq_s1 p q Hq1)
                                     (real_opp real_one))
                          (real_plus (df2_inst_chisq_s1 p q Hq1)
                                     (real_opp real_one)))).
Proof.
  intros p q Hp1 Hq1.
  apply (leb3_le_b_eq_r
           (real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                      (real_opp (real_mult (p2_one_minus q)
                                 (real_mult real_zero
                                            (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                       (real_opp real_one))))))
           (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                      (real_inv_pos (p2_one_minus q) Hq1))
           (real_mult (p2_one_minus q)
                      (real_mult (real_plus (df2_inst_chisq_s1 p q Hq1)
                                            (real_opp real_one))
                                 (real_plus (df2_inst_chisq_s1 p q Hq1)
                                            (real_opp real_one))))).
  - apply (leb3_le_b_eq_l
             (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                        (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))
             (real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                        (real_opp (real_mult (p2_one_minus q)
                                   (real_mult real_zero
                                              (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                         (real_opp real_one))))))
             (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                        (real_inv_pos (p2_one_minus q) Hq1))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                          (real_opp (real_mult (p2_one_minus q)
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                           (real_opp real_one))))))
               (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                          (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))).
      * exact (df2_sub_zero_r
                 (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                 (p2_one_minus q)
                 (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one))).
      * unfold df2_inst_kl_fb.
        apply (real_eq_trans
                 (real_mult (p2_one_minus q)
                    (real_plus (real_mult (df2_inst_chisq_s1 p q Hq1)
                                          (df2_inst_kl_Ls1 p q Hp1 Hq1))
                               (real_opp (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                    (real_opp real_one)))))
                 (real_plus
                    (real_mult (p2_one_minus q)
                               (real_mult (df2_inst_chisq_s1 p q Hq1)
                                          (df2_inst_kl_Ls1 p q Hp1 Hq1)))
                    (real_plus (p2_one_minus q)
                               (real_opp (real_mult (p2_one_minus q)
                                                    (df2_inst_chisq_s1 p q Hq1)))))
                 (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                            (real_plus (p2_one_minus q)
                                       (real_opp (p2_one_minus p))))).
        -- apply df2_fanout_ring.
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_mult (p2_one_minus q)
                                (real_mult (df2_inst_chisq_s1 p q Hq1)
                                           (df2_inst_kl_Ls1 p q Hp1 Hq1)))(real_plus (p2_one_minus q)
                                (real_opp (real_mult (p2_one_minus q)
                                                     (df2_inst_chisq_s1 p q Hq1))))(real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                     (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))).
           ++ exact (df2_inst_kl_term1_eq p q Hp1 Hq1).
           ++ apply (RealSetoid.real_eq_plus_compat (p2_one_minus q)
                       (real_opp (real_mult (p2_one_minus q) (df2_inst_chisq_s1 p q Hq1)))
                       (p2_one_minus q) (real_opp (p2_one_minus p))).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_opp_compat
                          (real_mult (p2_one_minus q) (df2_inst_chisq_s1 p q Hq1))
                          (p2_one_minus p)).
                 exact (df2_unit_scale (p2_one_minus q)
                          (real_inv_pos (p2_one_minus q) Hq1) (p2_one_minus p)
                          (real_inv_pos_correct (p2_one_minus q) Hq1)).
    + exact (dkc_gap_le_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).
  - apply real_eq_sym.
    exact (df2_ratio_sq_eq (p2_one_minus q) (p2_one_minus q) (p2_one_minus p)
             Hq1 (real_inv_pos_correct (p2_one_minus q) Hq1)
             (df2_ratio1_minus_one_eq p q Hq1)).
Qed.

Lemma df2_inst_kl_le_cs_raw : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b (df2_inst_kl_j p q Hp Hq Hp1 Hq1) (div2_cs p q Hq Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  apply (leb3_le_b_eq_r (df2_inst_kl_j p q Hp Hq Hp1 Hq1)
           (df2_cs_inst q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1))
           (div2_cs p q Hq Hq1)).
  - apply (leb3_le_b_eq_l
             (real_plus
                (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
                           (real_opp (real_mult q
                                      (real_mult real_zero
                                                 (real_plus (df2_inst_chisq_s p q Hq)
                                                            (real_opp real_one))))))
                (real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                           (real_opp (real_mult (p2_one_minus q)
                                      (real_mult real_zero
                                                 (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                            (real_opp real_one)))))))
             (df2_inst_kl_j p q Hp Hq Hp1 Hq1)
             (df2_cs_inst q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult q (df2_inst_kl_fa p q Hp Hq))
                          (real_opp (real_mult q
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s p q Hq)
                                                           (real_opp real_one))))))(real_plus (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                          (real_opp (real_mult (p2_one_minus q)
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                           (real_opp real_one))))))(real_mult q (df2_inst_kl_fa p q Hp Hq))
               (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))).
      * exact (df2_sub_zero_r (real_mult q (df2_inst_kl_fa p q Hp Hq)) q
                 (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one))).
      * exact (df2_sub_zero_r
                 (real_mult (p2_one_minus q) (df2_inst_kl_fb p q Hp1 Hq1))
                 (p2_one_minus q)
                 (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one))).
    + exact (df2_j_le_cs q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1)
               (df2_inst_kl_fa p q Hp Hq) (df2_inst_kl_fb p q Hp1 Hq1)
               real_zero (df2_inst_kl_up p q Hp Hq) (df2_inst_kl_up1 p q Hp1 Hq1)).
  - exact (df2_inst_chisq_eq p q Hq Hq1).
Qed.

Corollary df2_inst_kl_nonneg : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  apply (leb3_le_b_eq_r real_zero
           (df2_inst_kl_j p q Hp Hq Hp1 Hq1) (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - exact (df2_j_nonneg q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1)
             Hq Hq1 (df2_norm_inst p q Hp Hq Hp1 Hq1)
             (df2_inst_kl_fa p q Hp Hq) (df2_inst_kl_fb p q Hp1 Hq1)
             real_zero
             (df2_inst_kl_hlow p q Hp Hq) (df2_inst_kl_hlow1 p q Hp1 Hq1)).
  - exact (df2_inst_kl_eq p q Hp Hq Hp1 Hq1).
Qed.

Corollary df2_inst_kl_le_cs : forall (p q : Real) (Hp : real_lt real_zero p)
  (Hq : real_lt real_zero q) (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b (p2_kl2 p q Hp Hq Hp1 Hq1) (div2_cs p q Hq Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1.
  apply (leb3_le_b_eq_l (df2_inst_kl_j p q Hp Hq Hp1 Hq1)
           (p2_kl2 p q Hp Hq Hp1 Hq1) (div2_cs p q Hq Hq1)).
  - exact (df2_inst_kl_eq p q Hp Hq Hp1 Hq1).
  - exact (df2_inst_kl_le_cs_raw p q Hp Hq Hp1 Hq1).
Qed.

(* ============================================================ *)
(* ---- 4. Hellinger 实例：见证平方形（件 3 已落盘，零欠账闭合） ----   *)
(* ============================================================ *)

(*   f 数据取件 3 载件同构形：f(s) := (sp−sq)²·inv q（数学上 == (√s−1)²，
   s := p·inv q、√s = sp·inv sq 见证比——sq·inv sq 消去后恒等）；
   J_hel == dhe_h2 由两次 df2_unit_scale 闭合（免见证乘法）；
   照管与上臂证书零新增数学（平方非负 + 件 3 gap 下臂夹逼）。 *)

Definition df2_inst_hel_fa (p q sp sq : Real) (Hq : real_lt real_zero q) : Real :=
  real_mult (p2_tvsq sp sq) (real_inv_pos q Hq).

Definition df2_inst_hel_fb (p q sp1 sq1 : Real)
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_mult (p2_tvsq sp1 sq1) (real_inv_pos (p2_one_minus q) Hq1).

Definition df2_inst_hel_j (p q sp sq sp1 sq1 : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  df2_j q (df2_inst_hel_fa p q sp sq Hq) (df2_inst_hel_fb p q sp1 sq1 Hq1).

(* ---- 4.1 照管证书：0·(s−1) ≤_B f(s)（平方非负 × inv 正缩放） ---- *)

Lemma df2_inst_hel_hlow : forall (p q sp sq : Real) (Hq : real_lt real_zero q),
  real_le_b (real_mult real_zero
                       (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one)))
            (df2_inst_hel_fa p q sp sq Hq).
Proof.
  intros p q sp sq Hq.
  apply (leb3_le_b_eq_l real_zero
           (real_mult real_zero
              (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one)))
           (df2_inst_hel_fa p q sp sq Hq)).
  - (remember (df2_inst_chisq_s p q Hq) as S;
      apply real_eq_sym; d2_ring_eq).
  - apply (leb3_le_b_eq_r real_zero
             (real_mult (real_inv_pos q Hq) (p2_tvsq sp sq))
             (real_mult (p2_tvsq sp sq) (real_inv_pos q Hq))).
    + apply (leb3_le_b_eq_l (real_mult (real_inv_pos q Hq) real_zero) real_zero
               (real_mult (real_inv_pos q Hq) (p2_tvsq sp sq))).
      * (remember (real_inv_pos q Hq) as iq; d2_ring_eq).
      * exact (leb3_le_b_pos_scale_l real_zero (p2_tvsq sp sq)
                 (real_inv_pos q Hq)
                 (real_square_nonneg_B (p2_diff sp sq))
                 (real_inv_pos_pos q Hq)).
    + apply real_mult_comm.
Qed.

Lemma df2_inst_hel_hlow1 : forall (p q sp1 sq1 : Real)
  (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_le_b (real_mult real_zero
                       (real_plus (df2_inst_chisq_s1 p q Hq1)
                                  (real_opp real_one)))
            (df2_inst_hel_fb p q sp1 sq1 Hq1).
Proof.
  intros p q sp1 sq1 Hq1.
  apply (leb3_le_b_eq_l real_zero
           (real_mult real_zero
              (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one)))
           (df2_inst_hel_fb p q sp1 sq1 Hq1)).
  - (remember (df2_inst_chisq_s1 p q Hq1) as S1;
      apply real_eq_sym; d2_ring_eq).
  - apply (leb3_le_b_eq_r real_zero
             (real_mult (real_inv_pos (p2_one_minus q) Hq1) (p2_tvsq sp1 sq1))
             (real_mult (p2_tvsq sp1 sq1) (real_inv_pos (p2_one_minus q) Hq1))).
    + apply (leb3_le_b_eq_l
               (real_mult (real_inv_pos (p2_one_minus q) Hq1) real_zero)
               real_zero
               (real_mult (real_inv_pos (p2_one_minus q) Hq1) (p2_tvsq sp1 sq1))).
      * (remember (real_inv_pos (p2_one_minus q) Hq1) as iq1; d2_ring_eq).
      * exact (leb3_le_b_pos_scale_l real_zero (p2_tvsq sp1 sq1)
                 (real_inv_pos (p2_one_minus q) Hq1)
                 (real_square_nonneg_B (p2_diff sp1 sq1))
                 (real_inv_pos_pos (p2_one_minus q) Hq1)).
    + apply real_mult_comm.
Qed.

(* ---- 4.2 替换恒等：J_hel == dhe_h2（两次 unit_scale 闭合） ---- *)

Lemma df2_inst_hel_eq : forall (p q sp sq sp1 sq1 : Real)
  (Hq : real_lt real_zero q) (Hq1 : real_lt real_zero (p2_one_minus q)),
  real_eq (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1)
          (dhe_h2 p q sp sq sp1 sq1).
Proof.
  intros p q sp sq sp1 sq1 Hq Hq1.
  unfold df2_inst_hel_j, df2_j, df2_inst_hel_fa, df2_inst_hel_fb, dhe_h2.
  apply (RealSetoid.real_eq_plus_compat
           (real_mult q (real_mult (p2_tvsq sp sq) (real_inv_pos q Hq)))(real_mult (p2_one_minus q)
                      (real_mult (p2_tvsq sp1 sq1)
                                 (real_inv_pos (p2_one_minus q) Hq1)))(p2_tvsq sp sq)
           (p2_tvsq sp1 sq1)).
  - exact (df2_unit_scale q (real_inv_pos q Hq) (p2_tvsq sp sq)
             (real_inv_pos_correct q Hq)).
  - exact (df2_unit_scale (p2_one_minus q) (real_inv_pos (p2_one_minus q) Hq1)
             (p2_tvsq sp1 sq1)
             (real_inv_pos_correct (p2_one_minus q) Hq1)).
Qed.

(* ---- 4.3 cup 证书（dhe_gap_ge_h2term + dkc_gap_le_term 夹逼） ---- *)

Lemma df2_inst_hel_up : forall (p q sp sq : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q),
  real_le_b
    (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
               (real_opp (real_mult q
                            (real_mult real_zero
                                       (real_plus (df2_inst_chisq_s p q Hq)
                                                  (real_opp real_one))))))
    (real_mult q (real_mult (real_plus (df2_inst_chisq_s p q Hq)
                                       (real_opp real_one))
                            (real_plus (df2_inst_chisq_s p q Hq)
                                       (real_opp real_one)))).
Proof.
  intros p q sp sq Hp Hq Hsp Hsq Hspe Hsqe.
  apply (leb3_le_b_eq_r
           (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
                      (real_opp (real_mult q
                                 (real_mult real_zero
                                            (real_plus (df2_inst_chisq_s p q Hq)
                                                       (real_opp real_one))))))
           (real_mult (p2_tvsq p q) (real_inv_pos q Hq))
           (real_mult q (real_mult (real_plus (df2_inst_chisq_s p q Hq)
                                              (real_opp real_one))
                                   (real_plus (df2_inst_chisq_s p q Hq)
                                              (real_opp real_one))))).
  - apply (leb3_le_b_eq_l (p2_tvsq sp sq)
             (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
                        (real_opp (real_mult q
                                   (real_mult real_zero
                                              (real_plus (df2_inst_chisq_s p q Hq)
                                                         (real_opp real_one))))))
             (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
                          (real_opp (real_mult q
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s p q Hq)
                                                           (real_opp real_one))))))
               (real_mult q (df2_inst_hel_fa p q sp sq Hq))
               (p2_tvsq sp sq)).
      * exact (df2_sub_zero_r (real_mult q (df2_inst_hel_fa p q sp sq Hq)) q
                 (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one))).
      * unfold df2_inst_hel_fa.
        exact (df2_unit_scale q (real_inv_pos q Hq) (p2_tvsq sp sq)
                 (real_inv_pos_correct q Hq)).
    + apply (real_le_b_trans (p2_tvsq sp sq)
               (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))
               (real_mult (p2_tvsq p q) (real_inv_pos q Hq))).
      * exact (dhe_gap_ge_h2term p q sp sq Hp Hq Hsp Hsq Hspe Hsqe).
      * exact (dkc_gap_le_term p q Hp Hq).
  - apply real_eq_sym.
    exact (df2_ratio_sq_eq q q p Hq (real_inv_pos_correct q Hq)
             (df2_ratio_minus_one_eq p q Hq)).
Qed.

Lemma df2_inst_hel_up1 : forall (p q sp1 sq1 : Real)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b
    (real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
               (real_opp (real_mult (p2_one_minus q)
                            (real_mult real_zero
                                       (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                  (real_opp real_one))))))
    (real_mult (p2_one_minus q)
               (real_mult (real_plus (df2_inst_chisq_s1 p q Hq1)
                                     (real_opp real_one))
                          (real_plus (df2_inst_chisq_s1 p q Hq1)
                                     (real_opp real_one)))).
Proof.
  intros p q sp1 sq1 Hp1 Hq1 Hsp1 Hsq1 Hsp1e Hsq1e.
  apply (leb3_le_b_eq_r
           (real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                      (real_opp (real_mult (p2_one_minus q)
                                 (real_mult real_zero
                                            (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                       (real_opp real_one))))))
           (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                      (real_inv_pos (p2_one_minus q) Hq1))
           (real_mult (p2_one_minus q)
                      (real_mult (real_plus (df2_inst_chisq_s1 p q Hq1)
                                            (real_opp real_one))
                                 (real_plus (df2_inst_chisq_s1 p q Hq1)
                                            (real_opp real_one))))).
  - apply (leb3_le_b_eq_l (p2_tvsq sp1 sq1)
             (real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                        (real_opp (real_mult (p2_one_minus q)
                                   (real_mult real_zero
                                              (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                         (real_opp real_one))))))
             (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                        (real_inv_pos (p2_one_minus q) Hq1))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                          (real_opp (real_mult (p2_one_minus q)
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                           (real_opp real_one))))))
               (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
               (p2_tvsq sp1 sq1)).
      * exact (df2_sub_zero_r
                 (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                 (p2_one_minus q)
                 (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one))).
      * unfold df2_inst_hel_fb.
        exact (df2_unit_scale (p2_one_minus q)
                 (real_inv_pos (p2_one_minus q) Hq1) (p2_tvsq sp1 sq1)
                 (real_inv_pos_correct (p2_one_minus q) Hq1)).
    + apply (real_le_b_trans (p2_tvsq sp1 sq1)
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                          (real_plus (p2_one_minus q) (real_opp (p2_one_minus p))))
               (real_mult (p2_tvsq (p2_one_minus p) (p2_one_minus q))
                          (real_inv_pos (p2_one_minus q) Hq1))).
      * exact (dhe_gap_ge_h2term (p2_one_minus p) (p2_one_minus q) sp1 sq1
                 Hp1 Hq1 Hsp1 Hsq1 Hsp1e Hsq1e).
      * exact (dkc_gap_le_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).
  - apply real_eq_sym.
    exact (df2_ratio_sq_eq (p2_one_minus q) (p2_one_minus q) (p2_one_minus p)
             Hq1 (real_inv_pos_correct (p2_one_minus q) Hq1)
             (df2_ratio1_minus_one_eq p q Hq1)).
Qed.

(* ---- 4.4 双面复现：H² ≥ 0 经骨架 df2_j_nonneg；H² ≤_B χ² 经骨架
   df2_j_le_cs（件 3 未直列的新陈述，泛型容器新增产出） ---- *)

Lemma df2_inst_hel_le_cs_raw : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1) (div2_cs p q Hq Hq1).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1 Hspe Hsqe Hsp1e Hsq1e.
  apply (leb3_le_b_eq_r (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1)
           (df2_cs_inst q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1))
           (div2_cs p q Hq Hq1)).
  - apply (leb3_le_b_eq_l
             (real_plus
                (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
                           (real_opp (real_mult q
                                      (real_mult real_zero
                                                 (real_plus (df2_inst_chisq_s p q Hq)
                                                            (real_opp real_one))))))
                (real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                           (real_opp (real_mult (p2_one_minus q)
                                      (real_mult real_zero
                                                 (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                            (real_opp real_one)))))))
             (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1)
             (df2_cs_inst q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_mult q (df2_inst_hel_fa p q sp sq Hq))
                          (real_opp (real_mult q
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s p q Hq)
                                                           (real_opp real_one))))))(real_plus (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                          (real_opp (real_mult (p2_one_minus q)
                                     (real_mult real_zero
                                                (real_plus (df2_inst_chisq_s1 p q Hq1)
                                                           (real_opp real_one))))))(real_mult q (df2_inst_hel_fa p q sp sq Hq))
               (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))).
      * exact (df2_sub_zero_r (real_mult q (df2_inst_hel_fa p q sp sq Hq)) q
                 (real_plus (df2_inst_chisq_s p q Hq) (real_opp real_one))).
      * exact (df2_sub_zero_r
                 (real_mult (p2_one_minus q) (df2_inst_hel_fb p q sp1 sq1 Hq1))
                 (p2_one_minus q)
                 (real_plus (df2_inst_chisq_s1 p q Hq1) (real_opp real_one))).
    + exact (df2_j_le_cs q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1)
               (df2_inst_hel_fa p q sp sq Hq) (df2_inst_hel_fb p q sp1 sq1 Hq1)
               real_zero (df2_inst_hel_up p q sp sq Hp Hq Hsp Hsq Hspe Hsqe)
               (df2_inst_hel_up1 p q sp1 sq1 Hp1 Hq1 Hsp1 Hsq1 Hsp1e Hsq1e)).
  - exact (df2_inst_chisq_eq p q Hq Hq1).
Qed.

Corollary df2_inst_hel_nonneg : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b real_zero (dhe_h2 p q sp sq sp1 sq1).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1 Hspe Hsqe Hsp1e Hsq1e.
  apply (leb3_le_b_eq_r real_zero
           (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1) (dhe_h2 p q sp sq sp1 sq1)).
  - exact (df2_j_nonneg q (df2_inst_chisq_s p q Hq) (df2_inst_chisq_s1 p q Hq1)
             Hq Hq1 (df2_norm_inst p q Hp Hq Hp1 Hq1)
             (df2_inst_hel_fa p q sp sq Hq) (df2_inst_hel_fb p q sp1 sq1 Hq1)
             real_zero
             (df2_inst_hel_hlow p q sp sq Hq) (df2_inst_hel_hlow1 p q sp1 sq1 Hq1)).
  - exact (df2_inst_hel_eq p q sp sq sp1 sq1 Hq Hq1).
Qed.

Corollary df2_inst_hel_le_cs : forall (p q sp sq sp1 sq1 : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hsp : real_lt real_zero sp) (Hsq : real_lt real_zero sq)
  (Hsp1 : real_lt real_zero sp1) (Hsq1 : real_lt real_zero sq1)
  (Hspe : real_eq (real_mult sp sp) p) (Hsqe : real_eq (real_mult sq sq) q)
  (Hsp1e : real_eq (real_mult sp1 sp1) (p2_one_minus p))
  (Hsq1e : real_eq (real_mult sq1 sq1) (p2_one_minus q)),
  real_le_b (dhe_h2 p q sp sq sp1 sq1) (div2_cs p q Hq Hq1).
Proof.
  intros p q sp sq sp1 sq1 Hp Hq Hp1 Hq1 Hsp Hsq Hsp1 Hsq1 Hspe Hsqe Hsp1e Hsq1e.
  apply (leb3_le_b_eq_l (df2_inst_hel_j p q sp sq sp1 sq1 Hq Hq1)
           (dhe_h2 p q sp sq sp1 sq1) (div2_cs p q Hq Hq1)).
  - exact (df2_inst_hel_eq p q sp sq sp1 sq1 Hq Hq1).
  - exact (df2_inst_hel_le_cs_raw p q sp sq sp1 sq1 Hp Hq Hp1 Hq1
             Hsp Hsq Hsp1 Hsq1 Hspe Hsqe Hsp1e Hsq1e).
Qed.

(* ============================================================ *)
(* ---- 5. TV 泛型下界=开放申报接口（逐实例曲率常数证书位） ----        *)
(* ============================================================ *)
(*   模板契约（本件不落定理——逐实例曲率常数证书未建，如实申报，
   不留未证语句）：目标形态 TV² ≤_B c·J_f（c 为实例曲率常数），泛型容器
   需逐实例逐点证书 c·(u−1) 类差 ≤_B f(u)（Bishop 形）+ 两点拼接件：
     · χ² 实例：c := 1，逐点 (u−1)² ≤_B f(u) 即 f 自身（平方形恒等位）；
     · KL₂ 实例：c := 2（Pinsker 常数口径），逐点 2·E(s) 形证书位
       （dkc_E_nonneg 已供 0 ≤_B E，系数 2 缩放位留申报）；
     · Hellinger 实例：c := 2，见证平方形逐点证书位
       （dhe_gap_ge_h2term 已供 H 项 ≤ gap，TV² 拼接位留申报）。
   两点拼接件（p2_tvsq 口径的 TV² ≤ c·J_f 桥）为后续申报位；
   本件仅固定接口形状与证书位命名。 *)

(* ---- 99. 尾检（复活续建全量） ---- *)
Print Assumptions df2_j_nonneg.
Print Assumptions df2_j_le_cs.
Print Assumptions df2_norm_inst.
Print Assumptions df2_ratio_minus_one_eq.
Print Assumptions df2_ratio1_minus_one_eq.
Print Assumptions df2_ratio_sq_eq.
Print Assumptions df2_inst_chisq_eq.
Print Assumptions df2_inst_chisq_nonneg.
Print Assumptions df2_E_mirror_nonneg.
Print Assumptions df2_inst_kl_f_nonneg.
Print Assumptions df2_inst_kl_eq.
Print Assumptions df2_inst_kl_up.
Print Assumptions df2_inst_kl_nonneg.
Print Assumptions df2_inst_kl_le_cs.
Print Assumptions df2_inst_hel_eq.
Print Assumptions df2_inst_hel_nonneg.
Print Assumptions df2_inst_hel_le_cs.
