(* LW3ESlot.v                                                          *)
(* 使命：M3 Real 半边 E-槽接载首件（229 片D 推荐径）。e^X 的有理截断构造形    *)
(*      （E_Q := exp 部分和）＋逐点尾界（S03 exp_tail_abs 直连）＋几何合成   *)
(*      （B_N := (|X|^N/N!)·2）＋real_lt 面桥（apartness 出口使用面）＋端点  *)
(*      泛函标量 Lipschitz（尾界乘 |eps K f (node)| 界的合成机器）＋kills    *)
(*      缺口位显式前提承载组装＋锚例双向钉。加权/redesign 段（229 片C 裁决   *)
(*      前置）零触碰。                                                      *)
(* 依赖：Live_X 正本闭包 S01/S02/S03/LW0/LW1/LW2 系＋LW3ETranscendental      *)
(*      （vo 只读装载；S03 系经 Main_vo 第二 -Q，digest 谱系承 379 实测）。  *)
(* 对标：E-STAGING-LW0-GAPASUME（缺口即后续段目标形，逐字承载）；            *)
(*      E-STAGING-LW3-PROBEPIN（锚例值级 pin 走透明 exp_partial 面）；       *)
(*      E-STAGING-LW0-NOEVALIFT（桥全走库件引理，零 eval 级拼接）；          *)
(*      _tlw379 记录 §八尾款（本件使命源）。                                *)
(* 构造性：语句面全 Set（QltT/QleT' Id-bool 形、real_lt/real_eq 数据形、     *)
(*      sigT/And 数据组合）；语句与前提位零 Prop；等词面仅证明体内；         *)
(*      禁引六族零命中；提取并集数据名。                                    *)
(* 编译配方：SW2 双 export COQLIB/ROCQLIB 全字面；coqc -q -Q . ""            *)
(*      -Q Main_vo ""；cpu_guard 包裹。                                     *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW3ETranscendental.

(* ===== 1. 绝对值乘积恒等（Q 层，Z.abs_mul 直连） ===== *)

Lemma tlw383_qabs_mult : forall x y : Q, Qabs (x * y) == Qabs x * Qabs y.
Proof.
  intros [xn xd] [yn yd].
  unfold Qabs, Qmult, Qeq. cbn [Qnum Qden].
  rewrite Z.abs_mul. reflexivity.
Qed.

(* ===== 2. E_Q 截断构造形与均匀尾界形 ===== *)

(* e^X 的深度 N 有理截断（E-槽 E_Q 供给形：exp 部分和） *)
Definition tlw383_EQ (X : Q) (N : nat) : Q := exp_partial N X.

(* 深度 N 均匀尾界 B_N := (|X|^N / N!)·2（几何块收尾形） *)
Definition tlw383_geom_bound (X : Q) (N : nat) : Q :=
  (q_pow (Qabs X) N / q_fact N) * (1 + 1)%Q.

(* ===== 3. 逐点投影桥（Defined 透明构造的计算面） ===== *)

(* 常值实数的序列投影：projT1 (real_const c) n == c *)
Lemma tlw383_realconst_proj : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. unfold real_const. reflexivity. Qed.

(* 有理点实指数的逐点序列：exp_partial n X *)
Lemma tlw383_realexp_const_proj : forall (X : Q) (n : nat),
  projT1 (cauchy_real_exp (real_const X)) n == exp_partial n X.
Proof. intros X n. unfold cauchy_real_exp, real_const. reflexivity. Qed.

(* ===== 4. E-槽逐点尾界（229 片D 直连面） ===== *)

(* n ≥ N 处 |e_X(n) − E_Q| ≤ exp_tail_abs N n |X|：
   差恒等式（exp_partial_diff_tail）＋三角压制（exp_tail_abs_le）直连；
   装配走显式引理链（零 Qeq-rewrite，Qeq_trans 转换闭包一步） *)
Lemma tlw383_eslot_pointwise : forall (X : Q) (N n : nat), (N <= n)%nat ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
        (exp_tail_abs N n (Qabs X)).
Proof.
  intros X N n Hn.
  apply Qle_to_QleT'.
  apply (Qle_trans
           (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
           (Qabs (exp_tail N n X))
           (exp_tail_abs N n (Qabs X))).
  - apply qeq_le. apply (Qabs_wd _ _).
    apply (Qeq_trans _ (exp_partial n X - exp_partial N X) _).
    + reflexivity.
    + exact (exp_partial_diff_tail N n X Hn).
  - apply exp_tail_abs_le.
Qed.

(* ===== 5. 几何合成 ===== *)

(* 2|X| ≤ N+1 时 B_N 均匀压制逐点尾界（exp_tail_abs_geom2 直连；
   几何前提沿 t ≥ N 单调传递） *)
Lemma tlw383_eslot_geom : forall (X : Q) (N n : nat),
  QleT' (2 * Qabs X) (lw0_q_of_nat (N + 1)) ->
  (N <= n)%nat ->
  QleT' (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
        (tlw383_geom_bound X N).
Proof.
  intros X N n Hgeo Hn.
  apply (qleT'_trans
           (Qabs (projT1 (cauchy_real_exp (real_const X)) n - tlw383_EQ X N))
           (exp_tail_abs N n (Qabs X))
           (tlw383_geom_bound X N)).
  - apply tlw383_eslot_pointwise. exact Hn.
  - apply Qle_to_QleT'.
    apply (exp_tail_abs_geom2 (Qabs X) N n).
    + exact (QleT'_to_Qle _ _ (qabs_nonnegT X)).
    + intros t Ht.
      apply (Qle_trans (Qmult (1 + 1)%Q (Qabs X))
                       (lw0_q_of_nat (N + 1)) ((Z.of_nat (t + 1) # 1))).
      * exact (QleT'_to_Qle _ _ Hgeo).
      * unfold lw0_q_of_nat. unfold Qle. cbn [Qnum Qden].
        rewrite Z.mul_1_r. rewrite Z.mul_1_r. lia.
    + exact Hn.
Qed.

(* ===== 6. real_lt 面 E-槽桥（apartness 出口使用面） ===== *)

(* 给定 slack（B_N < eps）：实指数与截断常数的实距离 < eps。
   real_lt·real_metric·real_const 模式＝lw3_e_trans_exit 出口同款；
   内层精度位 δ := (eps − B_N)/2，半严格收尾走 qltT_half_lt_selfT。 *)
Theorem tlw383_eslot_real_lt : forall (X : Q) (N : nat) (eps : Q),
  QleT' (2 * Qabs X) (lw0_q_of_nat (N + 1)) ->
  QltT (tlw383_geom_bound X N) eps ->
  real_lt (real_metric (cauchy_real_exp (real_const X))
                        (real_const (tlw383_EQ X N)))
          (real_const eps).
Proof.
  intros X N eps Hgeo Hslack.
  assert (HBpos : QleT' 0 (tlw383_geom_bound X N)).
  { apply (qleT'_trans 0 (0 * (1 + 1)%Q) (tlw383_geom_bound X N)).
    - apply qeq_leT'. reflexivity.
    - apply (qleT'_trans (0 * (1 + 1)%Q)
               ((q_pow (Qabs X) N / q_fact N) * (1 + 1)%Q)
               (tlw383_geom_bound X N)).
      + apply qleT'_mult_compat_r.
        * unfold QleT'. vm_compute. reflexivity.
        * apply Qle_to_QleT'.
          apply (q_pow_fact_nonneg (Qabs X) N
                   (QleT'_to_Qle _ _ (qabs_nonnegT X))).
      + apply qeq_leT'. reflexivity. }
  assert (HltB : Qlt (tlw383_geom_bound X N) eps)
    by (apply QltT_to_Qlt; exact Hslack).
  assert (Heps0 : Qlt 0 eps)
    by (apply (Qle_lt_trans 0 (tlw383_geom_bound X N) eps);
        [exact (QleT'_to_Qle _ _ HBpos) | exact HltB]).
  (* 正差严格性：QltT 0 (eps − B_N)（plus-compat＋双侧 qeq 收尾，全库件） *)
  assert (HdB0T : QltT 0 (eps - tlw383_geom_bound X N)).
  { assert (H : QltT (tlw383_geom_bound X N + - (tlw383_geom_bound X N))
                     (eps + - (tlw383_geom_bound X N))).
    { apply (qltT_plus_leT'_ltT (tlw383_geom_bound X N) eps
               (- (tlw383_geom_bound X N)) (- (tlw383_geom_bound X N))).
      - exact Hslack.
      - apply qleT'_refl. }
    assert (H2 : QltT 0 (eps + - (tlw383_geom_bound X N))).
    { apply (qltT_eq_compat_l (tlw383_geom_bound X N + - (tlw383_geom_bound X N))
               0 (eps + - (tlw383_geom_bound X N))).
      - ring.
      - exact H. }
    apply (qltT_eq_compat_r (eps + - (tlw383_geom_bound X N))
             (eps - tlw383_geom_bound X N) 0).
    - ring.
    - exact H2. }
  exists (((eps - tlw383_geom_bound X N) / 2)%Q). split.
  - apply (qltT_div_pos (eps - tlw383_geom_bound X N) 2).
    + exact HdB0T.
    + exact qltT_0_2.
  - exists N. intros n HnN.
    (* 逐点界：|Δn| ≤ B_N *)
    assert (Hpd : QleT' (Qabs (exp_partial n X - tlw383_EQ X N))
                        (tlw383_geom_bound X N)).
    { exact (tlw383_eslot_geom X N n Hgeo (NatLe_drop N n HnN)). }
    (* 目标右位换算到计算面（投影体 Defined 透明，转换闭包） *)
    apply (qltT_eq_compat_r
             (eps - Qabs (exp_partial n X - tlw383_EQ X N))
             (projT1 (real_const eps) n
              - projT1 (real_metric (cauchy_real_exp (real_const X))
                         (real_const (tlw383_EQ X N))) n)
             ((eps - tlw383_geom_bound X N) / 2)).
    + reflexivity.
    + apply (qltT_leT'_ltT ((eps - tlw383_geom_bound X N) / 2)
               (eps - tlw383_geom_bound X N)
               (eps - Qabs (exp_partial n X - tlw383_EQ X N))).
      * apply (qltT_half_lt_selfT (eps - tlw383_geom_bound X N)).
        exact HdB0T.
      * apply Qle_to_QleT'.
        assert (Hneg : Qle (- (tlw383_geom_bound X N))
                          (- Qabs (exp_partial n X - tlw383_EQ X N)))
          by (apply (Qopp_le_compat _ _ (QleT'_to_Qle _ _ Hpd))).
        apply (Qle_trans (eps - tlw383_geom_bound X N)
                           (eps + - (tlw383_geom_bound X N))
                           (eps + - Qabs (exp_partial n X - tlw383_EQ X N))).
        -- apply qeq_imp_qle. ring.
        -- apply (Qle_trans (eps + - (tlw383_geom_bound X N))
                       (eps + - Qabs (exp_partial n X - tlw383_EQ X N))
                       (eps - Qabs (exp_partial n X - tlw383_EQ X N))).
           ++ apply (Qplus_le_compat eps eps (- (tlw383_geom_bound X N))
                        (- Qabs (exp_partial n X - tlw383_EQ X N)));
                [apply Qle_refl | exact Hneg].
           ++ apply qeq_imp_qle. apply (Qeq_sym _ _). ring.
Qed.

(* ===== 7. E-槽组装（kills 缺口位显式前提承载） ===== *)

(* kills 缺口位（E-槽余程施工目标形，逐字）：
   ∃M, 2|X| ≤ M+1 ∧ B_M < eps —— 阶乘压制的 eps-实例化，
   后续段闭合后本组装前提位减一。 *)
Theorem tlw383_eslot_carrier : forall (X : Q) (eps : Q),
  QltT 0 eps ->
  (sigT (fun M : nat =>
     And (QleT' (2 * Qabs X) (lw0_q_of_nat (M + 1)))
         (QltT (tlw383_geom_bound X M) eps))) ->
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const eps)).
Proof.
  intros X eps Heps0 Hkills.
  destruct Hkills as [M [Hgeo Hslack]].
  exists M. apply tlw383_eslot_real_lt; assumption.
Qed.

(* 实侧装配：p(e)=0 前件逐字携带（适用域闸；下游 redesign 段使用），
   节点位 X = −node(S nodecount)。 *)
Theorem tlw383_eslot_realcarrier : forall (p : zpoly) (Nn : nat) (eps : Q),
  real_eq (lw3_evalr p lw3_e) real_zero ->
  QltT 0 eps ->
  (sigT (fun M : nat =>
     And (QleT' (2 * Qabs (- lw2_node (Datatypes.S (lw3_nodecount p Nn))))
                 (lw0_q_of_nat (M + 1)))
         (QltT (tlw383_geom_bound
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M) eps))) ->
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M)))
            (real_const eps)).
Proof.
  intros p Nn eps Hpzero Heps0 Hkills.
  exact (tlw383_eslot_carrier
          (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) eps Heps0 Hkills).
Qed.

(* ===== 8. 端点泛函标量 Lipschitz（尾界乘 |eps K f (node)| 界合成机器） ===== *)

(* |E₁ − E₂| ≤ T、|eps_K f(X)| ≤ C ⟹ |exp_L(E₁) − exp_L(E₂)| ≤ T·C：
   机器对标量 E 的 Lipschitz——E-槽截断替换精确标量的偏差合成件 *)
Lemma tlw383_eslot_machine_lip : forall (E1 E2 : Q) (K : nat) (f : QPoly)
  (X T C : Q),
  QleT' (Qabs (E1 - E2)) T ->
  QleT' (Qabs (qpoly_eval (lw2_eps K f) X)) C ->
  QleT' (Qabs (lw2_exp_L E1 K f X - lw2_exp_L E2 K f X)) (T * C).
Proof.
  intros E1 E2 K f X T C HT HC.
  assert (HT0 : QleT' 0 T).
  { apply (qleT'_trans 0 (Qabs (E1 - E2)) T).
    - apply qabs_nonnegT.
    - exact HT. }
  assert (HT2 : QleT' (Qabs (E2 - E1)) T).
  { apply (qleT'_trans (Qabs (E2 - E1)) (Qabs (E1 - E2)) T).
    - apply qeq_leT'. exact (q_abs_minus_sym E2 E1).
    - exact HT. }
  assert (Hr : lw2_exp_L E1 K f X - lw2_exp_L E2 K f X
               == (E2 - E1) * qpoly_eval (lw2_eps K f) X).
  { unfold lw2_exp_L. ring. }
  apply (qleT'_trans (Qabs (lw2_exp_L E1 K f X - lw2_exp_L E2 K f X))
             (Qabs ((E2 - E1) * qpoly_eval (lw2_eps K f) X)) (T * C)).
  - apply qeq_leT'. apply (Qabs_wd _ _). exact Hr.
  - apply (qleT'_trans (Qabs ((E2 - E1) * qpoly_eval (lw2_eps K f) X))
             (Qabs (E2 - E1) * Qabs (qpoly_eval (lw2_eps K f) X)) (T * C)).
    + apply qeq_leT'.
      exact (tlw383_qabs_mult (E2 - E1) (qpoly_eval (lw2_eps K f) X)).
    + apply (qleT'_trans (Qabs (E2 - E1) * Qabs (qpoly_eval (lw2_eps K f) X))
               (T * Qabs (qpoly_eval (lw2_eps K f) X)) (T * C)).
      * apply qleT'_mult_compat_r; [apply qabs_nonnegT | exact HT2].
      * apply qleT'_mult_compat_l; [exact HT0 | exact HC].
Qed.

(* ===== 9. 锚例双向钉 ===== *)

(* 锚例值级 pin：节点 X = −node 2（|X| = 2），深度 N = 5 的均匀尾界
   B_5 = (2^5/5!)·2 = 8/15 < 1（透明 exp_partial 面值级，PROBEPIN 口径） *)
Theorem tlw383_eslot_anchor :
  QltT (tlw383_geom_bound
          (- lw2_node (Datatypes.S (Datatypes.S O)))
          (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))
       (1 # 1)%Q.
Proof.
  unfold QltT, Qlt_bool, tlw383_geom_bound, lw2_node.
  vm_compute. reflexivity.
Qed.

(* 锚例实侧见证产出：上述 slack 下 e^{-2} 与深度-5 截断的实距离 < 1
   （tlw379_p2inst 同款产出件口径——E-槽 real_lt 面见证实际产出） *)
Theorem tlw383_eslot_anchor_lt :
  real_lt (real_metric
             (cauchy_real_exp
                (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
             (real_const (tlw383_EQ
                (- lw2_node (Datatypes.S (Datatypes.S O)))
                (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))))
          (real_const (1 # 1)%Q).
Proof.
  apply (tlw383_eslot_real_lt
          (- lw2_node (Datatypes.S (Datatypes.S O)))
          (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))
          (1 # 1)%Q).
  - unfold QleT', Qle_bool, lw2_node, lw0_q_of_nat, Qabs.
    cbn [Qnum Qden]. vm_compute. reflexivity.
  - apply tlw383_eslot_anchor.
Qed.

(* ===== 10. 提取检核（G3 数据名并集） ===== *)

From Stdlib Require Import Extraction.
Separate Extraction tlw383_EQ tlw383_geom_bound.
