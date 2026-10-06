(* ===================================================================== *)
(*  abl_ln2_conv_core.v —— ln2 逼近链·算术卷积基建件                          *)
(*  模块名：abl_ln2_conv_core.                                            *)
(*  使命: 有理逼近下界的卷积核引理面（三肢乘积合成的算术半边），三层：       *)
(*        【层1·分离核】任意两个互异有理数的间隔下界——整数 heart           *)
(*        （|p1·q2 − p2·q1| ≥ 1 ⟹ 1 ≤ |p1/q1 − p2/q2|·q1·q2）与除式形      *)
(*        cc_sep_div（1/(q1·q2) ≤ |p1/q1 − p2/q2|）；                      *)
(*        【层2·显式带窗】Bernoulli 下界 1 + n/4 ≤ (5/4)ⁿ、底互换幂恒等式   *)
(*        （(4/5)ⁿ == ((5/4)ⁿ)⁻¹）与闭式带窗 (4/5)^{8q} < 1/(2q)（q ≥ 1）   *)
(*        ——衰减与带窗指标全显式（无存在窗）；数值锚 q=1 处 (4/5)^8 < 1/2；  *)
(*        【层3·两歧卷积引擎】对基准实数 X 与整系数线性形式 |a·X − b|：      *)
(*        上界肢（≤ (4/5)ⁿ）、载体下界肢（clo_n ≤ 线）、载体正性（0 < clo_n、 *)
(*        0 < |A_n|）四前提下，对一切有理数 u/v 显式给出正分离常数 c 与     *)
(*        终归指标 K，使 c ≤ |u/v − x_k| 对 k ≥ K 成立（Z.eq_dec 可判定     *)
(*        两歧分：命支 c := (clo_{n₀}/2)·|A_{n₀}|⁻¹ 沿命中恒等式             *)
(*        |a·x − b| = |a|·|x − u/v|；否支 c := ((1/v − (4/5)^{n₀})/2)·      *)
(*        |A_{n₀}|⁻¹ 沿三角劈分与整数 heart；带窗指标 n₀ := 8·⌊v⌋ 闭式）。   *)
(*        两歧常数皆封闭 Q 项。                                             *)
(*  依赖: Stdlib QArith/Qabs/Arith/ZArith/Lia；S01_BaseRing S02_Cauchy-    *)
(*        Complete S03_QExp；Ln2Bridge（ln2b_le_pt_slack 终归 slack 形、     *)
(*        ln2b_line_q 通分恒等式、ln2b_div_lt_of 除正除式桥）；池内拷贝件    *)
(*        abl_ln2_tail_bound（lnt_leT'_eq_r 传送面）。                      *)
(*  对标: Ln2Bridge ln2b_delta_of_supply 的 δ 提取形（其窗指标经衰减件      *)
(*        存在式给出）；本件差异三点：窗指标闭式化（Bernoulli 显式公式      *)
(*        n₀ := 8·⌊v⌋）、引擎对任意基准实数 X 通用（不锚 ln2i_x 特定载体）、  *)
(*        分离核以一般两有理数形独立成件（除式形可单独使用）。工艺注记：     *)
(*        Qabs 与 QleT' 无 Qeq-morphism 实例，凡 Qeq 等式在其内部一律走     *)
(*        顶层 Qabs_wd/lnt_leT'_eq_l/r 传送件，禁子项位 rewrite。           *)
(*  构造性: 纯构造性、零承认件；语句面全 Set（sigT/S01.And/QeqT/QleT'/     *)
(*        QltT/real_le），Qeq/Qle/Qlt 仅 Prop 推理面作脚手架（池件同款      *)
(*        纪律）；两歧分走 Z.eq_dec 可判定分（零 LPO）；见证全显式          *)
(*        （分离常数 c 与指标 K 均封闭 Q/nat 项）；文尾 Print Assumptions   *)
(*        全列取证＋Separate Extraction 验证。                              *)
(*  编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*        ulimit -s 65532 && nice -19 rocq c -native-compiler no           *)
(*        -Q vo_local_world_unified_0930 "" 本件（独占池 ln2_theta_total/， *)
(*        链序：abl_ln2_tail_bound 先编，道闸≤1 单道串行）。                *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs Setoid Morphisms
  Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import UpReqLn2Irrational UpReqIrrationalCriterion.
Require Import Ln2Bridge.
Require Import abl_ln2_tail_bound.

Open Scope nat_scope.

(* Q 层未注册环结构只注册域结构：Qeq 面恒等式一律走 field（Q 只注册
   Add Field 未注册 Add Ring——承 UpReqMixLogA 的勘录口径） *)
Ltac cc_zring := field.
Ltac cc_zring_goal := field.

(* ============================================================ *)
(* §0 整数 heart 与通分恒等式                                              *)
(* ============================================================ *)

(* 整数 heart：非零整数 w 的一分底 |w| ≥ 1（QleT' 面） *)
Lemma cc_one_le_zabs : forall w : Z, w <> 0%Z -> QleT' 1%Q (Qabs (w # 1)%Q).
Proof.
  intros w Hw. apply Qle_to_QleT'.
  destruct w as [| p | p]; cbn [Qabs] in *;
    unfold Qle; cbn [Qnum Qden]; lia.
Qed.

(* 通分恒等式：(p1/q1 − p2/q2)·q1·q2 == p1·q2 − p2·q1（整数分子收单） *)
Lemma cc_diff_cross : forall (p1 p2 : Z) (q1 q2 : positive),
  (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q)
     * ((Z.pos q2 # 1)%Q))%Q
  == (((p1 * Z.pos q2 - p2 * Z.pos q1) # 1)%Q).
Proof.
  intros p1 p2 q1 q2.
  unfold Qmult, Qminus, Qplus, Qopp, Qeq. cbn [Qnum Qden Pos.mul]. lia.
Qed.

(* ============================================================ *)
(* §1 层1·分离核：互异有理数的间隔下界                                       *)
(* ============================================================ *)

(* ★ 乘积形：p1·q2 ≠ p2·q1 ⟹ 1 ≤ |p1/q1 − p2/q2|·q1·q2 *)
Theorem cc_sep_core : forall (p1 p2 : Z) (q1 q2 : positive),
  (p1 * Z.pos q2 <> p2 * Z.pos q1)%Z ->
  QleT' 1%Q (Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                     * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))%Q).
Proof.
  intros p1 p2 q1 q2 Hd.
  apply (lnt_leT'_eq_r 1%Q
           (Qabs (((p1 * Z.pos q2 - p2 * Z.pos q1) # 1)%Q))
           (Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                    * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q)))%Q).
  - apply Qeq_sym. apply Qabs_wd. apply cc_diff_cross.
  - apply cc_one_le_zabs. intro E. apply Hd. lia.
Qed.

(* ★ 除式形：p1·q2 ≠ p2·q1 ⟹ 1/(q1·q2) ≤ |p1/q1 − p2/q2| *)
Theorem cc_sep_div : forall (p1 p2 : Z) (q1 q2 : positive),
  (p1 * Z.pos q2 <> p2 * Z.pos q1)%Z ->
  QleT' (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
        (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q).
Proof.
  intros p1 p2 q1 q2 Hd.
  pose proof (QleT'_to_Qle _ _ (cc_sep_core p1 p2 q1 q2 Hd)) as H1.
  (* 换形：|Δ·q1#1·q2#1| == |Δ|·(q1·q2)#1（顶层 Qeq 构造） *)
  assert (Habs_eq : Qabs (((p1 # q1)%Q - (p2 # q2)%Q)
                            * ((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))
                    == Qabs ((p1 # q1)%Q - (p2 # q2)%Q)
                         * ((Z.pos (q1 * q2)) # 1)%Q).
  { transitivity ((Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q))
                     * Qabs ((Z.pos q2 # 1)%Q))%Q).
    - apply Qabs_Qmult.
    - assert (E12 : Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q))
                    == Qabs ((p1 # q1)%Q - (p2 # q2)%Q)
                         * Qabs ((Z.pos q1 # 1)%Q))
        by apply Qabs_Qmult.
      assert (E1 : Qabs ((Z.pos q1 # 1)%Q) == ((Z.pos q1 # 1)%Q)).
      { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
      assert (E2 : Qabs ((Z.pos q2 # 1)%Q) == ((Z.pos q2 # 1)%Q)).
      { apply Qabs_pos. unfold Qle. cbn [Qnum Qden]. lia. }
      assert (Eq : (((Z.pos q1 # 1)%Q) * ((Z.pos q2 # 1)%Q))%Q
                   == ((Z.pos (q1 * q2)) # 1)%Q)
        by (unfold Qmult, Qeq; cbn [Qnum Qden Pos.mul]; lia).
      rewrite E12, E1, E2. rewrite <- Qmult_assoc, Eq. reflexivity. }
  (* Qle 假设位禁 rewrite——经 Qle_trans 顶层换形 *)
  assert (H1b : Qle 1%Q (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                             * ((Z.pos (q1 * q2)) # 1)%Q)).
  { apply (Qle_trans 1%Q
             (Qabs (((p1 # q1)%Q - (p2 # q2)%Q) * ((Z.pos q1 # 1)%Q)
                      * ((Z.pos q2 # 1)%Q)))%Q).
    - exact H1.
    - apply qeq_le. exact Habs_eq. }
  (* 正分母单调消去：1 ≤ |Δ|·C ⟹ C⁻¹ ≤ |Δ|（正 C 上乘 C⁻¹ 后消去，无拆分） *)
  assert (HC0 : Qlt 0 ((Z.pos (q1 * q2)) # 1)%Q).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (HCinvL : ((Z.pos (q1 * q2)) # 1)%Q
                     * Qinv ((Z.pos (q1 * q2)) # 1)%Q == 1%Q)
    by (apply Qmult_inv_r; apply lnt_qneq_of_eq0; exact HC0).
  assert (HQinvC0 : QltT 0 (Qinv ((Z.pos (q1 * q2)) # 1)%Q)).
  { apply Qlt_to_QltT. apply Qinv_lt_0_compat. exact HC0. }
  assert (Hle2 : QleT' ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
                       ((Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                          * (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                               * ((Z.pos (q1 * q2)) # 1)%Q))%Q).
  { apply (qleT'_mult_compat_l 1%Q
             (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                * ((Z.pos (q1 * q2)) # 1)%Q)
             (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
             HQinvC0 (Qle_to_QleT' _ _ H1b)). }
  apply (lnt_leT'_eq_l ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
           (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
           (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
  - apply Qmult_1_r.
  - apply (lnt_leT'_eq_r ((Qinv ((Z.pos (q1 * q2)) # 1)%Q) * 1%Q)
             ((Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                * (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q
                     * ((Z.pos (q1 * q2)) # 1)%Q))%Q
             (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
    + rewrite Qmult_assoc. rewrite (Qmult_comm (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                                         (Qabs ((p1 # q1)%Q - (p2 # q2)%Q)%Q)).
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (Qinv ((Z.pos (q1 * q2)) # 1)%Q)
                                 ((Z.pos (q1 * q2)) # 1)%Q).
      rewrite HCinvL. apply Qmult_1_r.
    + exact Hle2.
Qed.

(* ============================================================ *)
(* §2 层2·显式带窗：Bernoulli 下界与 (4/5) 幂的闭式窗                        *)
(* ============================================================ *)

(* Bernoulli 下界：1 + n/4 ≤ (5/4)ⁿ（QleT' 面归纳） *)
Lemma cc_bernoulli : forall n : nat,
  QleT' (((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q)%Q) (q_pow (5 # 4)%Q n).
Proof.
  induction n as [| n IH].
  - cbn [q_pow]. change (Z.of_nat 0) with 0%Z.
    apply qeq_leT'.
    unfold Qeq, Qnum, Qmult, Qplus, Qminus, Qopp.
    cbn [Qnum Qden Pos.mul]. ring.
  - cbn [Nat.add]. cbn [q_pow].
    apply (qleT'_trans
             (((1 # 1)%Q + (Z.of_nat (Datatypes.S n) # 1)%Q * (1 # 4)%Q)%Q)
             (((5 # 4)%Q * ((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q))%Q)
             (((5 # 4)%Q * q_pow (5 # 4)%Q n)%Q)).
    + apply Qle_to_QleT'.
      replace (Z.of_nat (Datatypes.S n)) with (Z.of_nat n + 1)%Z
        by (rewrite Nat2Z.inj_succ; lia).
      unfold Qle.
      cbn [Qnum Qden Qmult Qplus Qminus Qopp Qinv Qdiv Pos.mul].
      lia.
    + assert (Hth : QleT' 0 (5 # 4)%Q).
      { apply qltT_leT'. apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
      apply (qleT'_mult_compat_l
               (((1 # 1)%Q + (Z.of_nat n # 1)%Q * (1 # 4)%Q)%Q)
               (q_pow (5 # 4)%Q n) (5 # 4)%Q Hth IH).
Qed.

(* 底互换幂恒等式：(4/5)ⁿ == ((5/4)ⁿ)⁻¹（归纳＋Qinv 分配） *)
Lemma cc_qpow_swap : forall n : nat,
  q_pow (4 # 5)%Q n == Qinv (q_pow (5 # 4)%Q n).
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qinv_mult_distr. rewrite IH.
    reflexivity.
Qed.

(* 2 幂折算桥：(8·q)·(1/4) == 2·q（带窗指标换算的数域账） *)
Lemma cc_q8_index : forall q : nat,
  ((Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q)%Q == ((Z.of_nat (2 * q) # 1)%Q).
Proof.
  intro q. unfold Qmult, Qeq. cbn [Qnum Qden Pos.mul].
  rewrite (Nat2Z.inj_mul 8 q), (Nat2Z.inj_mul 2 q). nia.
Qed.

(* 除式一分化：1/z == z⁻¹（z 整底） *)
Lemma cc_div1_inv : forall z : Z,
  ((1 # 1)%Q / ((z # 1)%Q))%Q == Qinv ((z # 1)%Q).
Proof.
  intro z. unfold Qdiv.
  destruct z as [| p | p]; cbn [Qnum Qden Qinv Qmult];
    unfold Qeq, Qmult; cbn [Qnum Qden Pos.mul]; lia.
Qed.

(* QltT 沿 Qeq 的左右传送（Id 面无 Proper 实例——池件同款微件） *)
Lemma cc_qltT_transfer_l : forall x y z : Q, Qeq x y -> QltT y z -> QltT x z.
Proof.
  intros x y z Hxy Hyz. apply Qlt_to_QltT.
  apply (Qle_lt_trans x y z).
  - apply qeq_le. exact Hxy.
  - apply QltT_to_Qlt. exact Hyz.
Qed.

Lemma cc_qltT_transfer_r : forall x y z : Q, Qeq y z -> QltT x y -> QltT x z.
Proof.
  intros x y z Hyz Hxy. apply Qlt_to_QltT.
  apply (Qlt_le_trans x y z).
  - apply QltT_to_Qlt. exact Hxy.
  - apply qeq_le. exact Hyz.
Qed.

(* ★ Qinv 注入：0 < u、0 < v 且 v⁻¹ == u⁻¹ ⟹ v == u（两侧乘 v·u 后
    双侧正分母消去；Q 层未注册环结构，全程零 ring，纯 Qmult 重排） *)
Lemma cc_qinv_inj : forall u v : Q,
  Qlt 0 u -> Qlt 0 v -> Qinv v == Qinv u -> u == v.
Proof.
  intros u v Hu0 Hv0 h.
  assert (Ev : (Qinv v * v)%Q == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hv0).
  assert (Eu : (Qinv u * u)%Q == 1%Q)
    by (apply lnt_qinv_mul_cancel; apply lnt_qneq_of_eq0; exact Hu0).
  assert (Hstep : (Qinv v * (v * u))%Q == (Qinv u * (v * u))%Q)
    by (rewrite h; reflexivity).
  apply (Qeq_trans u (Qinv v * (v * u))%Q v).
  - apply (Qeq_trans u (1 * u)%Q (Qinv v * (v * u))%Q).
    + apply Qeq_sym. apply Qmult_1_l.
    + apply (Qeq_trans (1 * u)%Q ((Qinv v * v) * u)%Q (Qinv v * (v * u))%Q).
      * rewrite <- Ev. reflexivity.
      * rewrite <- Qmult_assoc. reflexivity.
  - apply (Qeq_trans (Qinv v * (v * u))%Q (Qinv u * (v * u))%Q v).
    + exact Hstep.
    + apply (Qeq_trans (Qinv u * (v * u))%Q (Qinv u * (u * v))%Q v).
      * rewrite (Qmult_comm v u). reflexivity.
      * rewrite Qmult_assoc. rewrite Eu. apply Qmult_1_l.
Qed.

(* ★ 严格倒数反序：0 < u、u < v ⟹ v⁻¹ < u⁻¹（全 Prop 层：非严支经 Qinv
    注入与 u < v 的自反性矛盾，零 Prop→Set 消取） *)
Lemma cc_qinv_lt : forall u v : Q, Qlt 0 u -> QltT u v -> QltT (Qinv v) (Qinv u).
Proof.
  intros u v Hu Hv. apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hv) as Hltuv.
  assert (Hv0 : Qlt 0 v).
  { apply (Qlt_trans 0%Q u v).
    - exact Hu.
    - exact Hltuv. }
  assert (Hle : Qle (Qinv v) (Qinv u)).
  { apply ln2i_inv_le.
    - exact Hu.
    - apply Qlt_le_weak. exact Hltuv. }
  destruct (Qle_lt_or_eq (Qinv v) (Qinv u) Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso. apply (Qlt_irrefl v).
    assert (Huv : u == v).
    { apply cc_qinv_inj.
      - exact Hu.
      - exact Hv0.
      - exact Heq. }
    rewrite Huv in Hltuv. exact Hltuv.
Qed.

(* ★ 闭式带窗：1 ≤ q ⟹ (4/5)^{8q} < 1/(2q)——衰减与带窗指标的显式公式 *)
Theorem cc_band : forall q : nat, 1 <= q ->
  QltT (q_pow (4 # 5)%Q (8 * q))
       (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q).
Proof.
  intros q Hq.
  pose proof (QleT'_to_Qle _ _ (cc_bernoulli (8 * q))) as Hb.
  (* Qle 假设位禁 rewrite——经 Qle_trans 顶层换形（指标账 cc_q8_index） *)
  assert (Hinner : ((1 # 1)%Q + (Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q)%Q
                   == ((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q).
  { rewrite cc_q8_index. reflexivity. }
  assert (Hb2 : Qle (((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q)
                    (q_pow (5 # 4)%Q (8 * q))).
  { apply (Qle_trans _ (((1 # 1)%Q + (Z.of_nat (8 * q) # 1)%Q * (1 # 4)%Q))%Q).
    - apply qeq_le. apply Qeq_sym. exact Hinner.
    - exact Hb. }
  assert (Hstep : QltT ((Z.of_nat (2 * q) # 1)%Q)
                       (((1 # 1)%Q + (Z.of_nat (2 * q) # 1)%Q)%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden Qplus]. lia. }
  assert (HbandP : QltT ((Z.of_nat (2 * q) # 1)%Q)
                        (q_pow (5 # 4)%Q (8 * q)))
    by (apply (qltT_leT'_ltT _ _ _ Hstep (Qle_to_QleT' _ _ Hb2))).
  assert (Hu0 : Qlt 0 ((Z.of_nat (2 * q) # 1)%Q)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Ediv : ((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q
                 == Qinv ((Z.of_nat (2 * q) # 1)%Q))
    by (apply cc_div1_inv).
  pose proof (cc_qinv_lt ((Z.of_nat (2 * q) # 1)%Q)
              (q_pow (5 # 4)%Q (8 * q)) Hu0 HbandP) as Hinv.
  apply (cc_qltT_transfer_l (q_pow (4 # 5)%Q (8 * q))
           (Qinv (q_pow (5 # 4)%Q (8 * q)))
           (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q)).
  - apply cc_qpow_swap.
  - apply (cc_qltT_transfer_r (Qinv (q_pow (5 # 4)%Q (8 * q)))
             (Qinv ((Z.of_nat (2 * q) # 1)%Q))
             (((1 # 1)%Q / ((Z.of_nat (2 * q) # 1)%Q))%Q)).
    + apply Qeq_sym. apply Ediv.
    + exact Hinv.
Qed.

(* 倒数对偶：(v#1)⁻¹ == (1#v)（正分母符号拆分） *)
Lemma cc_qinv_pair : forall v : positive, Qinv ((Z.pos v # 1)%Q) == (1 # v)%Q.
Proof.
  intro v. cbn [Qinv].
  destruct v; reflexivity.
Qed.

(* ★ 正分母带窗：θ^{8·⌊v⌋} < 1/v（引擎直用形——Bernoulli 1+2⌊v⌋ ≥ v 的
    严格化链：v ≤ 2⌊v⌋ < 1 + 2⌊v⌋ ≤ (5/4)^{8⌊v⌋}，倒数反序即得） *)
Theorem cc_band_v : forall v : positive,
  QltT (q_pow (4 # 5)%Q (8 * Z.to_nat (Z.pos v))) ((1 # v)%Q).
Proof.
  intro v.
  assert (Hv1 : (1 <= Z.to_nat (Z.pos v))%nat).
  { destruct (Z.to_nat (Z.pos v)) as [| m] eqn:E; [| lia].
    apply (f_equal Z.of_nat) in E.
    rewrite Z2Nat.id in E by lia.
    pose proof (Pos2Z.is_pos v). lia. }
  pose proof (QleT'_to_Qle _ _ (cc_bernoulli (8 * Z.to_nat (Z.pos v)))) as Hb.
  assert (Hinner : ((Z.of_nat (8 * Z.to_nat (Z.pos v)) # 1)%Q * (1 # 4)%Q)%Q
                   == ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)).
  { rewrite cc_q8_index. reflexivity. }
  assert (Hb2 : QleT' ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)
                       (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v)))).
  { apply Qle_to_QleT'.
    apply (Qle_trans ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)
             (((1 # 1)%Q + (Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)%Q)).
    - unfold Qle. cbn [Qnum Qden Qmult Qplus]. lia.
    - apply (Qle_trans _ (((1 # 1)%Q
                             + (Z.of_nat (8 * Z.to_nat (Z.pos v)) # 1)%Q
                                * (1 # 4)%Q))%Q).
      + apply qeq_le. rewrite <- Hinner. reflexivity.
      + exact Hb. }
  assert (Hstep : QltT ((Z.pos v # 1)%Q)
                        ((Z.of_nat (2 * Z.to_nat (Z.pos v)) # 1)%Q)).
  { apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden].
    assert (Hz := Z2Nat.id (Z.pos v) ltac:(lia)).
    lia. }
  assert (HbandP : QltT ((Z.pos v # 1)%Q)
                         (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
    by (apply (qltT_leT'_ltT _ _ _ Hstep Hb2)).
  assert (Hu0 : Qlt 0 ((Z.pos v # 1)%Q)).
  { unfold Qlt. cbn [Qnum Qden]. lia. }
  pose proof (cc_qinv_lt ((Z.pos v # 1)%Q)
              (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v)))
              Hu0 HbandP) as Hinv.
  apply (cc_qltT_transfer_l (q_pow (4 # 5)%Q (8 * Z.to_nat (Z.pos v)))
           (Qinv (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
           ((1 # v)%Q)).
  - apply cc_qpow_swap.
  - apply (cc_qltT_transfer_r (Qinv (q_pow (5 # 4)%Q (8 * Z.to_nat (Z.pos v))))
             (Qinv ((Z.pos v # 1)%Q))
             ((1 # v)%Q)).
    + apply cc_qinv_pair.
    + exact Hinv.
Qed.

(* 数值锚：q = 1 处 (4/5)^8 < 1/2（vm_compute 验证） *)
Theorem cc_band_anchor1 : QltT (q_pow (4 # 5)%Q 8) ((1 # 2)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §3 层3·两歧卷积引擎                                                       *)
(* ============================================================ *)

(* 整系数线性形式的绝对值实数：|a·X − b|（对任意基准实数 X） *)
Definition cc_line (X : Real) (a b : Z) : Real :=
  real_abs (real_plus (real_mult (real_const ((a # 1)%Q)) X)
                      (real_opp (real_const ((b # 1)%Q)))).

(* 投影读出：line 的第 k 读数 = |a·x_k − b| *)
Lemma cc_line_pt : forall (X : Real) (a b : Z) (k : nat),
  projT1 (cc_line X a b) k
  == Qabs (((a # 1)%Q * projT1 X k - ((b # 1)%Q))%Q).
Proof.
  intros X a b k. unfold cc_line.
  rewrite real_abs_proj, real_plus_proj, real_mult_proj, real_opp_proj,
          real_const_proj.
  reflexivity.
Qed.

(* 减法右分配：x·y − x·z == x·(y − z)（Q 值构造形拆分，Z 半环算术） *)
Lemma cc_mult_minus_distr : forall x y z : Q,
  (x * y - x * z)%Q == (x * (y - z))%Q.
Proof. intros. field. Qed.

(* 命中恒等式：a·q == b ⟹ |a·t − b| == |a|·|t − q|（两处消去的核） *)
Lemma cc_hit_abs : forall (a b : Z) (t q : Q),
  (((a # 1)%Q * q - ((b # 1)%Q))%Q == 0%Q) ->
  Qabs (((a # 1)%Q * t - ((b # 1)%Q))%Q)
  == Qabs ((a # 1)%Q) * Qabs ((t - q)%Q)%Q.
Proof.
  intros a b t q Hhit.
  assert (HB : ((b # 1)%Q) == ((a # 1)%Q * q)%Q).
  { apply Qeq_sym.
    apply (Qeq_trans ((a # 1)%Q * q)%Q
                     (((a # 1)%Q * q - ((b # 1)%Q)) + ((b # 1)%Q))%Q
                     ((b # 1)%Q)).
    - field.
    - rewrite Hhit. apply Qplus_0_l. }
  transitivity (Qabs ((a # 1)%Q * (t - q)%Q)).
  - apply Qabs_wd.
    apply (Qeq_trans ((a # 1)%Q * t - ((b # 1)%Q))%Q
                     ((a # 1)%Q * t - (a # 1)%Q * q)%Q
                     ((a # 1)%Q * (t - q)%Q)).
    + rewrite HB. reflexivity.
    + apply cc_mult_minus_distr.
  - rewrite Qabs_Qmult. reflexivity.
Qed.

(* 三角劈分：|a·q − b| ≤ |a|·|q − x_k| + |a·x_k − b| *)
Lemma cc_tri : forall (X : Real) (a b : Z) (q : Q) (k : nat),
  Qle (Qabs (((a # 1)%Q * q - ((b # 1)%Q))%Q))
      (Qabs ((a # 1)%Q) * Qabs ((q - projT1 X k)%Q)
       + projT1 (cc_line X a b) k)%Q.
Proof.
  intros X a b q k.
  assert (Hsplit : (((a # 1)%Q * q - ((b # 1)%Q))%Q
                    == ((a # 1)%Q * (q - projT1 X k)
                        + ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q)) by cc_zring.
  apply (Qle_trans _ (Qabs ((a # 1)%Q * (q - projT1 X k)
                             + ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q)).
  - apply qeq_le. apply Qabs_wd. exact Hsplit.
  - pose proof (Qabs_triangle ((a # 1)%Q * (q - projT1 X k))
                  ((a # 1)%Q * projT1 X k - ((b # 1)%Q))) as HT.
    assert (HE : (Qabs ((a # 1)%Q * (q - projT1 X k))
                  + Qabs ((a # 1)%Q * projT1 X k - ((b # 1)%Q)))%Q
                 == (Qabs ((a # 1)%Q) * Qabs ((q - projT1 X k)%Q)
                     + projT1 (cc_line X a b) k)%Q).
    { rewrite Qabs_Qmult. rewrite <- (cc_line_pt X a b k). reflexivity. }
    exact (Qle_trans _ _ _ HT (qeq_le _ _ HE)).
Qed.

(* ★ 两歧卷积引擎：四前提（上界肢/载体下界肢/载体正性/系数正性）下，对一切
    有理数 u/v 显式给出正分离常数 c 与终归指标 K，使 c ≤ |u/v − x_k|（k ≥ K）。
    命支（u·A_n₀ == v·B_n₀，n₀ := 8·⌊v⌋）：c := (clo_{n₀}/2)·|A_{n₀}|⁻¹；
    否支：c := ((1/v − (4/5)^{n₀})/2)·|A_{n₀}|⁻¹。两歧常数皆封闭 Q 项。 *)
Theorem cc_engine : forall (X : Real) (A B : nat -> Z) (clo : nat -> Q),
  (forall n : nat, real_le (cc_line X (A n) (B n))
                           (real_const (q_pow (4 # 5)%Q n))) ->
  (forall n : nat, real_le (real_const (clo n))
                           (cc_line X (A n) (B n))) ->
  (forall n : nat, QltT 0 (clo n)) ->
  (forall n : nat, QltT 0 (Qabs ((A n) # 1)%Q)) ->
  forall (u : Z) (v : positive),
    sigT (fun c : Q => And (QltT 0 c)
      (sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
        QleT' c (Qabs (((u # v)%Q - projT1 X k)%Q))))).
Proof.
  intros X A B clo Hup Hlo Hclop HA u v.
  set (n0 := 8 * Z.to_nat (Z.pos v)).
  assert (Hband1v : QltT (q_pow (4 # 5)%Q n0) ((1 # v)%Q))
    by (apply cc_band_v).
  destruct (Z.eq_dec (u * A n0) (Z.pos v * B n0)) as [Hhit | Hmiss].
  - (* —— 命支：逼近对与 u/v 重合，载体下界肢供正分离常数 —— *)
    assert (HhitQ : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q == 0%Q).
    { rewrite ln2b_line_q. rewrite Hhit.
      unfold Qeq. cbn [Qnum Qden Pos.mul]. lia. }
    assert (Heps0 : QltT 0 ((clo n0)%Q * (1 # 2)%Q)%Q).
    { apply qmult_ltT_0_compat.
      - exact (Hclop n0).
      - apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
    destruct (ln2b_le_pt_slack (real_const (clo n0))
                (cc_line X (A n0) (B n0)) (Hlo n0)
                ((clo n0)%Q * (1 # 2)%Q)%Q Heps0) as [K HK].
    exists (((clo n0)%Q * (1 # 2)%Q) * Qinv (Qabs ((A n0) # 1)%Q))%Q.
    split.
    + apply qmult_ltT_0_compat.
      * exact Heps0.
      * apply Qlt_to_QltT. apply Qinv_lt_0_compat.
        exact (QltT_to_Qlt _ _ (HA n0)).
    + exists K. intros k Hk.
      pose proof (HK k Hk) as HKq0.
      pose proof (QltT_to_Qlt _ _ HKq0) as HKq.
      rewrite (real_const_proj (clo n0) k) in HKq.
      (* clo < line + clo/2 ⟹ clo − clo/2 < line（加法消去；clo − clo/2 == clo/2） *)
      assert (Hred : Qlt ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                          (projT1 (cc_line X (A n0) (B n0)) k)%Q).
      { apply (lic_qlt_add_r_cancel_r ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                 (projT1 (cc_line X (A n0) (B n0)) k)
                 ((clo n0)%Q * (1 # 2)%Q)%Q).
        assert (Eclo : ((clo n0)%Q
                       == (((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)
                             + (clo n0)%Q * (1 # 2)%Q))%Q) by cc_zring.
        rewrite <- Eclo. exact HKq. }
      assert (Hhalf : Qlt ((clo n0)%Q * (1 # 2)%Q)
                           (projT1 (cc_line X (A n0) (B n0)) k)%Q).
      { assert (Er : ((clo n0)%Q - (clo n0)%Q * (1 # 2)%Q)%Q
                     == ((clo n0)%Q * (1 # 2)%Q)%Q) by cc_zring.
        rewrite Er in Hred. exact Hred. }
      rewrite (cc_line_pt X (A n0) (B n0) k) in Hhalf.
      rewrite (cc_hit_abs (A n0) (B n0) (projT1 X k) ((u # v)%Q) HhitQ)
        in Hhalf.
      apply Qle_to_QleT'. apply Qlt_le_weak.
      rewrite (Qabs_Qminus ((u # v)%Q) (projT1 X k)).
      exact (ln2b_div_lt_of ((clo n0)%Q * (1 # 2)%Q)
               (Qabs ((A n0) # 1)%Q)
               (Qabs ((projT1 X k - (u # v)%Q)%Q)) (HA n0) Hhalf).
  - (* —— 否支：整数 heart + 三角劈分 + 闭式带窗 —— *)
    assert (Hw0 : (u * A n0 - Z.pos v * B n0 <> 0)%Z)
      by (intro E; apply Hmiss; lia).
    assert (Hq : (((A n0) # 1)%Q * ((u # v)%Q) - ((B n0) # 1)%Q)%Q
                 == (((u * A n0 - Z.pos v * B n0) # v)%Q))
      by exact (ln2b_line_q (A n0) (B n0) u v).
    (* 1/v ≤ |w/v|（整数 heart 的 Qabs 通分账） *)
    assert (Honev : Qle ((1 # v)%Q)
                      (Qabs (((u * A n0 - Z.pos v * B n0) # v)%Q))).
    { unfold Qle, Qabs. cbn [Qabs Qnum Qden].
      pose proof (proj2 (Z.abs_pos (u * A n0 - Z.pos v * B n0)) Hw0). nia. }
    (* 窗余量 W := 1/v − (4/5)^{n₀} > 0，Δ := W/2 *)
    assert (HW0 : Qlt 0 (((1 # v)%Q - q_pow (4 # 5)%Q n0)%Q)).
    { apply lic_qlt_0_minus. exact (QltT_to_Qlt _ _ Hband1v). }
    assert (Hdelta0 : QltT 0 (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q).
    { apply qmult_ltT_0_compat.
      - apply Qlt_to_QltT. exact HW0.
      - apply Qlt_to_QltT. unfold Qlt. cbn. lia. }
    destruct (ln2b_le_pt_slack (cc_line X (A n0) (B n0))
                (real_const (q_pow (4 # 5)%Q n0)) (Hup n0)
                (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q Hdelta0)
      as [K HK].
    exists ((((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
              * Qinv (Qabs ((A n0) # 1)%Q))%Q.
    split.
    + apply qmult_ltT_0_compat.
      * exact Hdelta0.
      * apply Qlt_to_QltT. apply Qinv_lt_0_compat.
        exact (QltT_to_Qlt _ _ (HA n0)).
    + exists K. intros k Hk.
      pose proof (HK k Hk) as HKq0.
      pose proof (QltT_to_Qlt _ _ HKq0) as HKq.
      rewrite (real_const_proj (q_pow (4 # 5)%Q n0) k) in HKq.
      assert (Hmid : ((q_pow (4 # 5)%Q n0)
                       + ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q
                     == ((1 # v)%Q
                         - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q)
        by cc_zring.
      rewrite Hmid in HKq.
      pose proof (cc_tri X (A n0) (B n0) ((u # v)%Q) k) as Htri.
      assert (Hleg1 : Qle (Qabs (((u * A n0 - Z.pos v * B n0) # v)%Q))
                       (Qabs (((A n0) # 1)%Q * ((u # v)%Q)
                                - ((B n0) # 1)%Q))%Q).
      { apply qeq_le. apply Qeq_sym. apply Qabs_wd. exact Hq. }
      assert (Hleg2 : Qle (Qabs (((A n0) # 1)%Q * ((u # v)%Q)
                                   - ((B n0) # 1)%Q))
                       (Qabs ((A n0) # 1)%Q
                          * Qabs (((u # v)%Q - projT1 X k)%Q)
                          + projT1 (cc_line X (A n0) (B n0)) k)%Q)
        by exact Htri.
      pose proof (Qle_trans _ _ _ Honev
                   (Qle_trans _ _ _ Hleg1 Hleg2)) as Hchain1.
      assert (Hchain2 : Qlt (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              + projT1 (cc_line X (A n0) (B n0)) k)%Q
                             (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              + ((1 # v)%Q
                                 - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                   * (1 # 2)))%Q)
        by (apply (lic_qlt_add_l (Qabs ((A n0) # 1)%Q
                                   * Qabs (((u # v)%Q - projT1 X k)%Q)));
            exact HKq).
      assert (Hpre : Qlt ((1 # v)%Q)
                      (Qabs ((A n0) # 1)%Q
                         * Qabs (((u # v)%Q - projT1 X k)%Q)
                         + ((1 # v)%Q
                            - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2)))%Q)
        by (apply (Qle_lt_trans (1 # v)%Q
                    (Qabs ((A n0) # 1)%Q
                       * Qabs (((u # v)%Q - projT1 X k)%Q)
                       + projT1 (cc_line X (A n0) (B n0)) k)%Q);
            assumption).
      assert (Hchain : Qlt (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                         (Qabs ((A n0) # 1)%Q
                            * Qabs (((u # v)%Q - projT1 X k)%Q))).
      { pose proof (proj1 (Qlt_minus_iff (1 # v)%Q
                             (Qabs ((A n0) # 1)%Q
                                * Qabs (((u # v)%Q - projT1 X k)%Q)
                                + ((1 # v)%Q
                                   - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                     * (1 # 2)))%Q)
                     Hpre) as Hm.
        assert (Hring : ((Qabs ((A n0) # 1)%Q
                            * Qabs (((u # v)%Q - projT1 X k)%Q)
                            + ((1 # v)%Q
                               - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2)))
                          - (1 # v)%Q)%Q
                        == (Qabs ((A n0) # 1)%Q
                              * Qabs (((u # v)%Q - projT1 X k)%Q)
                              - ((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))%Q)
          by cc_zring.
        rewrite Hring in Hm.
        assert (Hring2 : ((((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                            + (Qabs ((A n0) # 1)%Q
                                 * Qabs (((u # v)%Q - projT1 X k)%Q)
                                 - ((1 # v)%Q - q_pow (4 # 5)%Q n0)
                                   * (1 # 2)))%Q
                         == (Qabs ((A n0) # 1)%Q
                               * Qabs (((u # v)%Q - projT1 X k)%Q)))
          by cc_zring.
        apply (lic_qlt_comp_r
                 _ (Qabs ((A n0) # 1)%Q
                      * Qabs (((u # v)%Q - projT1 X k)%Q))
                 (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
                 Hring2 (lic_qlt_lt_add_r _ _ Hm)).
      }
      apply Qle_to_QleT'. apply Qlt_le_weak.
      apply (ln2b_div_lt_of (((1 # v)%Q - q_pow (4 # 5)%Q n0) * (1 # 2))
               (Qabs ((A n0) # 1)%Q)
               (Qabs (((u # v)%Q - projT1 X k)%Q))).
      -- exact (HA n0).
      -- exact Hchain.
Qed.

(* ============================================================ *)
(* 可提取验证（Set 层见证面：分离核/带窗/线对象）                             *)
(* ============================================================ *)

Separate Extraction cc_sep_div cc_band cc_line.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。             *)
(* ============================================================ *)

Print Assumptions cc_one_le_zabs.
Print Assumptions cc_diff_cross.
Print Assumptions cc_sep_core.
Print Assumptions cc_sep_div.
Print Assumptions cc_bernoulli.
Print Assumptions cc_qpow_swap.
Print Assumptions cc_q8_index.
Print Assumptions cc_band.
Print Assumptions cc_band_anchor1.
Print Assumptions cc_line_pt.
Print Assumptions cc_hit_abs.
Print Assumptions cc_tri.
Print Assumptions cc_engine.
