(* 五字段指针｜使命：B5 非折半法锐化机（R 版终形）——√2 闭式分离常元
   自 1/(12b²)（u5c 现役·四分支定侧）锐化至 1/(b·(|a|+2b))（非折半·整值定侧连续化）。
   本件＝B5R 承 B5 冻结遗产收束：三工序（§B 桥层/§M 边距分支核/§W+§E 窗口自举）
   按冻结刻形（_c_b5_11..17 逐发错痕＋§F 注释块）落编译，终形 b5_sqrt2_nonhalf 零前提绿判。
   锐化账（精确有理算术独立复算全 PASS）：近域锐化 3.51×、Markov 天花板捕获 82.84%、
   收敛点最坏裕量 1.21×、锐化带 |a|<10b 符号全称验证。
   全证层：§S 基量（b5_den/b5_cert/正性/QeqT 钉定）｜§G 整隙（|a²−2b²|≥1）｜§I 恒等链
   （(q−x)(q+x)=q²−x² 之 Qabs 形）｜§H 计量辅助（证书上界/乘透/2w 界/e-衰减）｜
   §B 桥（b5_escape_dist：witness ε:=e(n0)/2 直达 real_lt——免 dmec 因子-2 税）｜
   §M 边距分支核（整值定侧：分支 A a²≤2b²／B a²>2b²∧|a|>2b／C a²>2b²∧|a|≤2b∧x≤q／
   sliver 2<q²<x² 由逃逸假设矛盾消去＋q≤0 直收）｜§W 窗口（e(n)≤1/(112b²)，n≥b+4）｜
   §E 逃逸自举（e(n')<D(n') ⟹ e(n'+1)<D(n'+1)，5/7-窗比）｜§T 终形装配（u5c 同形·c QeqT 钉定）｜
   §A 审计（PA＋Separate Extraction＋锐化样例 vm_compute）。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、
   SumInvFactEscape、UpReqBanachNormOpp、UpReqIrrationalCriterion、UpReqSqrt3Irrational、
   u5c_dm_escape_window；Stdlib QArith、Qabs、ZArith、Arith、Bool、Lia、Setoid、Morphisms、Qfield。
   构造性注记：承载语句面全 Set 层（sigT/prod/QltT/QleT'/real_lt/QeqT），零 Prop 前提位；
   证明体内构造性 Prop 推导合法；Q 层计量辅助件（Qle/Qlt 收尾）按在册 lib 同款工艺
   （lic_*/ir2_* 先例·转换词表迁移件类）；零承认、零 Abort、零全局假设、零经典逻辑；
   定义面透明。终形 b5_sqrt2_nonhalf 零前提（Print Assumptions Closed）。
   编译配方：rocq c -native-compiler no -q -Q . "" b5_machine.v *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import UpReqSqrt3Irrational.
Require Import u5c_dm_escape_window.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* §S 基量层：b5_den / b5_cert / 正性 / QeqT 钉定                  *)
(* ============================================================ *)

Definition b5_den (a : Z) (b : positive) : Z :=
  Z.pos b * (Z.abs a + 2 * Z.pos b).

Definition b5_cert (a : Z) (b : positive) : Q :=
  Qinv ((b5_den a b) # 1).

Lemma b5_den_pos : forall (a : Z) (b : positive), (0 < b5_den a b)%Z.
Proof.
  intros a b. unfold b5_den.
  pose proof (Z.abs_nonneg a) as Ha.
  pose proof (Pos2Z.is_pos b) as Hb.
  nia.
Qed.

Lemma b5_qinv_pos_lt : forall p : positive, QltT 0 (Qinv ((Z.pos p) # 1)).
Proof.
  intro p. apply Qlt_to_QltT. unfold Qlt, Qinv. cbn [Qnum Qden]. lia.
Qed.

Lemma b5_qinv_pos_lt2 : forall z : Z, (0 < z)%Z -> QltT 0 (Qinv (z # 1)).
Proof.
  intros z Hz. destruct z.
  - exfalso. lia.
  - apply b5_qinv_pos_lt.
  - exfalso. lia.
Qed.

Lemma b5_cert_pos : forall (a : Z) (b : positive), QltT 0 (b5_cert a b).
Proof.
  intros a b. unfold b5_cert. apply b5_qinv_pos_lt2. apply b5_den_pos.
Qed.

Lemma b5_cert_eq : forall (a : Z) (b : positive),
  QeqT (b5_cert a b) (Qinv ((Z.pos b * (Z.abs a + 2 * Z.pos b)) # 1)).
Proof.
  intros a b. unfold b5_cert. apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §G 整隙层（Z）：|a²−2b²| ≥ 1（ir2_no_sqrtZ 直系）                *)
(* ============================================================ *)

Lemma b5_gap_ge1 : forall (a : Z) (b : positive),
  (1 <= Z.abs (a * a - 2 * (Z.pos b * Z.pos b)))%Z.
Proof.
  intros a b.
  pose proof (Pos2Z.is_pos b) as Hb0.
  assert (Hne : (a * a - 2 * (Z.pos b * Z.pos b) <> 0)%Z).
  { intro Hc. apply (ir2_no_sqrtZ a (Z.pos b) Hb0). lia. }
  lia.
Qed.

(* ============================================================ *)
(* §I 恒等链层（Q）：(q−x)(q+x) = q²−x² 之 Qabs 形                  *)
(* ============================================================ *)

Lemma b5_sq_diff_abs : forall u v : Q,
  Qabs ((u - v) * (u + v)) == Qabs (u * u - v * v).
Proof.
  intros u v. rewrite <- (ir2_sq_diff u v). apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §H 计量辅助层（证书上界/乘透/2w 界/e-衰减——lic_*/ir2_* 同款工艺）   *)
(* ============================================================ *)

(* Qle 降 Z（Qle 定义面即 Z.le 形·exact 直提） *)
Lemma b5_qle_to_zle : forall x y : Q,
  Qle x y -> (Qnum x * Z.pos (Qden y) <= Qnum y * Z.pos (Qden x))%Z.
Proof. intros x y H. exact H. Qed.

(* 乘正元保严格序（右乘） *)
Lemma b5_qlt_mul_pos_r : forall x y z : Q, Qlt x y -> Qlt 0 z -> Qlt (x * z) (y * z).
Proof.
  intros x y z Hxy Hz.
  pose proof (Qmult_lt_0_compat ((y - x)%Q) z (lic_qlt_0_minus _ _ Hxy) Hz) as Hp.
  assert (Hsplit : (y * z == (x * z + (y - x) * z)%Q)) by ring.
  rewrite Hsplit. apply lic_qlt_lt_add_r. exact Hp.
Qed.

(* 正元消去（右乘·b5_qlt_mul_pos_r 之逆） *)
Lemma b5_qlt_mul_pos_cancel_r : forall x y z : Q,
  Qlt (x * z) (y * z) -> Qlt 0 z -> Qlt x y.
Proof.
  intros x y z Hlt Hz.
  destruct (Qlt_bool y x) eqn:E.
  - exfalso.
    pose proof (lic_qlt_bool_true _ _ E) as Hyx.
    pose proof (b5_qlt_mul_pos_r y x z Hyx Hz) as Hcontra.
    exact (Qlt_not_eq (x * z)%Q (x * z)%Q
             (Qlt_trans (x * z) (y * z) (x * z) Hlt Hcontra)
             (Qeq_refl (x * z)%Q)).
  - pose proof (lic_qlt_bool_false_le y x E) as Hle.
    destruct (Qle_lt_or_eq x y Hle) as [Hlt2 | Heq].
    + exact Hlt2.
    + exfalso. rewrite Heq in Hlt.
      exact (Qlt_not_eq (y * z)%Q (y * z)%Q Hlt (Qeq_refl (y * z)%Q)).
Qed.

(* 证书常元上界（den ≥ Z.pos p ⟹ c ≤ 1/p） *)
Lemma b5_cert_le : forall (a : Z) (b : positive) (p : positive),
  (Z.pos p <= b5_den a b)%Z -> Qle (b5_cert a b) (1 # p).
Proof.
  intros a b p Hd. unfold b5_cert.
  apply (Qle_trans (Qinv ((b5_den a b) # 1)) (Qinv ((Z.pos p) # 1)) (1 # p)).
  - apply (ir2_inv_le ((Z.pos p) # 1) ((b5_den a b) # 1)).
    + unfold Qlt. cbn [Qnum Qden]. pose proof (Pos2Z.is_pos p). lia.
    + unfold Qle. cbn [Qnum Qden]. pose proof Hd. lia.
  - apply qeq_le. apply qeqT_imp_qeq. apply (dmew_Qinv_1p p).
Qed.

(* 证书乘透：c·Y ≤ K ⟸ Y ≤ den·K（ir2_ge_inv 同构） *)
Lemma b5_cert_mul_le : forall (a : Z) (b : positive) (Y K : Q),
  Qle Y (((b5_den a b) # 1) * K) -> Qle (b5_cert a b * Y) K.
Proof.
  intros a b Y K HY.
  pose proof (QltT_to_Qlt _ _ (b5_cert_pos a b)) as Hc0.
  assert (Hc0le : Qle 0%Q (b5_cert a b)) by (apply Qlt_le_weak; exact Hc0).
  assert (Hne : ~ (((b5_den a b) # 1)%Q == 0%Q)).
  { intro Hc. unfold b5_cert in Hc0. rewrite Hc in Hc0.
    exact (Qlt_not_eq 0%Q 0%Q Hc0 (Qeq_refl 0%Q)). }
  apply (Qle_trans (b5_cert a b * Y)
                   (b5_cert a b * (((b5_den a b) # 1) * K))).
  - unfold b5_cert.
    pose proof (ir2_mult_le_compat_l Y (((b5_den a b) # 1) * K)
                  (Qinv ((b5_den a b) # 1)) HY Hc0le) as HH.
    exact HH.
  - unfold b5_cert.
    assert (Hmove : (Qinv ((b5_den a b) # 1)
                       * (((b5_den a b) # 1) * K) == K)%Q).
    { pose proof (bno_mul_div_self ((b5_den a b) # 1) Hne) as Hb.
      unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
      setoid_rewrite (Qmult_assoc (Qinv ((b5_den a b) # 1))
                        ((b5_den a b) # 1) K).
      setoid_rewrite (Qmult_comm (Qinv ((b5_den a b) # 1))
                        ((b5_den a b) # 1)).
      setoid_rewrite Hb. apply Qmult_1_l. }
    exact (qeq_le _ _ Hmove).
Qed.

(* 2w ≤ 2/(112b²) *)
Lemma b5_ww_le : forall (b : positive) (n0 : nat),
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  Qle (ir2_e n0 + ir2_e n0) (2 # (112 * (b * b)))%Q.
Proof.
  intros b n0 Hwin.
  apply (Qle_trans (ir2_e n0 + ir2_e n0)
                   ((1 # (112 * (b * b)))%Q + (1 # (112 * (b * b)))%Q)).
  - apply Qplus_le_compat; [exact Hwin | exact Hwin].
  - apply qeq_le. unfold Qeq. cbn [Qnum Qden Qplus]. nia.
Qed.

(* 0 < w（自 ir2_delta_pos） *)
Lemma b5_e_pos : forall n : nat, Qlt 0 (ir2_e n).
Proof.
  intro n.
  apply (Qmult_lt_0_compat (1 # 2) (ir2_delta n)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - exact (ir2_delta_pos n).
Qed.

(* 0 ≤ w（自 b5_e_pos） *)
Lemma b5_e_ge0 : forall n : nat, Qle 0 (ir2_e n).
Proof. intro n. apply Qlt_le_weak. apply (b5_e_pos n). Qed.

(* δ == 2w 恒等 *)
Lemma b5_delta_ww : forall n : nat, (ir2_delta n == ir2_e n + ir2_e n)%Q.
Proof. intro n. unfold ir2_e. ring. Qed.

(* e 一步衰减 1/28（δ'≤δ/28 ⟹ w'≤w/28） *)
Lemma b5_e_decay28 : forall n : nat, (1 <= n)%nat ->
  Qle (ir2_e (Datatypes.S n)) (((1 # 28) * ir2_e n)%Q).
Proof.
  intros n Hn1.
  pose proof (ir2_delta_step n Hn1 (ir2_quarter n Hn1)) as Hstep.
  apply (Qle_trans (ir2_e (Datatypes.S n))
                   (((1 # 2) * ((1 # 28) * ir2_delta n))%Q)
                   (((1 # 28) * ir2_e n)%Q)).
  - pose proof (ir2_mult_le_compat_l (ir2_delta (Datatypes.S n))
                  ((1 # 28) * ir2_delta n) (1 # 2) Hstep
                  (ltac:(unfold Qle; cbn [Qnum Qden]; lia))) as HH.
    unfold ir2_e. exact HH.
  - apply qeq_le. unfold ir2_e. ring.
Qed.

(* q ≤ |a|/b（q ≤ |q| 直系） *)
Lemma b5_q_le_absden : forall (a : Z) (b : positive),
  Qle ((a # b)%Q) ((Z.abs a) # b)%Q.
Proof.
  intros a b. unfold Qle. cbn [Qnum Qden].
  destruct a; cbn [Z.abs]; lia.
Qed.

(* ============================================================ *)
(* §B 桥层：witness ε:=e(n0)/2 直达 real_lt（免 dmec 因子-2 税）      *)
(* ============================================================ *)

Lemma b5_escape_dist :
  forall (q : Q) (n0 : nat), (1 <= n0)%nat ->
    QltT (ir2_e n0) (Qabs ((q - ir2_x n0)%Q)) ->
    forall c : Q,
    QltT (c + (ir2_e n0 + ir2_e n0)) (Qabs ((q - ir2_x n0)%Q)) ->
    real_lt (real_const c)
      (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                        (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                   (real_const q)).
Proof.
  intros q n0 Hn01 Hesc c Hm.
  pose proof (QltT_to_Qlt _ _ Hesc) as HescQ.
  pose proof (QltT_to_Qlt _ _ Hm) as HmQ.
  pose proof (b5_e_pos n0) as He0.
  unfold real_lt.
  exists ((1 # 2) * ir2_e n0)%Q.
  split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1 # 2) (ir2_e n0)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact He0.
  - exists n0. intros k HkN.
    apply NatLe_drop in HkN.
    pose proof (QltT_to_Qlt _ _ (ir2_tail n0 k Hn01 HkN)) as Ht0'.
    assert (Hpre : (q - ir2_x n0)%Q == ((q - ir2_x k) + (ir2_x k - ir2_x n0))%Q)
      by exact (lic_qlt_tri_decomp q (ir2_x n0) (ir2_x k)).
    assert (Htri : Qle (Qabs ((q - ir2_x n0)%Q))
                       (Qabs ((q - ir2_x k)%Q) + Qabs ((ir2_x k - ir2_x n0)%Q))).
    { pose proof (Qabs_triangle ((q - ir2_x k)%Q) ((ir2_x k - ir2_x n0)%Q)) as HTR.
      apply (Qle_trans (Qabs ((q - ir2_x n0)%Q))
               (Qabs (((q - ir2_x k) + (ir2_x k - ir2_x n0))%Q))).
      - apply qeq_le. setoid_rewrite Hpre. apply Qeq_refl.
      - exact HTR. }
    assert (Hlt2 : Qlt (Qabs ((q - ir2_x n0)%Q))
                       (Qabs ((q - ir2_x k)%Q) + ir2_e n0)).
    { apply (Qle_lt_trans _ (Qabs ((q - ir2_x k)%Q) + Qabs ((ir2_x k - ir2_x n0)%Q))).
      - exact Htri.
      - apply (lic_qlt_add_l _ _ _). exact Ht0'. }
    assert (Hltm : Qlt ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)%Q)
                       (Qabs ((q - ir2_x k)%Q))).
    { apply (lic_qlt_add_r_cancel_r
               ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)) (Qabs ((q - ir2_x k)%Q))
               (ir2_e n0)).
      rewrite (lic_qlt_minus_add_r (Qabs ((q - ir2_x n0)%Q)) (ir2_e n0)).
      exact Hlt2. }
    (* c+e < A−e（自 HmQ : c+2e < A） *)
    assert (Hce : Qlt (c + ir2_e n0)
                      ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)%Q)).
    { pose proof (lic_qlt_add_l (Qopp (ir2_e n0))
                  (c + (ir2_e n0 + ir2_e n0)) (Qabs ((q - ir2_x n0)%Q)) HmQ) as HH.
      assert (Hzeq : (Qopp (ir2_e n0) + (c + (ir2_e n0 + ir2_e n0))
                       == c + ir2_e n0)%Q) by ring.
      assert (Hzeq2 : (Qopp (ir2_e n0) + Qabs ((q - ir2_x n0)%Q)
                       == (Qabs ((q - ir2_x n0)%Q) - ir2_e n0))%Q) by ring.
      rewrite Hzeq in HH. rewrite Hzeq2 in HH. exact HH. }
    assert (Hfin : Qlt (c + ((1 # 2) * ir2_e n0))
                       ((Qabs ((q - ir2_x n0)%Q) - ir2_e n0)%Q)).
    { apply (Qlt_trans _ (c + ir2_e n0)).
      - apply (lic_qlt_add_l c).
        pose proof (b5_qlt_mul_pos_r (1 # 2) 1 (ir2_e n0)
                      (ltac:(unfold Qlt; cbn [Qnum Qden]; lia)) He0) as Hh2.
        apply (lic_qlt_comp_r (1 * ir2_e n0)%Q (ir2_e n0)).
        + apply Qeq_sym. ring.
        + exact Hh2.
      - exact Hce. }
    assert (HPr : projT1 (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                                  (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                           (real_const q)) k
                == Qabs ((ir2_x k - q)%Q))
      by apply lic_metric_proj.
    apply (lic_qltt_comp_r ((Qabs ((q - ir2_x k)%Q)) - c)
             (projT1 (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                                    (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                              (real_const q)) k
              - projT1 (real_const c) k) ((1 # 2) * ir2_e n0)).
    + rewrite real_const_proj. rewrite HPr.
      rewrite (Qabs_Qminus q (ir2_x k)). reflexivity.
    + apply Qlt_to_QltT.
      apply (lic_qlt_add_r_cancel_r ((1 # 2) * ir2_e n0)
               (Qabs ((q - ir2_x k)%Q) - c) c).
      rewrite (lic_qlt_minus_add_r (Qabs ((q - ir2_x k)%Q)) c).
      pose proof Hfin as Hfin2.
      rewrite (Qplus_comm c ((1 # 2) * ir2_e n0)) in Hfin2.
      apply (Qlt_trans _ (Qabs ((q - ir2_x n0)%Q) - ir2_e n0)).
      * exact Hfin2.
      * exact Hltm.
Qed.

(* ============================================================ *)
(* §M 边距分支核：整值定侧连续化                                     *)
(*    分支 A（a²≤2b²）／B（a²>2b²∧|a|>2b）／C（a²>2b²∧|a|≤2b∧x≤q）    *)
(*    ＋sliver（2<q²<x²）逃逸矛盾消去＋q≤0 直收                       *)
(* ============================================================ *)

(* 直收件：q ≤ 0 ⟹ D ≥ x ≥ 7/5 > c+2w *)
Lemma b5_margin_nonpos : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  Qle ((a # b)%Q) 0%Q ->
  QltT (b5_cert a b + (ir2_e n0 + ir2_e n0)) (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Hwin Hq0.
  pose proof (ir2_x_lb n0) as Hxlb.
  assert (HD : Qabs (((a # b)%Q - ir2_x n0)%Q) == (ir2_x n0 - (a # b)%Q)%Q).
  { rewrite (Qabs_Qminus ((a # b)%Q) (ir2_x n0)). apply ir2_abs_sub.
    apply (Qle_trans ((a # b)%Q) 0%Q (ir2_x n0));
      [exact Hq0 | apply Qlt_le_weak; apply (ir2_x_pos n0)]. }
  pose proof (Qopp_le_compat ((a # b)%Q) 0%Q Hq0) as Hneg.
  assert (Hge : Qle (7 # 5) (Qabs (((a # b)%Q - ir2_x n0)%Q))).
  { rewrite HD.
    apply (Qle_trans (7 # 5) (ir2_x n0)).
    - exact Hxlb.
    - apply (Qle_trans _ (ir2_x n0 + Qopp ((a # b)%Q))).
      + apply (Qle_trans _ (ir2_x n0 + 0%Q)).
        * assert (Hx0 : (ir2_x n0 == ir2_x n0 + 0%Q)%Q) by ring.
          apply qeq_le. exact Hx0.
        * apply (Qplus_le_compat (ir2_x n0) (ir2_x n0) 0%Q
                   (Qopp ((a # b)%Q)));
            [apply Qle_refl | exact Hneg].
      + apply Qle_refl. }
  assert (Hc : Qle (b5_cert a b) (1 # 2))
    by (apply b5_cert_le; unfold b5_den;
        pose proof (Pos2Z.is_pos b); nia).
  assert (Hww : Qle (ir2_e n0 + ir2_e n0) (2 # (112 * (b * b))))
    by (apply b5_ww_le; exact Hwin).
  assert (Hsmall : Qlt (b5_cert a b + (ir2_e n0 + ir2_e n0)) (7 # 5)).
  { apply (Qle_lt_trans _ ((1 # 2) + (2 # (112 * (b * b))))%Q).
    - apply Qplus_le_compat; [exact Hc | exact Hww].
    - unfold Qlt. cbn [Qnum Qden Qplus]. nia. }
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (7 # 5)%Q); [exact Hsmall | exact Hge].
Qed.

(* 分支 A：a² ≤ 2b² *)
Lemma b5_margin_A : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  (a * a <= 2 * (Z.pos b * Z.pos b))%Z ->
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  QltT (ir2_e n0) (Qabs (((a # b)%Q - ir2_x n0)%Q)) ->
  QltT (b5_cert a b + (ir2_e n0 + ir2_e n0)) (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Hsq Hwin Hesc.
  pose proof (ir2_x_lb n0) as Hxlb.
  pose proof (ir2_x_ub n0 Hn01) as Hxub.
  pose proof (ir2_x_pos n0) as Hxpos.
  pose proof (ir2_sq_ge2 n0) as Hxsq.
  pose proof (b5_gap_ge1 a b) as Hgap.
  pose proof (b5_e_pos n0) as He0.
  pose proof (Pos2Z.is_pos b) as Hb0.
  assert (Hlo : (1 <= 2 * (Z.pos b * Z.pos b) - a * a)%Z) by lia.
  assert (Hab : (Z.abs a <= 2 * Z.pos b)%Z) by nia.
  assert (HxubZ : (Qnum (ir2_x n0) * 2 <= 3 * Z.pos (Qden (ir2_x n0)))%Z)
    by (pose proof (b5_qle_to_zle (ir2_x n0) (3 # 2)%Q Hxub) as HH;
        cbn [Qnum Qden] in HH; exact HH).
  (* 1/b² ≤ 2−q² ≤ x²−q² > 0 *)
  assert (Hii : Qle ((1 # (b * b))%Q) (2%Q - ((a # b)%Q * ((a # b)%Q)))).
  { unfold Qle, Qminus. cbn [Qnum Qden Qmult Qplus Qopp]. nia. }
  assert (Hiii : Qle (2%Q - ((a # b)%Q * ((a # b)%Q)))
                     (ir2_x n0 * ir2_x n0 - ((a # b)%Q * ((a # b)%Q)))).
  { pose proof (ir2_add_le_r 2%Q (ir2_x n0 * ir2_x n0)
                  (Qopp (((a # b)%Q * ((a # b)%Q)))) Hxsq) as HH.
    unfold Qminus. exact HH. }
  assert (Hgx : Qlt 0%Q (ir2_x n0 * ir2_x n0 - ((a # b)%Q * ((a # b)%Q)))).
  { apply (Qlt_le_trans _ ((1 # (b * b))%Q)).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - apply (Qle_trans _ (2%Q - ((a # b)%Q * ((a # b)%Q))));
        [exact Hii | exact Hiii]. }
  (* q < x（整隙定侧） *)
  assert (Hqx : Qlt ((a # b)%Q) (ir2_x n0)).
  { destruct (Qlt_bool ((a # b)%Q) (ir2_x n0)) eqn:Hb;
      [exact (lic_qlt_bool_true _ _ Hb) |].
    exfalso.
    pose proof (lic_qlt_bool_false_le ((a # b)%Q) (ir2_x n0) Hb) as Hle.
    pose proof (ir2_sq_mono ((a # b)%Q) (ir2_x n0)
                  (Qlt_le_weak _ _ Hxpos) Hle) as Hsq2.
    pose proof (ir2_add_le_r (ir2_x n0 * ir2_x n0)
                  (((a # b)%Q * ((a # b)%Q)))
                  (Qopp (((a # b)%Q * ((a # b)%Q)))) Hsq2) as Hsq3.
    assert (Hsq4 : Qle (ir2_x n0 * ir2_x n0 + Qopp (((a # b)%Q * ((a # b)%Q)))) 0%Q).
    { apply (Qle_trans _ (((a # b)%Q * ((a # b)%Q))
                            + Qopp (((a # b)%Q * ((a # b)%Q))))).
      - exact Hsq3.
      - apply qeq_le. ring. }
    unfold Qminus in Hgx.
    exact (Qlt_not_eq 0%Q 0%Q (Qlt_le_trans 0%Q _ 0%Q Hgx Hsq4) (Qeq_refl 0%Q)). }
  assert (HD : Qabs (((a # b)%Q - ir2_x n0)%Q) == (ir2_x n0 - (a # b)%Q)%Q).
  { rewrite (Qabs_Qminus ((a # b)%Q) (ir2_x n0)). apply ir2_abs_sub.
    apply Qlt_le_weak. exact Hqx. }
  destruct (Qlt_bool 0%Q ((a # b)%Q)) eqn:Hq0b.
  - (* q > 0：主路 x+q > 0 *)
    pose proof (lic_qlt_bool_true 0%Q ((a # b)%Q) Hq0b) as Hq0.
    assert (Hcq : Qle (b5_cert a b * (ir2_x n0 + ((a # b)%Q)))
                      (7 # (8 * (b * b)))).
    { apply (b5_cert_mul_le a b).
      apply (Qle_trans (ir2_x n0 + ((a # b)%Q))
                       (((3 # 2) + ((Z.abs a) # b)%Q))
                       (((b5_den a b) # 1) * (7 # (8 * (b * b)))%Q)).
      - apply (Qle_trans _ (ir2_x n0 + ((Z.abs a) # b)%Q)).
        + apply Qplus_le_compat; [apply Qle_refl | apply b5_q_le_absden].
        + apply Qplus_le_compat; [exact Hxub | apply Qle_refl].
      - unfold Qle. cbn [Qnum Qden Qmult Qplus]. unfold b5_den. nia. }
    assert (Hwwq : Qle ((ir2_e n0 + ir2_e n0) * (ir2_x n0 + ((a # b)%Q)))
                       (7 # (112 * (b * b)))).
    { pose proof (b5_ww_le b n0 Hwin) as Hww2.
      pose proof (ir2_qpos_add ((a # b)%Q) (ir2_x n0) Hq0 Hxpos) as Hsum0.
      setoid_rewrite (Qplus_comm ((a # b)%Q) (ir2_x n0)) in Hsum0.
      apply (Qle_trans _ ((2 # (112 * (b * b)))%Q
                            * (ir2_x n0 + ((a # b)%Q)))).
      - apply Qmult_le_compat_r;
          [exact Hww2 | apply Qlt_le_weak; exact Hsum0].
      - apply (Qle_trans _ ((2 # (112 * (b * b)))%Q * ((7 # 2)%Q))).
        + apply ir2_mult_le_compat_l.
          * apply (Qle_trans _ (ir2_x n0 + ((Z.abs a) # b)%Q)).
            -- apply Qplus_le_compat;
                 [apply Qle_refl | apply b5_q_le_absden].
            -- apply (Qle_trans _ (((3 # 2) + ((Z.abs a) # b)%Q))).
               ++ apply Qplus_le_compat; [exact Hxub | apply Qle_refl].
               ++ apply (Qle_trans _ (((3 # 2) + (2 # 1)%Q))).
                  ** apply Qplus_le_compat;
                       [apply Qle_refl | unfold Qle; cbn [Qnum Qden]; nia].
                  ** apply qeq_le. ring.
          * unfold Qle. cbn [Qnum Qden]. nia.
        + apply qeq_le. unfold Qeq. cbn [Qnum Qden Qmult]. nia. }
    assert (Hlt1 : Qlt ((b5_cert a b + (ir2_e n0 + ir2_e n0))
                          * (ir2_x n0 + ((a # b)%Q)))
                       ((1 # (b * b))%Q)).
    { pose proof (Qmult_plus_distr_l (b5_cert a b) (ir2_e n0 + ir2_e n0)
                    (ir2_x n0 + ((a # b)%Q))) as Hdistr.
      apply (Qle_lt_trans _ ((7 # (8 * (b * b)))%Q + (7 # (112 * (b * b)))%Q)).
      - rewrite Hdistr. apply Qplus_le_compat; [exact Hcq | exact Hwwq].
      - unfold Qlt. cbn [Qnum Qden Qplus]. nia. }
    assert (Hge2 : Qle ((1 # (b * b))%Q)
                       ((ir2_x n0 - ((a # b)%Q)) * (ir2_x n0 + ((a # b)%Q)))).
    { apply (Qle_trans _ (ir2_x n0 * ir2_x n0
                            - ((a # b)%Q * ((a # b)%Q)))).
      - apply (Qle_trans _ (2%Q - ((a # b)%Q * ((a # b)%Q))));
          [exact Hii | exact Hiii].
      - apply qeq_le. apply Qeq_sym.
        exact (ir2_sq_diff (ir2_x n0) ((a # b)%Q)). }
    assert (Hkey : Qlt (b5_cert a b + (ir2_e n0 + ir2_e n0))
                       (ir2_x n0 - ((a # b)%Q))).
    { apply (b5_qlt_mul_pos_cancel_r (b5_cert a b + (ir2_e n0 + ir2_e n0))
               (ir2_x n0 - ((a # b)%Q)) (ir2_x n0 + ((a # b)%Q))).
      - apply (Qlt_le_trans _ ((1 # (b * b))%Q)).
        + exact Hlt1.
        + exact Hge2.
      - pose proof (ir2_qpos_add ((a # b)%Q) (ir2_x n0) Hq0 Hxpos) as Hsum.
        setoid_rewrite (Qplus_comm ((a # b)%Q) (ir2_x n0)) in Hsum.
        exact Hsum. }
    apply Qlt_to_QltT. rewrite HD. exact Hkey.
  - (* q ≤ 0：直收 *)
    exact (b5_margin_nonpos a b n0 Hn01 Hwin
             (lic_qlt_bool_false_le 0%Q ((a # b)%Q) Hq0b)).
Qed.

(* 分支 B：a² > 2b² ∧ |a| > 2b *)
Lemma b5_margin_B : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  (2 * (Z.pos b * Z.pos b) < a * a)%Z ->
  (2 * Z.pos b < Z.abs a)%Z ->
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  QltT (b5_cert a b + (ir2_e n0 + ir2_e n0)) (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Hsq Habs Hwin.
  pose proof (ir2_x_ub n0 Hn01) as Hxub.
  assert (Hc : Qle (b5_cert a b) (1 # (4 * (b * b))))
    by (apply b5_cert_le; unfold b5_den;
        pose proof (Pos2Z.is_pos b); nia).
  assert (Hww : Qle (ir2_e n0 + ir2_e n0) (2 # (112 * (b * b))))
    by (apply b5_ww_le; exact Hwin).
  assert (Hsmall : Qlt (b5_cert a b + (ir2_e n0 + ir2_e n0)) (1 # 2)).
  { apply (Qle_lt_trans _ ((1 # (4 * (b * b))) + (2 # (112 * (b * b))))%Q).
    - apply Qplus_le_compat; [exact Hc | exact Hww].
    - unfold Qlt. cbn [Qnum Qden Qplus]. nia. }
  assert (Hqabs : Qabs ((a # b)%Q) == ((Z.abs a) # b)%Q)
    by (destruct a; reflexivity).
  assert (Hq : Qle ((2 # 1) + (1 # b)) (Qabs ((a # b)%Q))).
  { rewrite Hqabs. unfold Qle. cbn [Qnum Qden Qplus]. nia. }
  assert (Hxabs : Qabs (ir2_x n0) == ir2_x n0).
  { pose proof (ir2_abs_sub (ir2_x n0) 0%Q
                  (Qlt_le_weak 0%Q (ir2_x n0) (ir2_x_pos n0))) as H0.
    assert (Hz0 : (ir2_x n0 - 0%Q == ir2_x n0)%Q) by ring.
    rewrite Hz0 in H0. exact H0. }
  assert (Htri : Qle (Qabs ((a # b)%Q))
                     (Qabs (((a # b)%Q - ir2_x n0)%Q) + ir2_x n0)).
  { pose proof (Qabs_triangle (((a # b)%Q - ir2_x n0)%Q) (ir2_x n0)) as HTR.
    apply (Qle_trans _ (Qabs (((a # b)%Q - ir2_x n0)%Q + ir2_x n0))).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply (Qle_trans _ (Qabs (((a # b)%Q - ir2_x n0)%Q)
                            + Qabs (ir2_x n0))).
      + exact HTR.
      + apply qeq_le. rewrite Hxabs. apply Qeq_refl. }
  assert (Hmid : Qle ((1 # 2) + (1 # b))
                     ((2 # 1) + (1 # b) - (3 # 2))%Q).
  { apply qeq_le. ring. }
  assert (Hsub : Qle ((2 # 1) + (1 # b) - ir2_x n0)
                     (Qabs (((a # b)%Q - ir2_x n0)%Q))).
  { pose proof (ir2_add_le_r (Qabs ((a # b)%Q))
                  (Qabs (((a # b)%Q - ir2_x n0)%Q) + ir2_x n0)
                  (Qopp (ir2_x n0)) Htri) as HT2.
    apply (Qle_trans _ (Qabs ((a # b)%Q) + Qopp (ir2_x n0))).
    - unfold Qminus.
      exact (ir2_add_le_r ((2 # 1) + (1 # b)) (Qabs ((a # b)%Q))
               (Qopp (ir2_x n0)) Hq).
    - apply (Qle_trans _ (Qabs (((a # b)%Q - ir2_x n0)%Q) + ir2_x n0
                            + Qopp (ir2_x n0))).
      + exact HT2.
      + apply qeq_le. ring. }
  assert (Hle : Qle ((1 # 2) + (1 # b)) (Qabs (((a # b)%Q - ir2_x n0)%Q))).
  { apply (Qle_trans _ ((2 # 1) + (1 # b) - (3 # 2))%Q).
    - exact Hmid.
    - apply (Qle_trans _ ((2 # 1) + (1 # b) - ir2_x n0)).
      + pose proof (Qopp_le_compat (ir2_x n0) (3 # 2) Hxub) as Hng.
        unfold Qminus.
        apply (Qplus_le_compat ((2 # 1) + (1 # b)) ((2 # 1) + (1 # b))
                 (Qopp (3 # 2)) (Qopp (ir2_x n0)));
          [apply Qle_refl | exact Hng].
      + exact Hsub. }
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ ((1 # 2)%Q)).
  - exact Hsmall.
  - apply (Qle_trans _ ((1 # 2) + (1 # b))).
    + apply (Qplus_le_compat (1 # 2) (1 # 2) 0%Q (1 # b));
        [apply Qle_refl | unfold Qle; cbn [Qnum Qden]; lia].
    + exact Hle.
Qed.

(* sliver 排除：a²>2b² ∧ |a|≤2b ∧ 0<q<x ⟹ 与逃逸假设矛盾 *)
Lemma b5_margin_sliver : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  (2 * (Z.pos b * Z.pos b) < a * a)%Z ->
  (Z.abs a <= 2 * Z.pos b)%Z ->
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  QltT (ir2_e n0) (Qabs (((a # b)%Q - ir2_x n0)%Q)) ->
  Qlt 0%Q ((a # b)%Q) ->
  Qlt ((a # b)%Q) (ir2_x n0) ->
  False.
Proof.
  intros a b n0 Hn01 Hsq Hab Hwin Hesc Hq0 Hqx.
  pose proof (QltT_to_Qlt _ _ Hesc) as HescQ.
  pose proof (ir2_x_lb n0) as Hxlb.
  pose proof (ir2_x_pos n0) as Hxpos.
  pose proof (b5_e_pos n0) as He0.
  (* q ≥ 7/5（q²>2） *)
  assert (Hq75 : Qle (7 # 5) ((a # b)%Q)).
  { destruct (Qlt_bool ((a # b)%Q) (7 # 5)) eqn:E;
      [| exact (lic_qlt_bool_false_le _ _ E)].
    exfalso.
    pose proof (lic_qlt_bool_true _ _ E) as Hlt75.
    pose proof (ir2_sq_mono (7 # 5) ((a # b)%Q)
                  (Qlt_le_weak _ _ Hq0)
                  (Qlt_le_weak _ _ Hlt75)) as Hsqm.
    assert (H49 : Qlt (((a # b)%Q * ((a # b)%Q))) 2%Q).
    { apply (Qle_lt_trans _ ((7 # 5) * (7 # 5))).
      - exact Hsqm.
      - unfold Qlt. cbn [Qnum Qden Qmult]. lia. }
    assert (Hq2 : Qlt 2%Q (((a # b)%Q * ((a # b)%Q)))).
    { unfold Qlt. cbn [Qnum Qden Qmult]. pose proof Hsq. nia. }
    exact (Qlt_not_eq 2%Q 2%Q
             (Qlt_trans 2%Q _ 2%Q Hq2 H49) (Qeq_refl 2%Q)). }
  (* D == x−q *)
  assert (HD : Qabs (((a # b)%Q - ir2_x n0)%Q) == (ir2_x n0 - (a # b)%Q)%Q).
  { rewrite (Qabs_Qminus ((a # b)%Q) (ir2_x n0)). apply ir2_abs_sub.
    apply Qlt_le_weak. exact Hqx. }
  (* x²−q² ≤ 2w（q²>2 直系） *)
  pose proof (b5_delta_ww n0) as Hdww.
  assert (Hq2 : Qlt 2%Q (((a # b)%Q * ((a # b)%Q)))).
  { unfold Qlt. cbn [Qnum Qden Qmult]. pose proof Hsq. nia. }
  assert (HxD : Qle (ir2_x n0 * ir2_x n0 - ((a # b)%Q * ((a # b)%Q)))
                    (ir2_e n0 + ir2_e n0)).
  { pose proof (Qopp_le_compat 2%Q ((a # b)%Q * ((a # b)%Q))
                  (Qlt_le_weak _ _ Hq2)) as Hneg.
    pose proof (ir2_add_le_r (Qopp (((a # b)%Q * ((a # b)%Q)))) (Qopp 2%Q)
                  (ir2_x n0 * ir2_x n0) Hneg) as H1.
    assert (Hr : (Qopp 2%Q + ir2_x n0 * ir2_x n0
                   == ir2_x n0 * ir2_x n0 - 2%Q)%Q) by ring.
    rewrite Hr in H1.
    apply (Qle_trans _ (ir2_x n0 * ir2_x n0 - 2%Q)).
    - apply (Qle_trans _ (Qopp (((a # b)%Q * ((a # b)%Q)))
                            + ir2_x n0 * ir2_x n0)).
      + apply qeq_le. ring.
      + exact H1.
    - exact (qeq_le _ _ Hdww). }
  (* (x−q)(x+q) == x²−q² ≤ 2w 且 x+q ≥ 14/5 ⟹ D·(14/5) ≤ 2w *)
  assert (Hsum : Qle (14 # 5) (ir2_x n0 + ((a # b)%Q))).
  { apply (Qle_trans (14 # 5) ((7 # 5) + (7 # 5))%Q).
    - apply qeq_le. ring.
    - apply (Qplus_le_compat (7 # 5) (ir2_x n0) (7 # 5) ((a # b)%Q));
        [exact Hxlb | exact Hq75]. }
  assert (HDge0 : Qle 0%Q (ir2_x n0 - (a # b)%Q))
    by (apply Qlt_le_weak; exact (lic_qlt_0_minus ((a # b)%Q) (ir2_x n0) Hqx)).
  assert (Hmul1 : Qle ((ir2_x n0 - (a # b)%Q) * (14 # 5))
                      ((ir2_x n0 - (a # b)%Q) * (ir2_x n0 + (a # b)%Q))).
  { apply (ir2_mult_le_compat_l (14 # 5) (ir2_x n0 + ((a # b)%Q))
             (ir2_x n0 - (a # b)%Q));
      [exact Hsum | exact HDge0]. }
  assert (Hmul2 : Qle ((ir2_x n0 - (a # b)%Q) * (ir2_x n0 + (a # b)%Q))
                      (ir2_e n0 + ir2_e n0)).
  { apply (Qle_trans _ (ir2_x n0 * ir2_x n0
                          - ((a # b)%Q * ((a # b)%Q)))).
    - apply qeq_le. exact (ir2_sq_diff (ir2_x n0) ((a # b)%Q)).
    - exact HxD. }
  assert (Hkey : Qlt (ir2_e n0 * (14 # 5)) (ir2_e n0 + ir2_e n0)).
  { apply (Qlt_le_trans _ ((ir2_x n0 - (a # b)%Q) * (14 # 5))).
    - pose proof (b5_qlt_mul_pos_r (ir2_e n0)
                    (ir2_x n0 - (a # b)%Q) (14 # 5)
                    (lic_qlt_comp_r (Qabs (((a # b)%Q - ir2_x n0)%Q))
                       (ir2_x n0 - (a # b)%Q) (ir2_e n0)
                       HD HescQ)
                    (ltac:(unfold Qlt; cbn [Qnum Qden]; lia))) as HH.
      exact HH.
    - exact (Qle_trans _ _ _ Hmul1 Hmul2). }
  (* (14/5)w < 2w ⟹ (4/5)w < 0 与 w>0 矛盾 *)
  assert (Hcontra : Qlt ((4 # 5) * ir2_e n0) 0%Q).
  { apply (lic_qlt_add_l_cancel (ir2_e n0 + ir2_e n0) ((4 # 5) * ir2_e n0) 0%Q).
    rewrite Qplus_0_r.
    rewrite (Qplus_comm (ir2_e n0 + ir2_e n0) ((4 # 5) * ir2_e n0)).
    assert (Hr1 : (ir2_e n0 * (14 # 5) == (4 # 5) * ir2_e n0
                     + (ir2_e n0 + ir2_e n0))%Q) by ring.
    rewrite <- Hr1. exact Hkey. }
  pose proof (Qmult_lt_0_compat (4 # 5) (ir2_e n0)
                (ltac:(unfold Qlt; cbn [Qnum Qden]; lia)) He0) as Hpos2.
  exact (Qlt_not_eq 0%Q 0%Q
           (Qlt_trans 0%Q _ 0%Q Hpos2 Hcontra) (Qeq_refl 0%Q)).
Qed.

(* 分支 C：a²>2b² ∧ |a|≤2b ∧ x ≤ q *)
Lemma b5_margin_C : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  (2 * (Z.pos b * Z.pos b) < a * a)%Z ->
  (Z.abs a <= 2 * Z.pos b)%Z ->
  Qle (ir2_x n0) ((a # b)%Q) ->
  Qle (ir2_e n0) (1 # (112 * (b * b)))%Q ->
  QltT (b5_cert a b + (ir2_e n0 + ir2_e n0)) (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Hsq Hab Hxq Hwin.
  pose proof (ir2_x_ub n0 Hn01) as Hxub.
  pose proof (ir2_x_pos n0) as Hxpos.
  pose proof (b5_delta_ww n0) as Hdww.
  assert (Hlo : (1 <= a * a - 2 * (Z.pos b * Z.pos b))%Z) by lia.
  assert (Hq0 : Qlt 0%Q ((a # b)%Q))
    by (apply (Qlt_le_trans 0%Q (ir2_x n0)); [exact Hxpos | exact Hxq]).
  assert (Hii : Qle ((1 # (b * b))%Q)
                    (((a # b)%Q * ((a # b)%Q)) - 2%Q)).
  { unfold Qle, Qminus. cbn [Qnum Qden Qmult Qplus Qopp]. nia. }
  assert (Hcq : Qle (b5_cert a b * (ir2_x n0 + ((a # b)%Q)))
                    (7 # (8 * (b * b)))).
  { apply (b5_cert_mul_le a b).
    apply (Qle_trans (ir2_x n0 + ((a # b)%Q))
                     (((3 # 2) + ((Z.abs a) # b)%Q))
                     (((b5_den a b) # 1) * (7 # (8 * (b * b)))%Q)).
    - apply (Qle_trans _ (ir2_x n0 + ((Z.abs a) # b)%Q)).
      + apply Qplus_le_compat; [apply Qle_refl | apply b5_q_le_absden].
      + apply Qplus_le_compat; [exact Hxub | apply Qle_refl].
    - unfold Qle. cbn [Qnum Qden Qmult Qplus]. unfold b5_den. nia. }
  assert (Hwwq : Qle ((ir2_e n0 + ir2_e n0) * (ir2_x n0 + ((a # b)%Q)))
                     (7 # (112 * (b * b)))).
  { pose proof (b5_ww_le b n0 Hwin) as Hww2.
    pose proof (ir2_qpos_add ((a # b)%Q) (ir2_x n0) Hq0 Hxpos) as Hsum0.
    setoid_rewrite (Qplus_comm ((a # b)%Q) (ir2_x n0)) in Hsum0.
    apply (Qle_trans _ ((2 # (112 * (b * b)))%Q
                          * (ir2_x n0 + ((a # b)%Q)))).
    - apply Qmult_le_compat_r;
        [exact Hww2 | apply Qlt_le_weak; exact Hsum0].
    - apply (Qle_trans _ ((2 # (112 * (b * b)))%Q * ((7 # 2)%Q))).
      + apply ir2_mult_le_compat_l.
        * apply (Qle_trans _ (ir2_x n0 + ((Z.abs a) # b)%Q)).
          -- apply Qplus_le_compat;
               [apply Qle_refl | apply b5_q_le_absden].
          -- apply (Qle_trans _ (((3 # 2) + ((Z.abs a) # b)%Q))).
             ++ apply Qplus_le_compat; [exact Hxub | apply Qle_refl].
             ++ apply (Qle_trans _ (((3 # 2) + (2 # 1)%Q))).
                ** apply Qplus_le_compat;
                     [apply Qle_refl | unfold Qle; cbn [Qnum Qden]; nia].
                ** apply qeq_le. ring.
        * unfold Qle. cbn [Qnum Qden]. nia.
      + apply qeq_le. unfold Qeq. cbn [Qnum Qden Qmult]. nia. }
  assert (Htotal : Qlt ((b5_cert a b + (ir2_e n0 + ir2_e n0))
                          * (ir2_x n0 + ((a # b)%Q))
                          + (ir2_e n0 + ir2_e n0))
                       ((1 # (b * b))%Q)).
  { pose proof (Qmult_plus_distr_l (b5_cert a b) (ir2_e n0 + ir2_e n0)
                  (ir2_x n0 + ((a # b)%Q))) as Hdistr.
    apply (Qle_lt_trans _ ((7 # (8 * (b * b)))%Q + (7 # (112 * (b * b)))%Q
                             + (2 # (112 * (b * b)))%Q)).
    - rewrite Hdistr.
      apply (Qle_trans _ ((b5_cert a b) * (ir2_x n0 + ((a # b)%Q))
                            + (ir2_e n0 + ir2_e n0) * (ir2_x n0 + ((a # b)%Q))
                            + (ir2_e n0 + ir2_e n0))).
      + apply qeq_le. ring.
      + apply (Qplus_le_compat
                 ((b5_cert a b) * (ir2_x n0 + ((a # b)%Q))
                    + (ir2_e n0 + ir2_e n0) * (ir2_x n0 + ((a # b)%Q)))
                 ((7 # (8 * (b * b)))%Q + (7 # (112 * (b * b)))%Q)
                 (ir2_e n0 + ir2_e n0) (2 # (112 * (b * b))));
          [apply (Qplus_le_compat (b5_cert a b * (ir2_x n0 + ((a # b)%Q)))
                    (7 # (8 * (b * b)))
                    ((ir2_e n0 + ir2_e n0) * (ir2_x n0 + ((a # b)%Q)))
                    (7 # (112 * (b * b))));
             [exact Hcq | exact Hwwq]
          | apply (b5_ww_le b n0 Hwin)].
    - unfold Qlt. cbn [Qnum Qden Qplus]. nia. }
  assert (Hge2 : Qle ((1 # (b * b))%Q + Qopp (ir2_e n0 + ir2_e n0))
                     (((a # b)%Q * ((a # b)%Q))
                        - (ir2_x n0 * ir2_x n0))).
  { pose proof (ir2_add_le_r ((1 # (b * b))%Q)
                  (((a # b)%Q * ((a # b)%Q)) - 2%Q)
                  (Qopp (ir2_e n0 + ir2_e n0)) Hii) as H1.
    apply (Qle_trans _ (((a # b)%Q * ((a # b)%Q)) - 2%Q
                          + Qopp (ir2_e n0 + ir2_e n0))).
    - exact H1.
    - apply qeq_le.
      assert (Hd2 : (ir2_e n0 + ir2_e n0
                       == ir2_x n0 * ir2_x n0 - 2%Q)%Q)
        by (unfold ir2_e, ir2_delta; ring).
      rewrite Hd2. ring. }
  assert (Hkey : Qlt (b5_cert a b + (ir2_e n0 + ir2_e n0))
                     (((a # b)%Q) - ir2_x n0)).
  { apply (b5_qlt_mul_pos_cancel_r (b5_cert a b + (ir2_e n0 + ir2_e n0))
             (((a # b)%Q) - ir2_x n0) (ir2_x n0 + ((a # b)%Q))).
    - apply (Qlt_le_trans _ ((1 # (b * b))%Q + Qopp (ir2_e n0 + ir2_e n0))).
      + apply (lic_qlt_add_r_cancel_r
                 ((b5_cert a b + (ir2_e n0 + ir2_e n0))
                    * (ir2_x n0 + ((a # b)%Q)))
                 ((1 # (b * b))%Q + Qopp (ir2_e n0 + ir2_e n0))
                 (ir2_e n0 + ir2_e n0)).
        apply (lic_qlt_comp_r (1 # (b * b))%Q
                (((1 # (b * b))%Q + Qopp (ir2_e n0 + ir2_e n0))
                   + (ir2_e n0 + ir2_e n0))).
        * apply Qeq_sym.
          exact (lic_qlt_minus_add_r (1 # (b * b)) (ir2_e n0 + ir2_e n0)).
        * exact Htotal.
      + apply (Qle_trans _ (((a # b)%Q * ((a # b)%Q))
                              - (ir2_x n0 * ir2_x n0))).
        * exact Hge2.
        * apply qeq_le. apply Qeq_sym. ring.
    - pose proof (ir2_qpos_add ((a # b)%Q) (ir2_x n0) Hq0 Hxpos) as Hsum.
      setoid_rewrite (Qplus_comm ((a # b)%Q) (ir2_x n0)) in Hsum.
      exact Hsum. }
  apply Qlt_to_QltT.
  rewrite (ir2_abs_sub ((a # b)%Q) (ir2_x n0) Hxq).
  exact Hkey.
Qed.

(* 分派器：整值定侧一次定死（a² vs 2b²·|a| vs 2b·q vs x）＋sliver 消去 *)
Lemma b5_margin_nonhalf : forall (a : Z) (b : positive) (n0 : nat),
  (1 <= n0)%nat ->
  QleT' (ir2_e n0) ((Qinv ((112 * (Z.pos b * Z.pos b)) # 1))%Q) ->
  QltT (ir2_e n0) (Qabs (((a # b)%Q - ir2_x n0)%Q)) ->
  QltT (b5_cert a b + (ir2_e n0 + ir2_e n0))
       (Qabs (((a # b)%Q - ir2_x n0)%Q)).
Proof.
  intros a b n0 Hn01 Hwin Hesc.
  assert (HwinQ : Qle (ir2_e n0) (1 # (112 * (b * b)))%Q).
  { assert (Hnum : (112 * (Z.pos b * Z.pos b))%Z = Z.pos (112 * (b * b)))
      by reflexivity.
    pose proof (qeqT_imp_qeq _ _ (dmew_Qinv_1p (112 * (b * b)))) as Hq112.
    pose proof (QleT'_to_Qle _ _ Hwin) as HwinQ.
    rewrite Hnum in HwinQ. rewrite Hq112 in HwinQ.
    exact HwinQ. }
  destruct (Z_le_gt_dec (a * a) (2 * (Z.pos b * Z.pos b))) as [HA | HB].
  - exact (b5_margin_A a b n0 Hn01 HA HwinQ Hesc).
  - assert (Hgt : (2 * (Z.pos b * Z.pos b) < a * a)%Z) by lia.
    destruct (Z_le_gt_dec (Z.abs a) (2 * Z.pos b)) as [HC | HDx].
    + destruct (Qlt_bool ((a # b)%Q) (ir2_x n0)) eqn:Hqx.
      * destruct (Qlt_bool 0%Q ((a # b)%Q)) eqn:Hq0b.
        -- exfalso.
           exact (b5_margin_sliver a b n0 Hn01 Hgt HC HwinQ Hesc
                    (lic_qlt_bool_true 0%Q ((a # b)%Q) Hq0b)
                    (lic_qlt_bool_true ((a # b)%Q) (ir2_x n0) Hqx)).
        -- exact (b5_margin_nonpos a b n0 Hn01 HwinQ
                   (lic_qlt_bool_false_le 0%Q ((a # b)%Q) Hq0b)).
      * exact (b5_margin_C a b n0 Hn01 Hgt HC
                 (lic_qlt_bool_false_le ((a # b)%Q) (ir2_x n0) Hqx) HwinQ).
    + assert (HabsB : (2 * Z.pos b < Z.abs a)%Z) by lia.
      exact (b5_margin_B a b n0 Hn01 Hgt HabsB HwinQ).
Qed.

(* ============================================================ *)
(* §W 窗口：e(n) ≤ 1/(112b²)（n ≥ b+4；δ/28 衰减一步）               *)
(* ============================================================ *)

Lemma b5_win112 : forall (b : positive) (n : nat),
  (Z.to_nat (Z.pos b) + 4 <= n)%nat ->
  QleT' (ir2_e n) ((Qinv ((112 * (Z.pos b * Z.pos b)) # 1))%Q).
Proof.
  intros b n Hn. apply Qle_to_QleT'.
  destruct n as [|m]; [lia|].
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (Hb3 : (Z.to_nat (Z.pos b) + 3 <= m)%nat) by lia.
  assert (E112 : (112 * (Z.pos b * Z.pos b))%Z = Z.pos (112 * (b * b)))
    by reflexivity.
  assert (E12 : (12 * (Z.pos b * Z.pos b))%Z = Z.pos (12 * (b * b)))
    by reflexivity.
  apply (Qle_trans (ir2_e (Datatypes.S m))
                   (((1 # 28) * ir2_e m)%Q)
                   ((Qinv ((112 * (Z.pos b * Z.pos b)) # 1))%Q)).
  - apply (b5_e_decay28 m). exact Hm1.
  - apply (Qle_trans _ (((1 # 28)
                            * ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q))%Q)).
    + apply (ir2_mult_le_compat_l (ir2_e m)
               ((Qinv ((12 * (Z.pos b * Z.pos b)) # 1))%Q) (1 # 28)).
      * apply QleT'_to_Qle. apply (dmew_e_bnd b m). exact Hb3.
      * unfold Qle. cbn [Qnum Qden]. lia.
    + pose proof (qeqT_imp_qeq _ _ (dmew_Qinv_1p (112 * (b * b)))) as Hq112.
      pose proof (qeqT_imp_qeq _ _ (dmew_Qinv_1p (12 * (b * b)))) as Hq12.
      rewrite E112. rewrite Hq112.
      rewrite E12. rewrite Hq12.
      unfold Qle. cbn [Qnum Qden Qmult]. nia.
Qed.

(* ============================================================ *)
(* §E 逃逸自举：e(n')<D(n') ⟹ e(n'+1)<D(n'+1)（5/7-窗比）            *)
(* ============================================================ *)

Lemma b5_esc_step : forall (q : Q) (n : nat), (1 <= n)%nat ->
  QltT (ir2_e n) (Qabs ((q - ir2_x n)%Q)) ->
  QltT (ir2_e (Datatypes.S n)) (Qabs ((q - ir2_x (Datatypes.S n))%Q)).
Proof.
  intros q n Hn1 Hesc.
  pose proof (QltT_to_Qlt _ _ Hesc) as HescQ.
  pose proof (ir2_x_lb n) as Hxlb.
  pose proof (ir2_x_lb (Datatypes.S n)) as Hylb.
  pose proof (ir2_x_pos n) as Hxpos.
  pose proof (ir2_mono n) as Hmono.
  pose proof (ir2_delta_ge0 (Datatypes.S n)) as Hd'0.
  pose proof (b5_e_pos n) as He0.
  (* w' ≤ w/28 *)
  assert (Hw' : Qle (ir2_e (Datatypes.S n)) (((1 # 28) * ir2_e n)%Q))
    by (apply (b5_e_decay28 n); exact Hn1).
  (* x(n)−x(n+1) ≤ (5/7)·w *)
  assert (Hsumpos : Qlt 0 (ir2_x n + ir2_x (Datatypes.S n))).
  { apply (ir2_qpos_add (ir2_x n) (ir2_x (Datatypes.S n)));
      [exact Hxpos | apply (ir2_x_pos _)]. }
  assert (Hne0 : ~ ((ir2_x n + ir2_x (Datatypes.S n)) == 0%Q)).
  { intro Hc. apply Qeq_sym in Hc.
    exact (Qlt_not_eq 0%Q _ Hsumpos Hc). }
  pose proof (bno_mul_div_self (ir2_x n + ir2_x (Datatypes.S n)) Hne0) as Hb.
  unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
  assert (Hdd : ((ir2_x n - ir2_x (Datatypes.S n))
                  == (ir2_delta n - ir2_delta (Datatypes.S n))
                     * Qinv (ir2_x n + ir2_x (Datatypes.S n)))%Q).
  { assert (Hpm : (((ir2_x n - ir2_x (Datatypes.S n))
                      * (ir2_x n + ir2_x (Datatypes.S n)))
                     * Qinv (ir2_x n + ir2_x (Datatypes.S n)))
                  == (ir2_x n - ir2_x (Datatypes.S n))%Q).
    { rewrite <- (Qmult_assoc _ _ _). rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsq2 : ((ir2_x n * ir2_x n
                      - ir2_x (Datatypes.S n) * ir2_x (Datatypes.S n))
                     == (ir2_delta n - ir2_delta (Datatypes.S n)))%Q)
      by (unfold ir2_delta; ring).
    rewrite Hsq2 in Hpm. apply Qeq_sym. exact Hpm. }
  assert (Hinvle : Qle (Qinv (ir2_x n + ir2_x (Datatypes.S n)))
                       (Qinv (14 # 5))).
  { apply (ir2_inv_le (14 # 5) (ir2_x n + ir2_x (Datatypes.S n))).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - apply (Qle_trans _ ((7 # 5) + (7 # 5))%Q).
      + apply qeq_le. ring.
      + apply (Qplus_le_compat (7 # 5) (ir2_x n) (7 # 5)
                 (ir2_x (Datatypes.S n)));
          [exact Hxlb | exact Hylb]. }
  assert (Hle1 : Qle ((ir2_delta n - ir2_delta (Datatypes.S n))
                        * Qinv (ir2_x n + ir2_x (Datatypes.S n)))
                     (ir2_delta n * Qinv (14 # 5))).
  { apply (Qle_trans _ (ir2_delta n * Qinv (ir2_x n + ir2_x (Datatypes.S n)))).
    - pose proof (Qopp_le_compat 0%Q (ir2_delta (Datatypes.S n)) Hd'0) as Hng.
      cbn [Qopp Z.opp] in Hng.
      apply (Qmult_le_compat_r (ir2_delta n - ir2_delta (Datatypes.S n))
               (ir2_delta n) (Qinv (ir2_x n + ir2_x (Datatypes.S n))));
        [pose proof (Qplus_le_compat (ir2_delta n) (ir2_delta n)
                   (Qopp (ir2_delta (Datatypes.S n))) 0%Q
                   (Qle_refl (ir2_delta n)) Hng) as Hst;
         assert (Hrz : (ir2_delta n + 0%Q == ir2_delta n)%Q) by ring;
         rewrite Hrz in Hst; exact Hst
        | apply (ir2_inv_pos _ Hsumpos)].
    - apply (ir2_mult_le_compat_l (Qinv (ir2_x n + ir2_x (Datatypes.S n)))
               (Qinv (14 # 5)) (ir2_delta n));
        [exact Hinvle | exact (ir2_delta_ge0 n)]. }
  assert (Hle2 : Qle (ir2_delta n * Qinv (14 # 5)) (((5 # 7) * ir2_e n)%Q)).
  { replace (Qinv (14 # 5)) with ((5 # 14)%Q) by reflexivity.
    apply (Qle_trans _ (ir2_delta n * (5 # 14)%Q)).
    - apply Qle_refl.
    - apply qeq_le. rewrite (b5_delta_ww n). ring. }
  assert (Hxy : Qle (ir2_x n - ir2_x (Datatypes.S n)) (((5 # 7) * ir2_e n)%Q)).
  { apply (Qle_trans _ ((ir2_delta n - ir2_delta (Datatypes.S n))
                          * Qinv (ir2_x n + ir2_x (Datatypes.S n)))).
    - rewrite Hdd. apply Qle_refl.
    - exact (Qle_trans _ _ _ Hle1 Hle2). }
  (* 反三角：D' ≥ D − (x−y) *)
  assert (HDd : Qabs ((ir2_x (Datatypes.S n) - ir2_x n)%Q)
                == (ir2_x n - ir2_x (Datatypes.S n))%Q).
  { rewrite (Qabs_Qminus (ir2_x (Datatypes.S n)) (ir2_x n)).
    apply ir2_abs_sub. exact Hmono. }
  assert (HT2 : Qle (Qabs ((q - ir2_x n)%Q))
                    (Qabs ((q - ir2_x (Datatypes.S n))%Q)
                       + (ir2_x n - ir2_x (Datatypes.S n)))).
  { pose proof (Qabs_triangle ((q - ir2_x (Datatypes.S n))%Q)
                  ((ir2_x (Datatypes.S n) - ir2_x n)%Q)) as HTR.
    apply (Qle_trans _ (Qabs (((q - ir2_x (Datatypes.S n))
                                + (ir2_x (Datatypes.S n) - ir2_x n))%Q))).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply (Qle_trans _ (Qabs ((q - ir2_x (Datatypes.S n))%Q)
                            + Qabs ((ir2_x (Datatypes.S n) - ir2_x n)%Q))).
      + exact HTR.
      + rewrite HDd. apply Qle_refl. }
  assert (Hz2 : Qle ((2 # 7) * ir2_e n)
                    (ir2_e n - (ir2_x n - ir2_x (Datatypes.S n)))).
  { pose proof (Qopp_le_compat (ir2_x n - ir2_x (Datatypes.S n))
                  ((5 # 7) * ir2_e n) Hxy) as Hng.
    apply (Qle_trans _ (ir2_e n + Qopp ((5 # 7) * ir2_e n))).
    - apply qeq_le. ring.
    - apply Qplus_le_compat; [apply Qle_refl | exact Hng]. }
  assert (Hlt2 : Qlt ((2 # 7) * ir2_e n)
                     (Qabs ((q - ir2_x n)%Q)
                        - (ir2_x n - ir2_x (Datatypes.S n)))).
  { pose proof (lic_qlt_add_l (Qopp (ir2_x n - ir2_x (Datatypes.S n)))
                  (ir2_e n) (Qabs ((q - ir2_x n)%Q)) HescQ) as HH.
    assert (Hzq : (Qopp (ir2_x n - ir2_x (Datatypes.S n)) + ir2_e n
                   == ir2_e n - (ir2_x n - ir2_x (Datatypes.S n)))%Q)
      by ring.
    assert (Hzq2 : (Qopp (ir2_x n - ir2_x (Datatypes.S n))
                      + Qabs ((q - ir2_x n)%Q)
                     == (Qabs ((q - ir2_x n)%Q)
                           - (ir2_x n - ir2_x (Datatypes.S n))))%Q)
      by ring.
    rewrite Hzq in HH. rewrite Hzq2 in HH.
    apply (Qle_lt_trans _ (ir2_e n - (ir2_x n - ir2_x (Datatypes.S n)))).
    - exact Hz2.
    - exact HH. }
  assert (Hle3 : Qle (Qabs ((q - ir2_x n)%Q)
                        - (ir2_x n - ir2_x (Datatypes.S n)))
                     (Qabs ((q - ir2_x (Datatypes.S n))%Q))).
  { pose proof (ir2_add_le_r (Qabs ((q - ir2_x n)%Q))
                  (Qabs ((q - ir2_x (Datatypes.S n))%Q)
                     + (ir2_x n - ir2_x (Datatypes.S n)))
                  (Qopp (ir2_x n - ir2_x (Datatypes.S n))) HT2) as HH.
    apply (Qle_trans _ (Qabs ((q - ir2_x (Datatypes.S n))%Q)
                          + (ir2_x n - ir2_x (Datatypes.S n))
                          + Qopp (ir2_x n - ir2_x (Datatypes.S n)))).
    - exact HH.
    - apply qeq_le. ring. }
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ ((2 # 7) * ir2_e n)).
  - exact (Qle_lt_trans _ _ _ Hw'
             (b5_qlt_mul_pos_r (1 # 28) (2 # 7) (ir2_e n)
                (ltac:(unfold Qlt; cbn [Qnum Qden]; lia)) He0)).
  - apply Qlt_le_weak.
    exact (Qlt_le_trans _ _ _ Hlt2 Hle3).
Qed.

(* ============================================================ *)
(* §T 终形装配：b5_sqrt2_nonhalf（u5c 同形·c QeqT 钉定·零前提）        *)
(* ============================================================ *)

Theorem b5_sqrt2_nonhalf : forall (a : Z) (b : positive),
  sigT (fun c : Q => And (QeqT c (b5_cert a b))
    (And (QltT 0 c)
      (real_lt (real_const c)
        (real_metric (existT (fun u : Qseq => cauchy u) ir2_x
                          (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
                   (real_const ((a # b)%Q)))))).
Proof.
  intros a b.
  destruct (dmew_escape_closed_window a b) as [np [Hnp Hescp]].
  pose proof (b5_esc_step ((a # b)%Q) np (ltac:(lia)) Hescp) as Hesc1.
  exists (b5_cert a b).
  split. apply b5_cert_eq.
  split.
  + apply b5_cert_pos.
  + apply (b5_escape_dist ((a # b)%Q) (Datatypes.S np)).
    * lia.
    * exact Hesc1.
    * apply (b5_margin_nonhalf a b (Datatypes.S np)).
      -- lia.
      -- apply b5_win112. lia.
      -- exact Hesc1.
Qed.

(* ============================================================ *)
(* §A 审计：PA＋Separate Extraction＋锐化样例 vm_compute              *)
(* ============================================================ *)

Print Assumptions b5_den_pos.
Print Assumptions b5_cert_pos.
Print Assumptions b5_cert_eq.
Print Assumptions b5_gap_ge1.
Print Assumptions b5_sq_diff_abs.

(* 锐化样例一：22/7 处 B5 证书 1/252 严格大于现役 1/588（2.33×） *)
Lemma b5_smoke_22_7 : (Qlt_bool (1 # 588)%Q (b5_cert 22 7)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 锐化样例二：239/169（Pell 收敛子）处 1/97513 > 1/342732（3.51×） *)
Lemma b5_smoke_239_169 : (Qlt_bool (1 # 342732)%Q (b5_cert 239 169)) = true.
Proof. vm_compute. reflexivity. Qed.

(* 正性样例（负元） *)
Lemma b5_smoke_pos : (Qlt_bool 0%Q (b5_cert (-22) 7)) = true.
Proof. vm_compute. reflexivity. Qed.

(* RunAlive 末棒档样例：22/7 于 n0 := 11（=b+4）处全链边距数值锚 *)
Lemma b5_smoke_nonhalf_22_7 :
  (Qlt_bool (b5_cert 22 7 + (ir2_e 11 + ir2_e 11))
            (Qabs ((22 # 7)%Q - ir2_x 11))) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions b5_smoke_22_7.
Print Assumptions b5_smoke_239_169.
Print Assumptions b5_smoke_pos.
Print Assumptions b5_escape_dist.
Print Assumptions b5_margin_nonhalf.
Print Assumptions b5_win112.
Print Assumptions b5_esc_step.
Print Assumptions b5_sqrt2_nonhalf.
Print Assumptions b5_smoke_nonhalf_22_7.

From Stdlib Require Import Extraction.
Separate Extraction b5_cert b5_gap_ge1 b5_sq_diff_abs b5_smoke_22_7.
Separate Extraction b5_escape_dist b5_margin_nonhalf b5_win112
  b5_esc_step b5_sqrt2_nonhalf b5_smoke_nonhalf_22_7.
