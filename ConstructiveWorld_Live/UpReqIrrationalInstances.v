(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   ir2_sqrt2_irrational_criterion（原 L1286，2 句玩具证）               *)
(*   ir2_qp_def（原 L238，2 句玩具证）                                    *)
(*   ir2_x1（原 L235，1 句玩具证）                                        *)
(*   ir2_zpos_xo（原 L200，2 句玩具证）                                   *)
(*   ir2_add_lt_r（原 L42，2 句玩具证）                                   *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqIrrationalInstances.v                                    *)
(*                                                               *)
(* 目的：母定理 lic_irrational_criterion 的第二实例装配：             *)
(*       ir2_sqrt2_irrational_criterion —— √2 的构造性无理性          *)
(*       （Q 层 Newton 迭代 x_{n+1} = (x_n + 2/x_n)/2，x_0 = 2，       *)
(*         误差窗 e_n = (x_n²−2)/2，显式指数衰减 1/2^{n+1}，          *)
(*         逃逸窗由 q² 对 2 的可判定比较 + 1/den(q)² 间隙供给；        *)
(*         vanish 复用 lic_vanish_e 的 N=den(eps)+1 配方）。          *)
(* 路线：C2R2 遗留配方（Q 层 Newton 近似列 + 显式误差窗）；             *)
(*       主定理真走 exact 装配（lic_irrational_criterion              *)
(*       ir2_x ir2_e ir2_tail ir2_escape ir2_vanish q），零旁路。     *)
(*       ln2 实例遗留（报告 §遗留：独立级数列需重写逃逸论证）。          *)
(* 命名：ir2_ 前缀（开工 grep 零撞名）。                              *)
(* 公理面：本件纯构造性（零经典逻辑、零排中、零认授（未证断言））；               *)
(*       语句面全 Set 层（sigT/And/real_lt/QltT 形，无 Prop 泄露位）；  *)
(*       证内 Prop（Qlt/Qle）仅作 Q 层推理脚手架，不进结论面。           *)
(* 依赖：UpReqIrrationalCriterion（母定理件，只读参照）；               *)
(*       Stdlib QArith、ZArith、Arith、Lia、Lra、Qfield。             *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.
From Stdlib Require Import Lia Setoid Morphisms Qfield.

(* ============================================================ *)
(* S0：Q 层通用小件                                                *)
(* ============================================================ *)

Lemma ir2_add_le_r : forall x y z : Q, Qle x y -> Qle (x + z) (y + z).
Proof.
  intros [xn xd] [yn yd] [zn zd]. unfold Qle in *.
  cbn [Qnum Qden Qplus] in *. nia.
Qed.

Lemma ir2_add_lt_r : forall x y z : Q, Qlt x y -> Qlt (x + z) (y + z).
Proof.
  intros x y z H.
  apply (lic_qlt_add_r x y z H).
Qed.

(* 非负平方单调：0 ≤ v ≤ u ⟹ v·v ≤ u·u *)
Lemma ir2_sq_mono : forall u v : Q, Qle 0 v -> Qle v u -> Qle (v*v) (u*u).
Proof.
  intros u v H0 H1.
  destruct u as [un ud]; destruct v as [vn vd].
  unfold Qle, Qmult in *. cbn [Qnum Qden] in *. nia.
Qed.

(* 正部平方比较逆：0 ≤ u、0 ≤ v 且 v·v < u·u ⟹ v < u *)
Lemma ir2_lt_of_sq : forall u v : Q, Qle 0 u -> Qle 0 v -> Qlt (v*v) (u*u) -> Qlt v u.
Proof.
  intros u v Hu0 Hv0 Hsq.
  destruct (Qlt_le_dec v u) as [Hlt | Hle].
  - exact Hlt.
  - exfalso.
    pose proof (ir2_sq_mono v u Hu0 Hle) as Hm.
    apply (Qlt_not_le (v*v) (u*u) Hsq Hm).
Qed.

(* 平方差恒等式 *)
Lemma ir2_sq_diff : forall u v : Q, ((u - v) * (u + v) == u * u - v * v)%Q.
Proof.
  intros u v. unfold Qminus. ring.
Qed.

(* |u − v| == u − v（u ≥ v） *)
Lemma ir2_abs_sub : forall u v : Q, Qle v u -> Qabs ((u - v)%Q) == (u - v)%Q.
Proof.
  intros u v H. apply Qabs_pos.
  unfold Qle in *. destruct u as [un ud]; destruct v as [vn vd].
  unfold Qminus, Qplus, Qopp. cbn [Qnum Qden] in *. lia.
Qed.

(* 正加正 *)
Lemma ir2_qpos_add : forall u v : Q, Qlt 0 u -> Qlt 0 v -> Qlt 0 (u + v).
Proof.
  intros [un ud] [vn vd]. assert (Hud : (0 < Z.pos ud)%Z) by apply Pos2Z.is_pos.
  assert (Hvd : (0 < Z.pos vd)%Z) by apply Pos2Z.is_pos.
  unfold Qlt, Qplus in *. cbn [Qnum Qden] in *. nia.
Qed.

(* 2/x > 0（x > 0） *)
Lemma ir2_div2_pos : forall v : Q, Qlt 0 v -> Qlt 0 (2%Q / v).
Proof.
  intros v Hv. unfold Qdiv.
  apply (Qmult_lt_0_compat (2#1) (Qinv v)).
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply (Qinv_lt_0_compat v Hv).
Qed.

Lemma ir2_inv_pos : forall w : Q, Qlt 0 w -> Qle 0 (Qinv w).
Proof.
  intros [wn wd] H. unfold Qlt, Qle, Qinv in *.
  destruct wn; cbn in *; try lia; nia.
Qed.

(* 乘后 ≤：X ≤ Y·M ⟹ X·M⁻¹ ≤ Y（0 < M）形态的等价小件 *)
Lemma ir2_le_of_mul_le : forall X Y M : Q,
  Qlt 0 M -> Qle (X * Qinv M) Y -> Qle X (Y * M).
Proof.
  intros X Y M Hm Hle.
  assert (HMne : ~ (M == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q M Hm (Qeq_sym _ _ Hc))).
  pose proof (bno_mul_div_self M HMne) as Hb. unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
  assert (Hb2 : (Qinv M * M == 1%Q)%Q)
    by (rewrite (Qmult_comm (Qinv M) M); exact Hb).
  apply (Qle_trans X ((X * Qinv M) * M)%Q).
  - rewrite <- (Qmult_assoc X (Qinv M) M). rewrite Hb2.
    apply qeq_le. symmetry. apply Qmult_1_r.
  - apply Qmult_le_compat_r; [exact Hle | apply Qlt_le_weak; exact Hm].
Qed.

(* 乘正除回：X·M ≤ Y 且 M > 0 ⟹ X ≤ Y·M⁻¹ *)
Lemma ir2_le_mul_inv : forall X Y M : Q,
  Qlt 0 M -> Qle (X * M) Y -> Qle X (Y * Qinv M).
Proof.
  intros X Y M Hm Hle.
  apply (ir2_le_of_mul_le X Y (Qinv M)).
  - destruct (Qlt_le_dec 0%Q (Qinv M)) as [Hi | Hi].
    + exact Hi.
    + exfalso. apply (Qlt_not_eq 0%Q M Hm).
      assert (Hz : (Qinv M == 0%Q)%Q)
        by (apply Qle_antisym; [exact Hi | apply ir2_inv_pos; exact Hm]).
      pose proof (Qinv_involutive M) as Hii. rewrite Hz in Hii. exact Hii.
  - rewrite Qinv_involutive. exact Hle.
Qed.

(* Qinv 严格反序：0 < u、0 < v 且 v < u ⟹ u⁻¹ < v⁻¹ *)
Lemma ir2_inv_lt : forall u v : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt v u -> Qlt (Qinv u) (Qinv v).
Proof.
  intros [un ud] [vn vd] Hu Hv Hlt. unfold Qlt, Qinv in *.
  destruct un; destruct vn; cbn in *; lia.
Qed.

(* Qinv 非严格反序：0 < u ≤ v ⟹ v⁻¹ ≤ u⁻¹ *)
Lemma ir2_inv_le : forall u v : Q, Qlt 0 u -> Qle u v -> Qle (Qinv v) (Qinv u).
Proof.
  intros [un ud] [vn vd]. unfold Qlt, Qle, Qinv in *.
  destruct un; destruct vn; cbn in *; try lia; nia.
Qed.

(* 左乘保 ≤：x ≤ y、0 ≤ z ⟹ z·x ≤ z·y（stdlib 只有右乘形 Qmult_le_compat_r） *)
Lemma ir2_mult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z Hxy Hz. rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_le_compat_r; assumption.
Qed.

(* ============================================================ *)
(* S1：Z 层——2 无有理平方根（无穷递降）                              *)
(* ============================================================ *)

Lemma ir2_even_of_sq_even : forall z : Z, Z.even (z * z) = true -> Z.even z = true.
Proof.
  intros z H. pose proof (Z.even_mul z z) as HM. rewrite HM in H.
  apply Bool.orb_true_iff in H. destruct H as [H | H]; exact H.
Qed.

Lemma ir2_no_sqrtZ : forall a b : Z, (0 < b)%Z -> (a * a = 2 * (b * b))%Z -> False.
Proof.
  assert (Hgen : forall n : nat, forall a b : Z, (0 < b)%Z ->
    (a * a = 2 * (b * b))%Z -> (Z.to_nat b <= n)%nat -> False).
  { induction n as [|n IH]; intros a b Hb Heq Hn.
    - assert (Hb0 : (b = 0)%Z).
      { pose proof (Z2Nat.id b (ltac:(lia))) as Hzz.
        apply Nat.le_0_r in Hn. rewrite Hn in Hzz. cbn in Hzz.
        symmetry. exact Hzz. }
      lia.
    - (* a 偶、b 偶、b 严格降 *)
      assert (Hae : Z.even a = true).
      { apply ir2_even_of_sq_even. rewrite Heq.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec a)) in Hae. destruct Hae as [a1 Ha1].
      assert (Hbb : (b * b = 2 * (a1 * a1))%Z) by lia.
      assert (Hbe : Z.even b = true).
      { apply ir2_even_of_sq_even. rewrite Hbb.
        rewrite Z.even_mul, Z.even_mul. cbn [Z.even]. reflexivity. }
      apply (proj1 (Z.even_spec b)) in Hbe. destruct Hbe as [b1 Hb1].
      apply (IH a1 b1).
      + lia.
      + rewrite Hb1 in Hbb.
        replace ((2 * b1) * (2 * b1))%Z with (4 * (b1 * b1))%Z in Hbb by ring.
        lia.
      + pose proof (Z2Nat.inj_mul b b1 (ltac:(lia)) (ltac:(lia))) as Hmm.
        pose proof (Z2Nat.id b (ltac:(lia))) as Hz1.
        pose proof (Z2Nat.id b1 (ltac:(lia))) as Hz2.
        lia. }
  intros a b Hb Heq.
  apply (Hgen (Z.to_nat b) a b Hb Heq (Nat.le_refl _)).
Qed.

Lemma ir2_zpos_xo : forall p : positive, (Z.pos (xO p) = 2 * Z.pos p)%Z.
Proof. intro p. exact eq_refl. Qed.

Lemma ir2_no_sqrt2 : forall q : Q, ~ (q * q == 2%Q).
Proof.
  intros q Hq. destruct q as [a b].
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (Heq : (a * a = 2 * (Z.pos b * Z.pos b))%Z).
  { unfold Qeq, Qmult in Hq. cbn in Hq.
    assert (Hb1 : (Z.pos (b * b) = Z.pos b * Z.pos b)%Z) by apply Pos2Z.inj_mul.
    assert (Hb2 : (Z.pos (b * b)~0 = 2 * Z.pos (b * b))%Z)
      by apply ir2_zpos_xo.
    lia. }
  exact (ir2_no_sqrtZ a (Z.pos b) Hb Heq).
Qed.

(* ============================================================ *)
(* S2：Newton 序列及其 Q 层基本量                                    *)
(* ============================================================ *)

Fixpoint ir2_x (n : nat) : Q :=
  match n with
  | O => 2%Q
  | Datatypes.S m => (ir2_x m + 2%Q / ir2_x m) * (1 # 2)
  end.

Definition ir2_delta (n : nat) : Q := ir2_x n * ir2_x n - 2%Q.
Definition ir2_e (n : nat) : Q := (1 # 2) * ir2_delta n.

Fixpoint ir2_qp (m : nat) : Q :=
  match m with
  | O => 1%Q
  | Datatypes.S m' => (2 # 1) * ir2_qp m'
  end.

Lemma ir2_x1 : ir2_x 1 == (3 # 2).
Proof. unfold Qeq. cbn. exact eq_refl. Qed.

Lemma ir2_qp_def : forall n : nat, ir2_qp (Datatypes.S n) == ((2 # 1) * ir2_qp n)%Q.
Proof. intros n. exact (Qeq_refl ((2 # 1) * ir2_qp n)%Q). Qed.

Lemma ir2_qp_pos : forall n : nat, Qlt 0 (ir2_qp n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [ir2_qp Qnum Qden]. lia.
  - cbn [ir2_qp]. apply (Qmult_lt_0_compat (2 # 1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + exact IH.
Qed.

(* qp n 就是 2^n（显式指数形态，供 vanish/escape 的 nat 幂比较） *)
Lemma ir2_qp_pow : forall n : nat, ir2_qp n == ((Z.of_nat (2 ^ n)) # 1)%Q.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite ir2_qp_def. rewrite IH.
    rewrite Nat.pow_succ_r'. rewrite Nat2Z.inj_mul.
    cbn [Z.of_nat]. reflexivity.
Qed.


(* 数值引理（nat 层） *)
Lemma ir2_pow_ge : forall j : nat, (Datatypes.S j <= 2 ^ j)%nat.
Proof.
  induction j as [|j IH].
  - cbn. lia.
  - replace (2 ^ Datatypes.S j)%nat with (2 * 2 ^ j)%nat
      by (rewrite Nat.pow_succ_r'; reflexivity).
    lia.
Qed.

(* 步进不等式（j ≥ 3 时 6j+3 ≤ 3j²、10j+5 ≤ 5j²；归纳 + ring 换形后纯线性，
   避免 nia 三假设乘积证书在本环境的失手） *)
Lemma ir2_step_le : forall j : nat, (3 <= j)%nat -> (6 * j + 3 <= 3 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (3 * Datatypes.S j * Datatypes.S j)%nat
      with (3 * j * j + 6 * j + 3)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|[|j'']]]; lia.
Qed.

Lemma ir2_step_le5 : forall j : nat, (3 <= j)%nat -> (10 * j + 5 <= 5 * j * j)%nat.
Proof.
  induction j as [|j IH]; intro Hj.
  - lia.
  - replace (5 * Datatypes.S j * Datatypes.S j)%nat
      with (5 * j * j + 10 * j + 5)%nat by ring.
    destruct (Nat.le_gt_cases 4 (Datatypes.S j)) as [Hj4 | Hjlt].
    + assert (Hj3 : (3 <= j)%nat) by lia.
      specialize (IH Hj3). lia.
    + destruct j as [|[|[|j'']]]; lia.
Qed.

Lemma ir2_pow3sq : forall j : nat, (3 * j * j <= 2 ^ (j + 8))%nat.
Proof.
  assert (Haux : forall j : nat, (3 * j * j <= 2 ^ (8 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (8 + Datatypes.S j)%nat with (Datatypes.S (8 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (3 * Datatypes.S j * Datatypes.S j)%nat
          with (3 * j * j + 6 * j + 3)%nat by ring.
        pose proof (ir2_step_le j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 8). apply Haux.
Qed.

Lemma ir2_pow5sq : forall j : nat, (5 * j * j <= 2 ^ (j + 4))%nat.
Proof.
  assert (Haux : forall j : nat, (5 * j * j <= 2 ^ (4 + j))%nat).
  { induction j as [|j IH].
    - apply (proj1 (Nat.leb_le _ _)). vm_compute. reflexivity.
    - replace (4 + Datatypes.S j)%nat with (Datatypes.S (4 + j))%nat by lia.
      rewrite Nat.pow_succ_r'.
      destruct (Nat.le_gt_cases 3 j) as [Hj3 | Hjlt].
      + replace (5 * Datatypes.S j * Datatypes.S j)%nat
          with (5 * j * j + 10 * j + 5)%nat by ring.
        pose proof (ir2_step_le5 j Hj3). lia.
      + destruct j as [|j'].
        * apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
        * destruct j' as [|j''].
          -- apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
          -- destruct j'' as [|j'''].
             ++ apply (proj1 (Nat.leb_le _ _)); vm_compute; reflexivity.
             ++ lia. }
  intro j. rewrite (Nat.add_comm j 4). apply Haux.
Qed.

(* ============================================================ *)
(* S3：序列基本性质（正性/下界/单调/δ 代数）                          *)
(* ============================================================ *)

Lemma ir2_x_pos : forall n : nat, Qlt 0 (ir2_x n).
Proof.
  induction n as [|n IH].
  - unfold Qlt. cbn [ir2_x Qnum Qden]. lia.
  - cbn [ir2_x]. apply (Qmult_lt_0_compat _ (1 # 2)).
    + apply ir2_qpos_add; [exact IH | apply ir2_div2_pos; exact IH].
    + unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Lemma ir2_delta_succ_mul : forall n : nat,
  (ir2_delta (Datatypes.S n) * (4 * (ir2_x n * ir2_x n)) == ir2_delta n * ir2_delta n)%Q.
Proof.
  intro n. unfold ir2_delta. cbn [ir2_x].
  field.
  intro Heq. apply (Qlt_not_eq 0%Q (ir2_x n) (ir2_x_pos n)).
  apply Qeq_sym. exact Heq.
Qed.

Lemma ir2_ge0_of_mul : forall A M : Q, Qlt 0 M -> Qle 0 (A * M) -> Qle 0 A.
Proof.
  intros [an ad] [mn md] Hm Hp. unfold Qlt, Qle, Qmult in *.
  cbn [Qnum Qden] in *. nia.
Qed.

Lemma ir2_delta_ge0 : forall n : nat, Qle 0 (ir2_delta n).
Proof.
  induction n as [|n IH].
  - unfold ir2_delta, Qle, Qmult, Qminus, Qplus, Qopp.
    cbn [ir2_x Qnum Qden]. lia.
  - assert (HM : Qlt 0%Q (4 * (ir2_x n * ir2_x n))).
    { apply (Qmult_lt_0_compat (4#1) (ir2_x n * ir2_x n)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - apply (Qmult_lt_0_compat (ir2_x n) (ir2_x n)); exact (ir2_x_pos n). }
    pose proof (ir2_delta_succ_mul n) as Hmul.
    assert (Hsq : Qle 0 (ir2_delta n * ir2_delta n)).
    { destruct (ir2_delta n) as [dn dd] eqn:Ed.
      pose proof IH as H0.
      rewrite ?Ed in H0. unfold Qle in H0. cbn [Qnum Qden] in H0.
      unfold Qle, Qmult. rewrite ?Ed. cbn [Qnum Qden]. nia. }
    apply (ir2_ge0_of_mul _ _ HM).
    rewrite Hmul. exact Hsq.
Qed.

Lemma ir2_delta_pos : forall n : nat, Qlt 0 (ir2_delta n).
Proof.
  intro n. pose proof (ir2_delta_ge0 n) as Hge.
  destruct (Qeq_dec (ir2_delta n) 0%Q) as [Hz | Hne].
  - exfalso. apply (ir2_no_sqrt2 (ir2_x n)).
    unfold ir2_delta in Hz.
    rewrite <- (lic_qlt_minus_add_r (ir2_x n * ir2_x n) 2%Q).
    rewrite Hz. reflexivity.
  - destruct (Qlt_le_dec 0%Q (ir2_delta n)) as [Hlt | Hle].
    + exact Hlt.
    + exfalso. apply Hne. apply (Qle_antisym (ir2_delta n) 0%Q Hle Hge).
Qed.

Lemma ir2_sq_ge2 : forall n : nat, Qle 2%Q (ir2_x n * ir2_x n).
Proof.
  intro n. pose proof (ir2_delta_ge0 n) as H.
  assert (Hr : ((ir2_x n * ir2_x n - 2) + 2 == ir2_x n * ir2_x n)%Q)
    by apply lic_qlt_minus_add_r.
  rewrite <- Hr.
  apply (Qle_trans 2%Q (0%Q + 2%Q)%Q ((ir2_x n * ir2_x n - 2)%Q + 2%Q)%Q).
  - rewrite Qplus_0_l. apply Qle_refl.
  - apply Qplus_le_compat; [exact H | apply Qle_refl].
Qed.

Lemma ir2_x_lb : forall n : nat, (7 # 5) <= ir2_x n.
Proof.
  intro n. pose proof (ir2_x_pos n) as Hp.
  destruct (Qlt_le_dec (ir2_x n) (7#5)) as [Hlt | Hle].
  - exfalso.
    assert (H1 : Qlt ((ir2_x n) * (ir2_x n)) ((7#5) * (ir2_x n))).
    { apply (Qmult_lt_compat_r (ir2_x n) (7#5) (ir2_x n)); [exact Hp | exact Hlt]. }
    assert (H2 : Qlt ((7#5) * (ir2_x n)) ((7#5) * (7#5))).
    { rewrite (Qmult_comm (7#5) (ir2_x n)).
      apply (Qmult_lt_compat_r (ir2_x n) (7#5) (7#5)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - exact Hlt. }
    assert (H3 : Qlt (ir2_x n * ir2_x n) 2%Q).
    { apply (Qlt_trans _ ((7#5) * (7#5))).
      - apply (Qlt_trans _ ((7#5) * (ir2_x n))); [exact H1 | exact H2].
      - unfold Qlt, Qmult. cbn [Qnum Qden]. lia. }
    apply (Qlt_not_le (ir2_x n * ir2_x n) 2%Q).
    + exact H3.
    + apply ir2_sq_ge2.
  - exact Hle.
Qed.

Lemma ir2_mono : forall n : nat, ir2_x (Datatypes.S n) <= ir2_x n.
Proof.
  intro n. cbn [ir2_x].
  pose proof (ir2_sq_ge2 n) as H2.
  pose proof (ir2_x_pos n) as Hxp.
  destruct (ir2_x n) as [a b] eqn:Ex.
  assert (Hb : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
  assert (H2c : (2 * Z.pos b * Z.pos b <= a * a)%Z).
  { pose proof H2 as H2'. rewrite ?Ex in H2'.
    unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'. nia. }
  assert (Hne : ~ ((a # b) == 0%Q)).
  { intro Hc. apply (Qlt_not_eq 0%Q (a # b) Hxp).
    apply Qeq_sym. exact Hc. }
  assert (Hbb : ((a # b) * Qinv (a # b))%Q == 1%Q).
  { pose proof (bno_mul_div_self (a # b) Hne) as Hbb0.
    unfold Qdiv in Hbb0. rewrite Qmult_1_l in Hbb0. exact Hbb0. }
  assert (Hivp : Qle 0%Q (Qinv (a # b)))
    by (apply ir2_inv_pos; exact Hxp).
  assert (Hinv : Qle (2%Q / (a # b)) (a # b)).
  { apply (Qle_trans _ (((a # b) * (a # b)) * Qinv (a # b))%Q).
    - apply Qmult_le_compat_r; [exact H2 | exact Hivp].
    - apply qeq_le.
      rewrite <- (Qmult_assoc (a # b) (a # b) (Qinv (a # b))).
      rewrite Hbb. apply Qmult_1_r. }
  apply (Qle_trans _ (((a # b) + (a # b)) * (1 # 2))%Q).
  - apply Qmult_le_compat_r.
    + apply (Qplus_le_compat (a # b) (a # b)
               (2%Q / (a # b)) (a # b));
        [apply Qle_refl | exact Hinv].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hr : ((((a # b) + (a # b)) * (1 # 2))
                   == (a # b))%Q) by ring.
    rewrite Hr. apply Qle_refl.
Qed.

Lemma ir2_mono_le : forall n k : nat, (1 <= n)%nat -> (n <= k)%nat ->
  ir2_x k <= ir2_x n.
Proof.
  intros n k Hn1 Hnk.
  assert (Hgen : forall d : nat, ir2_x (n + d) <= ir2_x n).
  { induction d as [|d IHd].
    - rewrite Nat.add_0_r. apply Qle_refl.
    - replace (n + Datatypes.S d)%nat with (Datatypes.S (n + d))%nat by lia.
      apply (Qle_trans _ (ir2_x (n + d))).
      + apply ir2_mono.
      + exact IHd. }
  replace k with (n + (k - n))%nat by lia.
  apply Hgen.
Qed.

Lemma ir2_x_ub : forall n : nat, (1 <= n)%nat -> ir2_x n <= (3 # 2).
Proof.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply (Qle_trans _ (ir2_x 1)).
    + apply (ir2_mono_le 1 (Datatypes.S n')); lia.
    + rewrite ir2_x1. apply Qle_refl.
Qed.

(* ============================================================ *)
(* S4：误差窗衰减（δ ≤ 1/4；δ(Sn) ≤ δn/28；e_n ≤ 1/2^{n+1}）          *)
(* ============================================================ *)

Lemma ir2_delta_step : forall n : nat, (1 <= n)%nat -> Qle (ir2_delta n) (1#4) ->
  Qle (ir2_delta (Datatypes.S n)) ((1#28) * ir2_delta n).
Proof.
  intros n Hn1 Hdu.
  pose proof (ir2_x_pos n) as Hxp.
  assert (Hlb : Qle ((7#5) * (7#5)) (ir2_x n * ir2_x n)).
  { apply (Qle_trans _ ((7#5) * ir2_x n)%Q).
    - apply ir2_mult_le_compat_l; [apply (ir2_x_lb n) | unfold Qle; cbn; lia].
    - apply Qmult_le_compat_r; [apply (ir2_x_lb n) | apply Qlt_le_weak; apply (ir2_x_pos n)]. }
  assert (H7 : Qle 7%Q (4 * (ir2_x n * ir2_x n))).
  { apply (Qle_trans _ ((4#1) * ((7#5) * (7#5)))%Q).
    - unfold Qle, Qmult. cbn [Qnum Qden]. lia.
    - rewrite (Qmult_comm (4#1) ((7#5) * (7#5))).
      rewrite (Qmult_comm (4#1) (ir2_x n * ir2_x n)).
      apply Qmult_le_compat_r; [exact Hlb | unfold Qle; cbn; lia]. }
  pose proof (ir2_delta_succ_mul n) as Hmul.
  pose proof (ir2_delta_ge0 (Datatypes.S n)) as HdS0.
  assert (Ha : Qle (7 * ir2_delta (Datatypes.S n)) (ir2_delta n * ir2_delta n)).
  { rewrite <- Hmul.
    rewrite (Qmult_comm (ir2_delta (Datatypes.S n)) (4 * (ir2_x n * ir2_x n))).
    apply Qmult_le_compat_r; [exact H7 | exact HdS0]. }
  assert (Hb : Qle (ir2_delta n * ir2_delta n) ((1#4) * ir2_delta n)).
  { apply (Qmult_le_compat_r (ir2_delta n) (1#4) (ir2_delta n));
      [exact Hdu | apply (ir2_delta_ge0 n)]. }
  assert (Hc : Qle (7 * ir2_delta (Datatypes.S n)) ((1#4) * ir2_delta n))
    by (apply (Qle_trans _ (ir2_delta n * ir2_delta n)); assumption).
  apply (Qle_trans (ir2_delta (Datatypes.S n))
    (((1#4) * ir2_delta n) * Qinv (7#1)) ((1#28) * ir2_delta n)).
  - apply (ir2_le_mul_inv (ir2_delta (Datatypes.S n)) ((1#4) * ir2_delta n) (7#1)).
    + unfold Qlt. cbn [Qnum Qden]. lia.
    + rewrite (Qmult_comm (ir2_delta (Datatypes.S n)) (7#1)). exact Hc.
  - assert (Hc2 : Qinv (7#1) == (1#7)%Q) by reflexivity.
    rewrite Hc2. apply qeq_le. ring.
Qed.

Lemma ir2_quarter : forall n : nat, (1 <= n)%nat -> Qle (ir2_delta n) (1#4).
Proof.
  induction n as [|n IH].
  - lia.
  - destruct n as [|n].
    + change (ir2_delta 1) with (4 # 16)%Q.
      unfold Qle. cbn [Qnum Qden]. lia.
    + intro Hle0. assert (Hn1 : (1 <= Datatypes.S n)%nat) by lia.
      pose proof (IH Hn1) as Hdu.
      apply (Qle_trans _ ((1#28) * ir2_delta (Datatypes.S n))).
      * apply (ir2_delta_step (Datatypes.S n)); [lia | exact Hdu].
      * apply (Qle_trans _ ((1#28) * (1#4))%Q).
        -- apply ir2_mult_le_compat_l; [exact Hdu | unfold Qle; cbn; lia].
        -- unfold Qle, Qmult. cbn [Qnum Qden]. lia.
Qed.

Lemma ir2_e_step : forall n : nat, (1 <= n)%nat ->
  Qle (ir2_e (Datatypes.S n)) ((1#2) * ir2_e n).
Proof.
  intros n Hn1. unfold ir2_e.
  apply (Qle_trans _ ((1#2) * ((1#28) * ir2_delta n))%Q).
  - rewrite (Qmult_comm (1#2) (ir2_delta (Datatypes.S n))).
    rewrite (Qmult_comm (1#2) ((1#28) * ir2_delta n)).
    pose proof (ir2_quarter n Hn1) as Hdu.
    apply Qmult_le_compat_r.
    + apply (ir2_delta_step n); [exact Hn1 | exact Hdu].
    + unfold Qle. cbn [Qnum Qden]. lia.
  - destruct (ir2_delta n) as [dn dd] eqn:Edn.
    pose proof (ir2_delta_ge0 n) as Hge. rewrite Edn in Hge.
    unfold Qle in Hge. cbn [Qnum Qden] in Hge.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qle, Qmult. cbn [Qnum Qden]. nia.
Qed.

Lemma ir2_e_to_delta : forall n : nat,
  (ir2_e n * ir2_qp (Datatypes.S n) == ir2_delta n * ir2_qp n)%Q.
Proof.
  intro n. unfold ir2_e. rewrite ir2_qp_def. ring.
Qed.

Lemma ir2_decay : forall n : nat,
  Qle (ir2_e (Datatypes.S n) * ir2_qp (Datatypes.S (Datatypes.S n))) 1%Q.
Proof.
  induction n as [|n IH].
  - change (ir2_e 1) with (4 # 32)%Q.
    change (ir2_qp 2) with (4 # 1)%Q.
    unfold Qle, Qmult. cbn [Qnum Qden]. lia.
  - apply (Qle_trans _ (((1#2) * ir2_e (Datatypes.S n))
                          * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))%Q).
    + rewrite ir2_qp_def.
      apply Qmult_le_compat_r.
      * apply (ir2_e_step (Datatypes.S n)). lia.
      * apply Qlt_le_weak.
        apply (Qmult_lt_0_compat (2#1) (ir2_qp (Datatypes.S (Datatypes.S n)))).
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- apply ir2_qp_pos.
    + rewrite ir2_qp_def.
      assert (Hr : ((((1#2) * ir2_e (Datatypes.S n))
                      * ((2#1) * ir2_qp (Datatypes.S (Datatypes.S n))))
                     == (ir2_e (Datatypes.S n)
                          * ir2_qp (Datatypes.S (Datatypes.S n))))%Q) by ring.
      rewrite Hr. exact IH.
Qed.

Lemma ir2_delta_pow_le : forall n : nat, (1 <= n)%nat ->
  Qle (ir2_delta n * ir2_qp n) 1%Q.
Proof.
  intros n Hn. rewrite <- (ir2_e_to_delta n).
  destruct n as [|n'].
  - lia.
  - apply (ir2_decay n').
Qed.

(* 1/M⁻¹ 形引理：0 < u 且 u·v ≤ 1 ⟹ v ≤ u⁻¹ *)
Lemma ir2_le_inv : forall u v : Q, Qlt 0 u -> Qle (u * v) 1%Q -> Qle v (Qinv u).
Proof.
  intros [un ud] [vn vd] Hm Hle. unfold Qlt, Qle, Qmult, Qinv in *.
  destruct un; cbn [Qnum Qden] in *; try lia; nia.
Qed.

(* 对偶：0 < u 且 1 ≤ u·v ⟹ u⁻¹ ≤ v *)
Lemma ir2_ge_inv : forall u v : Q, Qlt 0 u -> Qle 1 (u * v) -> Qle (Qinv u) v.
Proof.
  intros [un ud] [vn vd] Hm Hle. unfold Qlt, Qle, Qmult, Qinv in *.
  destruct un; cbn [Qnum Qden] in *; try lia; nia.
Qed.

(* ============================================================ *)
(* S5：逃逸间隙引理（√2 与任一有理数的 Q 层可判间隙）                    *)
(* ============================================================ *)

Lemma ir2_gap_lower : forall u v : Q,
  Qle 0 v -> Qle v u -> Qle u (3#2) -> Qle 2 (u*u) -> Qlt (v*v) 2 ->
  Qle ((2 - v*v) * (1#3)) (u - v).
Proof.
  intros u v Hv0 Hvu Hub H2 Hsq.
  assert (Hu0 : Qle 0 u) by (apply (Qle_trans 0 v u); assumption).
  assert (Huv0 : Qlt 0%Q (u + v)).
  { destruct (Qlt_le_dec 0%Q (u + v)) as [Hlt | Hle].
    - exact Hlt.
    - exfalso.
      assert (Huu : Qle u (u + v)).
      { apply (Qle_trans u (u + 0%Q) (u + v)).
        - apply qeq_le. symmetry. apply Qplus_0_r.
        - apply (Qplus_le_compat u u 0%Q v); [apply Qle_refl | exact Hv0]. }
      assert (Hu : u == 0%Q).
      { apply (Qle_antisym u 0%Q).
        - apply (Qle_trans u (u + v) 0%Q); [exact Huu | exact Hle].
        - exact Hu0. }
      pose proof H2 as H2'. rewrite Hu in H2'.
      unfold Qle, Qmult in H2'. cbn [Qnum Qden] in H2'.
      clear Hu Huu Hle. lia. }
  assert (Hne : ~ ((u + v)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (u + v) Huv0); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((u - v) == (u*u - v*v) * Qinv (u + v))%Q).
  { pose proof (bno_mul_div_self (u + v) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((u - v) * (u + v)) * Qinv (u + v)) == (u - v))%Q).
    { rewrite <- (Qmult_assoc (u - v) (u + v) (Qinv (u + v))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hw0 : Qle 0%Q (2 - v*v))
    by (apply Qlt_le_weak; apply (lic_qlt_0_minus (v*v) 2%Q Hsq)).
  assert (Hub3 : Qle (u + v) 3%Q).
  { apply (Qle_trans _ ((3#2) + (3#2))%Q).
    - apply (Qplus_le_compat u (3#2) v (3#2)).
      + exact Hub.
      + apply (Qle_trans v u (3#2)); assumption.
    - unfold Qle, Qplus, Qmult. cbn [Qnum Qden]. lia. }
  assert (Hivp : Qle 0%Q (Qinv (u + v))) by (apply ir2_inv_pos; exact Huv0).
  rewrite Hbridge.
  apply (Qle_trans _ ((u*u - v*v) * Qinv (u + v))%Q).
  - apply (Qle_trans _ ((2 - v*v) * Qinv (u + v))%Q).
    + apply ir2_mult_le_compat_l.
      * apply (ir2_inv_le (u + v) (3#1)); [exact Huv0 | exact Hub3].
      * exact Hw0.
    + apply Qmult_le_compat_r.
      * unfold Qminus. apply ir2_add_le_r. exact H2.
      * exact Hivp.
  - apply Qle_refl.
Qed.

Lemma ir2_gap_upper_small : forall u v d : Q,
  Qlt 0 u -> Qlt 0 v -> Qlt u v -> Qle v (3#2) -> Qlt 2 (v*v) ->
  d == (u*u - 2) -> Qle 0 d -> Qle d ((2#5) * (v*v - 2)) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Hv0 Huv Hv32 Hsq Hd Hdu Hdle.
  assert (Hw0 : Qlt 0 (v*v - 2)) by (apply (lic_qlt_0_minus 2%Q (v*v)); exact Hsq).
  assert (Hpu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; assumption).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpu (Qeq_sym _ _ Hc))).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 2) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
    destruct v as [vn vd].
    unfold Qlt, Qle, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hvup : Qlt (v + u) ((3#2) + (3#2))%Q).
  { apply (Qlt_le_trans (v + u) (v + v) ((3#2) + (3#2))).
    - apply (lic_qlt_add_l v u v Huv).
    - apply (Qplus_le_compat v (3#2) v (3#2)); [exact Hv32 | exact Hv32]. }
  apply (Qle_lt_trans (d * (1#2)) ((v*v - u*u) * (1#3)) (v - u)).
  - apply (Qle_trans _ ((1#5) * (v*v - 2))%Q).
    + destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
      rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
      unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
      cbn [Qnum Qden Qplus] in *.
      assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
      assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      lia.
    + assert (H35 : Qle ((3#5) * (v*v - 2)) (v*v - u*u)).
      { rewrite Hsh.
        destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
        rewrite ?Ew, ?Ed in Hw0, Hdle, Hdu.
        destruct v as [vn vd].
        unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
        cbn [Qnum Qden Qplus] in *.
        assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
        assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
        nia. }
      assert (Hr35 : (((1#3) * ((3#5) * (v*v - 2))) == ((1#5) * (v*v - 2)))%Q) by ring.
      apply (Qle_trans _ ((1#3) * ((3#5) * (v*v - 2)))%Q).
      * rewrite Hr35. apply Qle_refl.
      * rewrite (Qmult_comm (1#3) ((3#5) * (v*v - 2))).
        apply Qmult_le_compat_r; [exact H35 | unfold Qle; cbn; lia].
  - rewrite Hbridge.
    rewrite (Qmult_comm (v*v - u*u) (1#3)).
    rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
    apply (Qmult_lt_compat_r (1#3) (Qinv (v + u)) (v*v - u*u)).
    + exact Hvu2.
    + apply (ir2_inv_lt (3#1) (v + u)).
      * unfold Qlt. cbn [Qnum Qden]. lia.
      * exact Hpu.
      * apply (lic_qlt_comp_r ((3#2) + (3#2))%Q (3#1)%Q (v + u)).
        -- reflexivity.
        -- exact Hvup.
Qed.

Lemma ir2_gap_upper_big : forall u v d : Q,
  Qlt 0 u -> Qlt u v -> (3#2) <= v -> Qlt 2 (v*v) ->
  d == (u*u - 2) -> Qle 0 d -> Qle ((v + 1) * d) (v*v - 2) ->
  Qlt (d * (1#2)) (v - u).
Proof.
  intros u v d Hu0 Huv Hv32 Hsq Hd Hdu Hd1.
  assert (Hw0 : Qlt 0 (v*v - 2)) by (apply (lic_qlt_0_minus 2%Q (v*v)); exact Hsq).
  assert (Hvp : Qlt 0 v).
  { apply (Qlt_le_trans 0%Q (3#2) v); [unfold Qlt; cbn; lia | exact Hv32]. }
  assert (Hpvu : Qlt 0%Q (v + u)) by (apply ir2_qpos_add; [exact Hvp | exact Hu0]).
  assert (Hne : ~ ((v + u)%Q == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (v + u) Hpvu); rewrite Hc; apply Qeq_refl).
  assert (Hbridge : ((v - u) == (v*v - u*u) * Qinv (v + u))%Q).
  { pose proof (bno_mul_div_self (v + u) Hne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((v - u) * (v + u)) * Qinv (v + u)) == (v - u))%Q).
    { rewrite <- (Qmult_assoc (v - u) (v + u) (Qinv (v + u))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite (ir2_sq_diff v u) in Hpm. exact (Qeq_sym _ _ Hpm). }
  assert (Hsh : ((v*v - u*u) == ((v*v - 2) - d))%Q) by (rewrite Hd; ring).
  assert (Hvu2 : Qle 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (H2vp : Qlt 0%Q ((2#1) * v)).
  { apply (Qmult_lt_0_compat (2#1) v); [unfold Qlt; cbn; lia | exact Hvp]. }
  assert (Huv2 : Qle (v + u) ((2#1) * v)).
  { apply (Qle_trans (v + u) (v + v) ((2#1) * v)).
    - apply (Qplus_le_compat v v u v); [apply Qle_refl | apply Qlt_le_weak; exact Huv].
    - apply qeq_le. ring. }
  assert (Hdv : Qle (d * v) ((v*v - 2) - d)).
  { destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  assert (Hkey : Qle (d * (1#2)) (((v*v - 2) - d) * Qinv ((2#1) * v))).
  { apply (ir2_le_mul_inv (d * (1#2)) ((v*v - 2) - d) ((2#1) * v)).
    - exact H2vp.
    - assert (Hring : (((d * (1#2)) * ((2#1) * v)) == (d * v))%Q) by ring.
      rewrite Hring. exact Hdv. }
  assert (Hvu2p : Qlt 0 (v*v - u*u)).
  { rewrite Hsh.
    destruct (v*v - 2)%Q as [wn wd] eqn:Ew. destruct d as [dn dd] eqn:Ed.
    destruct v as [vn vd].
    rewrite ?Ew, ?Ed in Hw0, Hd1, Hdu.
    unfold Qle, Qlt, Qmult, Qminus, Qplus, Qopp in *.
    cbn [Qnum Qden Qplus] in *.
    assert (Hwd : (0 < Z.pos wd)%Z) by apply Pos2Z.is_pos.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    nia. }
  apply (Qle_lt_trans (d * (1#2)) (((v*v - 2) - d) * Qinv ((2#1) * v)) (v - u)).
  - exact Hkey.
  - apply (Qle_lt_trans ((v*v - 2 - d) * Qinv ((2#1) * v))
            ((v*v - u*u) * Qinv ((2#1) * v)) (v - u)).
    + assert (Hle2 : Qle (v*v - 2 - d) (v*v - u*u)).
      { rewrite Hd. apply qeq_le. ring. }
      apply Qmult_le_compat_r; [exact Hle2 | apply ir2_inv_pos; exact H2vp].
    + rewrite Hbridge.
      rewrite (Qmult_comm (v*v - u*u) (Qinv ((2#1) * v))).
      rewrite (Qmult_comm (v*v - u*u) (Qinv (v + u))).
      apply (Qmult_lt_compat_r (Qinv ((2#1) * v)) (Qinv (v + u)) (v*v - u*u)).
      * exact Hvu2p.
      * apply (ir2_inv_lt ((2#1) * v) (v + u)).
        -- exact H2vp.
        -- exact Hpvu.
        -- assert (Hr2 : (v + v == (2#1) * v)%Q) by ring.
           rewrite <- Hr2. apply (lic_qlt_add_l v u v Huv).
Qed.

(* ============================================================ *)
(* S6：母定理三前件实例（尾控/窗宽消失/逃逸窗）                         *)
(* ============================================================ *)

Definition ir2_tail : lic_tail_bounded ir2_x ir2_e.
Proof.
  intros n k Hn1 Hnk.
  pose proof (ir2_mono_le n k Hn1 Hnk) as Hmono.
  pose proof (ir2_delta_ge0 n) as Hd0n.
  pose proof (ir2_delta_pos n) as Hdpn.
  assert (Habs : Qabs ((ir2_x k - ir2_x n)%Q) == (ir2_x n - ir2_x k)%Q).
  { rewrite Qabs_Qminus. apply ir2_abs_sub. exact Hmono. }
  assert (Hsumpos : Qlt 0 (ir2_x n + ir2_x k)).
  { apply ir2_qpos_add.
    - apply (Qlt_le_trans 0%Q (7#5) (ir2_x n)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (ir2_x_lb n).
    - apply (Qlt_le_trans 0%Q (7#5) (ir2_x k)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (ir2_x_lb k). }
  assert (Hsumne : ~ ((ir2_x n + ir2_x k) == 0%Q))
    by (intro Hc; apply (Qlt_not_eq 0%Q (ir2_x n + ir2_x k) Hsumpos);
        rewrite Hc; apply Qeq_refl).
  assert (Hbridge : (((ir2_x n - ir2_x k)
                      == (ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))%Q)).
  { pose proof (bno_mul_div_self (ir2_x n + ir2_x k) Hsumne) as Hb.
    unfold Qdiv in Hb. rewrite Qmult_1_l in Hb.
    assert (Hpm : ((((ir2_x n - ir2_x k) * (ir2_x n + ir2_x k))
                    * Qinv (ir2_x n + ir2_x k)) == (ir2_x n - ir2_x k))%Q).
    { rewrite <- (Qmult_assoc (ir2_x n - ir2_x k) (ir2_x n + ir2_x k)
                    (Qinv (ir2_x n + ir2_x k))).
      rewrite Hb. apply Qmult_1_r. }
    rewrite ir2_sq_diff in Hpm.
    assert (Hsh : ((ir2_x n * ir2_x n - ir2_x k * ir2_x k)
                   == (ir2_delta n - ir2_delta k))%Q)
      by (unfold ir2_delta; ring).
    rewrite Hsh in Hpm. exact (Qeq_sym _ _ Hpm). }
  apply Qlt_to_QltT. rewrite Habs. rewrite Hbridge.
  assert (Hsumb : Qle ((14#5)) (ir2_x n + ir2_x k)).
  { apply (Qle_trans _ ((7#5) + (7#5))%Q).
    - apply qeq_le. reflexivity.
    - apply (Qplus_le_compat (7#5) (ir2_x n) (7#5) (ir2_x k));
        [apply (ir2_x_lb n) | apply (ir2_x_lb k)]. }
  assert (Hinvp : Qle 0%Q (Qinv (ir2_x n + ir2_x k)))
    by (apply ir2_inv_pos; exact Hsumpos).
  assert (Hstep1 : Qle ((ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))
                     (ir2_delta n * Qinv (ir2_x n + ir2_x k))).
  { apply Qmult_le_compat_r.
    - unfold Qminus, Qle, Qopp in *.
      destruct (ir2_delta n) as [dn dd] eqn:Edn.
      destruct (ir2_delta k) as [ek ed] eqn:Edk.
      pose proof (ir2_delta_ge0 k) as H0k.
      rewrite Edk in H0k. unfold Qle in H0k. cbn [Qnum Qden] in H0k.
      cbn [Qnum Qden Qplus Qopp Qmult].
      assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
      assert (Hed0 : (0 < Z.pos ed)%Z) by apply Pos2Z.is_pos.
      nia.
    - exact Hinvp. }
  assert (Hstep2 : Qle (ir2_delta n * Qinv (ir2_x n + ir2_x k))
                     (ir2_delta n * Qinv ((14#5)))).
  { rewrite (Qmult_comm (ir2_delta n) (Qinv (ir2_x n + ir2_x k))).
    rewrite (Qmult_comm (ir2_delta n) (Qinv ((14#5)))).
    apply Qmult_le_compat_r.
    - apply (ir2_inv_le (14#5) (ir2_x n + ir2_x k));
        [unfold Qlt; cbn [Qnum Qden]; lia | exact Hsumb].
    - exact Hd0n. }
  assert (Hstep3 : Qlt (ir2_delta n * Qinv ((14#5))) ((1#2) * ir2_delta n)).
  { destruct (ir2_delta n) as [dn dd] eqn:Edn.
    pose proof (ir2_delta_pos n) as Hdp.
    rewrite Edn in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
    assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
    unfold Qlt, Qmult, Qinv. cbn [Qnum Qden Qinv]. nia. }
  apply (Qle_lt_trans ((ir2_delta n - ir2_delta k) * Qinv (ir2_x n + ir2_x k))
          (ir2_delta n * Qinv (ir2_x n + ir2_x k)) ((1#2) * ir2_delta n)).
  - exact Hstep1.
  - apply (Qle_lt_trans (ir2_delta n * Qinv (ir2_x n + ir2_x k))
            (ir2_delta n * Qinv ((14#5))) ((1#2) * ir2_delta n)).
    + exact Hstep2.
    + exact Hstep3.
Defined.

Definition ir2_vanish : lic_vanish ir2_e.
Proof.
  intros eps Heps. destruct eps as [pn pd].
  pose proof (QltT_to_Qlt 0%Q (pn # pd) Heps) as Heps0.
  unfold Qlt in Heps0. cbn [Qnum Qden] in Heps0.
  assert (Hpn : (0 < pn)%Z) by lia.
  assert (Hpd : (0 < Z.pos pd)%Z) by apply Pos2Z.is_pos.
  exists (Z.to_nat (Z.pos pd) + 1)%nat.
  intros n Hn. destruct n as [|n'].
  - lia.
  - apply Qlt_to_QltT.
    apply (Qle_lt_trans (ir2_e (Datatypes.S n'))
            (Qinv (ir2_qp (Datatypes.S (Datatypes.S n')))) ((pn # pd)%Q)).
    + apply (ir2_le_inv (ir2_qp (Datatypes.S (Datatypes.S n')))
               (ir2_e (Datatypes.S n'))).
      * apply ir2_qp_pos.
      * rewrite (Qmult_comm (ir2_qp (Datatypes.S (Datatypes.S n')))
                            (ir2_e (Datatypes.S n'))).
        apply (ir2_decay n').
    + apply (Qlt_le_trans (Qinv (ir2_qp (Datatypes.S (Datatypes.S n'))))
              (Qinv (Z.pos pd # 1)) ((pn # pd)%Q)).
      * apply (ir2_inv_lt (ir2_qp (Datatypes.S (Datatypes.S n'))) (Z.pos pd # 1)).
        -- apply ir2_qp_pos.
        -- unfold Qlt. cbn [Qnum Qden]. lia.
        -- rewrite ir2_qp_pow.
           replace (Datatypes.S (Datatypes.S n'))%nat with (n' + 2)%nat by lia.
           assert (Hzc : (Z.pos pd <= Z.of_nat n')%Z).
           { assert (Hle : (Z.to_nat (Z.pos pd) + 1 <= Datatypes.S n')%nat) by lia.
             pose proof (proj1 (Nat2Z.inj_le _ _) Hle) as Hz.
             rewrite Nat2Z.inj_add, Nat2Z.inj_succ in Hz.
             pose proof (Z2Nat.id (Z.pos pd) (ltac:(lia))) as Hz2.
             cbn in Hz. lia. }
           pose proof (proj1 (Nat2Z.inj_le _ _) (ir2_pow_ge (n' + 2))) as Hpg.
           unfold Qlt. cbn [Qnum Qden]. lia.
      * unfold Qle, Qinv. cbn [Qnum Qden]. nia.
Qed.

Definition ir2_escape : lic_escape_window ir2_x ir2_e.
Proof.
  intro q.
  destruct (Qlt_bool 0%Q q) eqn:Hpos.
  - pose proof (lic_qlt_bool_true 0%Q q Hpos) as Hq0.
    destruct (Qlt_bool (q * q) 2%Q) eqn:H2b.
    + (* q² < 2：N := den(q) + 8 *)
      pose proof (lic_qlt_bool_true (q * q) 2%Q H2b) as H2.
      destruct q as [a b].
      assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
      assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
      assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
      { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
        exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
        rewrite Ek in Hz. cbn in Hz. lia. }
      exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
      apply Qlt_to_QltT.
      assert (Hxsq : Qle 2%Q (ir2_x (Z.to_nat (Z.pos b) + 8)
                                * ir2_x (Z.to_nat (Z.pos b) + 8)))
        by apply ir2_sq_ge2.
      assert (Hqx : Qlt ((a # b) * (a # b))
                    (ir2_x (Z.to_nat (Z.pos b) + 8)
                     * ir2_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (Qlt_le_trans ((a # b) * (a # b)) 2%Q
                    (ir2_x (Z.to_nat (Z.pos b) + 8)
                     * ir2_x (Z.to_nat (Z.pos b) + 8))); assumption).
      assert (Hqle : Qlt (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)))
        by (apply (ir2_lt_of_sq (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b));
            [apply Qlt_le_weak; apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8))
            | apply Qlt_le_weak; exact Hq0 | exact Hqx]).
      assert (Habs : Qabs ((a # b) - ir2_x (Z.to_nat (Z.pos b) + 8))%Q
                     == (ir2_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      { rewrite Qabs_Qminus. apply ir2_abs_sub. apply Qlt_le_weak. exact Hqle. }
      rewrite Habs.
      apply (Qlt_le_trans (ir2_e (Z.to_nat (Z.pos b) + 8))
              (Qinv ((3 * (Z.pos b * Z.pos b)) # 1))
              (ir2_x (Z.to_nat (Z.pos b) + 8) - (a # b))%Q).
      * apply (Qle_lt_trans (ir2_e (Z.to_nat (Z.pos b) + 8))
                (Qinv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8))))
                (Qinv ((3 * (Z.pos b * Z.pos b)) # 1))).
        -- apply (ir2_le_inv (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   (ir2_e (Z.to_nat (Z.pos b) + 8))).
           ++ apply ir2_qp_pos.
           ++ rewrite (Qmult_comm (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                       (ir2_e (Z.to_nat (Z.pos b) + 8))).
              replace (Z.to_nat (Z.pos b) + 8)%nat
                with (Datatypes.S (Z.to_nat (Z.pos b) + 7))%nat by lia.
              apply (ir2_decay (Z.to_nat (Z.pos b) + 7)).
        -- apply (ir2_inv_lt (ir2_qp (Datatypes.S (Z.to_nat (Z.pos b) + 8)))
                   ((3 * (Z.pos b * Z.pos b)) # 1)).
           ++ apply ir2_qp_pos.
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ rewrite ir2_qp_pow.
              replace (Datatypes.S (Z.to_nat (Z.pos b) + 8))%nat
                with (Z.to_nat (Z.pos b) + 8 + 1)%nat by lia.
              assert (Hb3 : (2 ^ (Z.to_nat (Z.pos b) + 8 + 1)
                             = 2 * 2 ^ (Z.to_nat (Z.pos b) + 8))%nat)
                by (rewrite Nat.pow_add_r, Nat.pow_1_r, Nat.mul_comm; reflexivity).
              assert (Hzp : (1 <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow_ge (Z.to_nat (Z.pos b) + 8)) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite Nat2Z.inj_succ in Hp. lia. }
              assert (Hz : (3 * (Z.pos b * Z.pos b)
                            <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp.
                rewrite Hkb in Hp. cbn [Z.of_nat] in Hp. lia. }
              pose proof (f_equal Z.of_nat Hb3) as Hb4.
              rewrite Nat2Z.inj_mul in Hb4. cbn [Z.of_nat] in Hb4.
              unfold Qlt. cbn [Qnum Qden]. lia.
      * apply (Qle_trans _ ((2 - (a # b) * (a # b))
                             * (1#3))%Q).
        -- apply (ir2_ge_inv ((3 * (Z.pos b * Z.pos b)) # 1)
                   (((2 - (a # b) * (a # b)) * (1#3))%Q)).
           ++ unfold Qlt. cbn [Qnum Qden]. lia.
           ++ unfold Qle, Qmult, Qminus.
              pose proof H2 as H2'. unfold Qlt, Qmult, Qminus in H2'.
              cbn [Qnum Qden Qplus Qopp] in H2' |- *.
              assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
              nia.
        -- apply (ir2_gap_lower (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b)).
           ++ apply Qlt_le_weak. exact Hq0.
           ++ apply Qlt_le_weak. exact Hqle.
           ++ apply ir2_x_ub. lia.
           ++ exact Hxsq.
           ++ exact H2.
    + (* 2 ≤ q² *)
      pose proof (lic_qlt_bool_false_le (q * q) 2%Q H2b) as Hge2.
      destruct (Qeq_dec (q * q) 2%Q) as [Heq2 | Hne2].
      * exfalso. exact (ir2_no_sqrt2 q Heq2).
      * destruct (Qlt_bool 2%Q (q * q)) eqn:H2lt.
        -- pose proof (lic_qlt_bool_true 2%Q (q * q) H2lt) as Hlt2.
           destruct (Qlt_bool (3#2) q) eqn:H32b.
           ++ (* 3/2 < q：N := num(q) + den(q) + 1 *)
              pose proof (lic_qlt_bool_true (3#2) q H32b) as H32.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (H32z : (3 * Z.pos b < 2 * a)%Z).
              { pose proof H32 as H32'. unfold Qlt in H32'.
                cbn [Qnum Qden] in H32'. lia. }
              assert (Hz2 : (2 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt2 as H2'. unfold Qlt, Qmult in H2'.
                cbn [Qnum Qden] in H2'. lia. }
              assert (Hkba : Z.of_nat (Z.to_nat a) = a)
                by (apply Z2Nat.id; lia).
              assert (Hkbb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b)
                by (apply Z2Nat.id; lia).
              assert (HpowN : ((a + Z.pos b) * Z.pos b
                               <= Z.of_nat (2 ^ (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)))%Z).
              { replace (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat
                  with (Datatypes.S (Z.to_nat a + Z.to_nat (Z.pos b))) by lia.
                rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r.
                pose proof (ir2_pow_ge (Z.to_nat a)) as H1.
                pose proof (ir2_pow_ge (Z.to_nat (Z.pos b))) as H2.
                apply (proj1 (Nat2Z.inj_le _ _)) in H1.
                apply (proj1 (Nat2Z.inj_le _ _)) in H2.
                rewrite Nat2Z.inj_succ in H1, H2.
                pose proof (Z2Nat.id a (ltac:(lia))) as Hz3.
                pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz4.
                rewrite Hz3 in H1. rewrite Hz4 in H2.
                rewrite !Nat2Z.inj_mul. cbn [Z.of_nat].
                nia. }
              exists (Z.to_nat a + Z.to_nat (Z.pos b) + 1)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hdpow : Qle (ir2_delta (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)
                                    * ir2_qp (Z.to_nat a
                                              + Z.to_nat (Z.pos b) + 1)) 1%Q).
              { apply (ir2_delta_pow_le). lia. }
              assert (Hbnd : Qle (((a # b) + 1)
                                  * ir2_delta (Z.to_nat a
                                               + Z.to_nat (Z.pos b) + 1))
                           (((a # b) * (a # b)) - 2%Q)%Q).
              { apply (Qle_trans _ (((a # b) + 1)
                                    * Qinv (ir2_qp (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1)))%Q).
                - apply ir2_mult_le_compat_l.
                  + apply (ir2_le_inv (ir2_qp (Z.to_nat a
                                          + Z.to_nat (Z.pos b) + 1))
                              (ir2_delta (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1))).
                    * apply ir2_qp_pos.
                    * rewrite (Qmult_comm (ir2_qp (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                                (ir2_delta (Z.to_nat a
                                             + Z.to_nat (Z.pos b) + 1))).
                      exact Hdpow.
                  + apply (Qle_trans 0%Q (a # b) ((a # b) + 1)%Q).
                    * apply Qlt_le_weak. exact Hq0.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_lt_add_r (a # b) 1%Q).
                      unfold Qlt. cbn [Qnum Qden]. lia.
                - rewrite (ir2_qp_pow (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                  assert (Hzp1 : (1 <= Z.of_nat (2 ^ (Z.to_nat a
                                                   + Z.to_nat (Z.pos b) + 1)))%Z).
                  { pose proof (ir2_pow_ge (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hp.
                    apply (proj1 (Nat2Z.inj_le _ _)) in Hp. lia. }
                  destruct (Z.of_nat (2 ^ (Z.to_nat a
                                           + Z.to_nat (Z.pos b) + 1)))
                    as [|pp|pp] eqn:Ez; try lia.
                  rewrite ?Ez in HpowN.
                  unfold Qle, Qmult, Qminus, Qinv.
                  cbn [Qnum Qden Qplus Qopp] in HpowN |- *.
                  assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                  nia. }
              assert (Hdl : Qlt (ir2_delta (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1))
                            (((a # b) * (a # b)) - 2%Q)%Q).
              { destruct (ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                  as [dn dd] eqn:Ed.
                rewrite (ir2_qp_pow (Z.to_nat a
                          + Z.to_nat (Z.pos b) + 1)) in Hdpow.
                rewrite ?Ed in Hdpow, Hbnd.
                pose proof (ir2_delta_pos (Z.to_nat a
                                            + Z.to_nat (Z.pos b) + 1)) as Hdp3.
                rewrite ?Ed in Hdp3.
                unfold Qle, Qlt in *.
                cbn [Qnum Qden Qmult Qminus Qopp Qplus] in *.
                assert (Hdd : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                nia. }
              assert (Hxq : Qlt (ir2_x (Z.to_nat a
                                       + Z.to_nat (Z.pos b) + 1))
                                (a # b)).
              { apply (ir2_lt_of_sq (a # b)
                        (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
                - apply Qlt_le_weak. exact Hq0.
                - apply Qlt_le_weak.
                  apply (ir2_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
                - pose proof Hdl as Hdl'.
                  unfold ir2_delta in Hdl'.
                  pose proof (lic_qlt_minus_add_r ((a # b) * (a # b)) 2%Q)
                    as Hr1.
                  pose proof (lic_qlt_minus_add_r
                                (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                                2%Q) as Hr2.
                  apply (Qle_lt_trans
                          (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                           * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                          ((ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                            - 2%Q) + 2%Q)%Q
                          ((a # b) * (a # b))).
                  + apply (qeq_le _ _ (Qeq_sym _ _ Hr2)).
                  + apply (lic_qlt_comp_r
                              (((a # b) * (a # b) - 2%Q) + 2%Q)%Q
                              ((a # b) * (a # b))
                              ((ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                - 2%Q) + 2%Q)%Q).
                    * exact Hr1.
                    * apply (lic_qlt_add_r
                                (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 * ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                 - 2%Q)%Q
                                ((a # b) * (a # b) - 2%Q)%Q
                                2%Q Hdl'). }
              assert (HeqN : (ir2_e (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                              == ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1)
                                  * (1#2))%Q).
              { unfold ir2_e. ring. }
              rewrite HeqN.
              rewrite (ir2_abs_sub (a # b)
                        (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1)))
                by (apply Qlt_le_weak; exact Hxq).
              apply (ir2_gap_upper_big
                      (ir2_x (Z.to_nat a + Z.to_nat (Z.pos b) + 1))
                      (a # b)
                      (ir2_delta (Z.to_nat a + Z.to_nat (Z.pos b) + 1))).
              ** apply (ir2_x_pos (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hxq.
              ** apply Qlt_le_weak. exact H32.
              ** exact Hlt2.
              ** reflexivity.
              ** apply (ir2_delta_ge0 (Z.to_nat a + Z.to_nat (Z.pos b) + 1)).
              ** exact Hbnd.
           ++ (* 2 < q² 且 q ≤ 3/2：N := den(q) + 8（与分支 2 同窗，x_N 自下方追上 q） *)
              pose proof (lic_qlt_bool_false_le (3#2) q H32b) as H32.
              destruct q as [a b].
              assert (Hb0 : (0 < Z.pos b)%Z) by apply Pos2Z.is_pos.
              assert (Hkb : Z.of_nat (Z.to_nat (Z.pos b)) = Z.pos b) by (apply Z2Nat.id; lia).
              assert (Hkb1 : (1 <= Z.to_nat (Z.pos b))%nat).
              { destruct (Z.to_nat (Z.pos b)) as [|k'] eqn:Ek; [ | lia].
                exfalso. pose proof (Z2Nat.id (Z.pos b) (ltac:(lia))) as Hz.
                rewrite Ek in Hz. cbn in Hz. lia. }
              assert (Hq2z : (2 * (Z.pos b * Z.pos b) + 1 <= a * a)%Z).
              { pose proof Hlt2 as H2'. unfold Qlt, Qmult in H2'.
                cbn [Qnum Qden] in H2'. lia. }
              exists (Z.to_nat (Z.pos b) + 8)%nat. split. lia.
              apply Qlt_to_QltT.
              assert (Hpow3 : (3 * (Z.pos b * Z.pos b)
                               <= Z.of_nat (2 ^ (Z.to_nat (Z.pos b) + 8)))%Z).
              { pose proof (ir2_pow3sq (Z.to_nat (Z.pos b))) as Hp.
                apply (proj1 (Nat2Z.inj_le _ _)) in Hp.
                rewrite !Nat2Z.inj_mul in Hp. rewrite Hkb in Hp.
                cbn [Z.of_nat] in Hp. lia. }
              assert (Hdpow : Qle (ir2_delta (Z.to_nat (Z.pos b) + 8)
                                    * ir2_qp (Z.to_nat (Z.pos b) + 8)) 1%Q)
                by (apply ir2_delta_pow_le; lia).
              rewrite (ir2_qp_pow (Z.to_nat (Z.pos b) + 8)) in Hdpow.
              assert (H25 : Qlt (ir2_delta (Z.to_nat (Z.pos b) + 8))
                              (((2#5) * (((a # b) * (a # b)) - 2%Q))%Q)).
              { destruct (ir2_delta (Z.to_nat (Z.pos b) + 8)) as [dn dd] eqn:Ed.
                rewrite ?Ed in Hdpow.
                pose proof (ir2_delta_pos (Z.to_nat (Z.pos b) + 8)) as Hdp.
                rewrite Ed in Hdp. unfold Qlt in Hdp. cbn [Qnum Qden] in Hdp.
                unfold Qle, Qlt, Qmult in Hdpow. cbn [Qnum Qden] in Hdpow.
                unfold Qlt, Qmult, Qminus. cbn [Qnum Qden Qplus Qopp] in Hdp, Hdpow |- *.
                assert (Hdd0 : (0 < Z.pos dd)%Z) by apply Pos2Z.is_pos.
                assert (Hbp : (1 <= Z.pos b)%Z) by lia.
                nia. }
              assert (Hdl : Qlt (ir2_delta (Z.to_nat (Z.pos b) + 8))
                              ((((a # b) * (a # b)) - 2%Q)%Q)).
              { apply (Qlt_le_trans (ir2_delta (Z.to_nat (Z.pos b) + 8))
                        (((2#5) * (((a # b) * (a # b)) - 2%Q))%Q)
                        ((((a # b) * (a # b)) - 2%Q)%Q)).
                - exact H25.
                - apply (Qle_trans _ (1%Q * (((a # b) * (a # b)) - 2%Q))%Q).
                  + apply Qmult_le_compat_r.
                    * unfold Qle. cbn [Qnum Qden]. lia.
                    * apply Qlt_le_weak.
                      apply (lic_qlt_0_minus 2%Q ((a # b) * (a # b)) Hlt2).
                  + apply qeq_le. apply Qmult_1_l. }
              assert (Hqx : Qlt (ir2_x (Z.to_nat (Z.pos b) + 8)
                                  * ir2_x (Z.to_nat (Z.pos b) + 8))
                            ((a # b) * (a # b))).
              { assert (Hr : (((ir2_x (Z.to_nat (Z.pos b) + 8)
                                * ir2_x (Z.to_nat (Z.pos b) + 8) - 2%Q) + 2%Q)
                              == (ir2_x (Z.to_nat (Z.pos b) + 8)
                                   * ir2_x (Z.to_nat (Z.pos b) + 8)))%Q)
                  by apply lic_qlt_minus_add_r.
                rewrite <- Hr.
                apply (Qlt_le_trans _ ((((a # b) * (a # b)) - 2%Q) + 2%Q)%Q).
                - apply (lic_qlt_add_r _ _ 2%Q Hdl).
                - apply qeq_le. apply lic_qlt_minus_add_r. }
              assert (Hqle : Qlt (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b))
                by (apply (ir2_lt_of_sq (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)));
                    [apply Qlt_le_weak; exact Hq0
                    | apply Qlt_le_weak;
                       apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8))
                    | exact Hqx]).
              rewrite (ir2_abs_sub (a # b) (ir2_x (Z.to_nat (Z.pos b) + 8)))
                by (apply Qlt_le_weak; exact Hqle).
              assert (Heq8 : (ir2_e (Z.to_nat (Z.pos b) + 8)
                              == ir2_delta (Z.to_nat (Z.pos b) + 8)
                                  * (1#2))%Q).
              { unfold ir2_e. ring. }
              rewrite Heq8.
              apply (ir2_gap_upper_small
                      (ir2_x (Z.to_nat (Z.pos b) + 8)) (a # b)
                      (ir2_delta (Z.to_nat (Z.pos b) + 8))).
              ** apply (ir2_x_pos (Z.to_nat (Z.pos b) + 8)).
              ** exact Hq0.
              ** exact Hqle.
              ** exact H32.
              ** exact Hlt2.
              ** reflexivity.
              ** apply (ir2_delta_ge0 (Z.to_nat (Z.pos b) + 8)).
              ** apply Qlt_le_weak. exact H25.
        -- (* ¬(2 < q²) 且 2 ≤ q² ⟹ q² == 2 ⟹ 与 ir2_no_sqrt2 矛盾 *)
           exfalso. apply Hne2.
           pose proof (lic_qlt_bool_false_le 2%Q (q * q) H2lt) as Hle2'.
           apply (Qle_antisym (q * q) 2%Q); [exact Hle2' | exact Hge2].
  - (* q ≤ 0 *)
    pose proof (lic_qlt_bool_false_le 0%Q q Hpos) as Hq0.
    destruct q as [qn qd].
    assert (Hqd : (0 < Z.pos qd)%Z) by apply Pos2Z.is_pos.
    exists 1%nat. split. lia.
    apply Qlt_to_QltT.
    rewrite (Qabs_Qminus (qn # qd) (ir2_x 1)).
    rewrite (ir2_abs_sub (ir2_x 1) (qn # qd)).
    2: { apply (Qle_trans (qn # qd) 0%Q (ir2_x 1)).
         - exact Hq0.
         - apply Qlt_le_weak. apply (ir2_x_pos 1). }
    rewrite ir2_x1.
    assert (Heq1 : ir2_e 1 == (1#8)%Q) by reflexivity.
    rewrite Heq1.
    unfold Qle in Hq0. cbn [Qnum Qden] in Hq0.
    unfold Qlt, Qminus. cbn [Qnum Qden Qopp Qplus]. lia.
Defined.

(* ============================================================ *)
(* S7：主定理装配（真走母定理 exact 装配，零旁路）+ 提取检验 + 公理面自审 *)
(* ============================================================ *)

Theorem ir2_sqrt2_irrational_criterion : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
                            ir2_x
                            (lic_seq_cauchy ir2_x ir2_e ir2_tail ir2_vanish))
       (real_const q)))).
Proof.
  intro q.
  exact (lic_irrational_criterion ir2_x ir2_e ir2_tail ir2_escape ir2_vanish q).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction ir2_sqrt2_irrational_criterion ir2_tail ir2_vanish
  ir2_escape ir2_x ir2_delta ir2_e ir2_qp ir2_decay ir2_gap_lower
  ir2_gap_upper_small ir2_gap_upper_big ir2_no_sqrt2.

Print Assumptions ir2_sqrt2_irrational_criterion.
