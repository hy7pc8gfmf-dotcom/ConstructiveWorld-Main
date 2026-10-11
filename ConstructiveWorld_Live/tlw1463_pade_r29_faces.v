(* ========================================================================= *)
(* tlw1463_pade_r29_faces                                                    *)
(* 使命：本件在 Lambert 三项递推表（tlw1463_pade_table）之上形式化 w=1 处的   *)
(*       四项代数性质：(1) 相邻对 (U_j, V_j) 的行列式恒等式                   *)
(*       V_{j+1}·U_j − V_j·U_{j+1} = (−1)^j·((j+1)!)²；(2) 行列式的交错定号   *)
(*       与偶/奇指标两侧符号；(3) 非零下界 3·((2n+1)!)²/V_{2n+1} > 0；(4)     *)
(*       相邻间隔商 gap_{n+1} ≤ (21/100)·gap_n 作为显式承载前提下的相对衰减   *)
(*       界 gap_n ≤ (71/100000)·(21/100)^n，并附 n ≤ 3 的计算锚。             *)
(* 依赖：Stdlib QArith、QArith.Qring、ZArith、List、Setoid、Lia、Extraction； *)
(*       本库件 tlw1463_pade_table。                                          *)
(* 对标：K. Mahler, On the approximation of pi, Indagationes Math. 15 (1953) *)
(*       （Lambert 连分数收敛子行列式恒等式的经典出处）。                      *)
(* 构造性注记：全部有名语句居 Set 层（bid/Qeq_bool/Qle_bool 形）；            *)
(*       零承认、零全局假设；定义透明、可提取；有理数序事实一律经分量展开     *)
(*       归约至整数非线性判定（nia，辅助事实申报）。                          *)
(* 编译配方：coqc -q -Q . "" tlw1463_pade_r29_faces.v（cpu_guard v3 包裹）。  *)
(* ========================================================================= *)

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Require Import tlw1463_pade_table.
Import ListNotations.

(* ==================== §1 表在 w=1 处的求值 ==================== *)

(** 表在 w=1 处的取值即系数和：U_k(1)、V_k(1) 均为整数（递推自整系数表
    出发，加法与标量乘保持整性，w=1 时移位项并入系数和）。 *)
Definition padeU1 (k : nat) : Q := fold_right Qplus 0%Q (padeU k).
Definition padeV1 (k : nat) : Q := fold_right Qplus 0%Q (padeV k).

Fixpoint natfact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S m => S m * natfact m
  end.

Lemma natfact_pos : forall n : nat, (0 < natfact n)%nat.
Proof.
  induction n as [|n IH].
  - cbn [natfact]. lia.
  - cbn [natfact]. nia.
Qed.

(** 表加法的求值同态：系数和的和等于和的系数和。 *)
Lemma val1_vadd : forall a b : list Q,
  fold_right Qplus 0%Q (vadd a b) == fold_right Qplus 0%Q a + fold_right Qplus 0%Q b.
Proof.
  intros a. induction a as [|x a' IH]; intros b; destruct b as [|y b'].
  - cbn [vadd fold_right]. rewrite Qplus_0_l. apply Qeq_refl.
  - cbn [vadd fold_right]. rewrite Qplus_0_l. apply Qeq_refl.
  - cbn [vadd fold_right]. rewrite Qplus_0_r. apply Qeq_refl.
  - cbn [vadd fold_right]. rewrite IH. ring.
Qed.

(** 表标量乘的求值同态。 *)
Lemma val1_vsmul : forall (c : Q) (l : list Q),
  fold_right Qplus 0%Q (vsmul c l) == c * fold_right Qplus 0%Q l.
Proof.
  intros c l. induction l as [|x t IH].
  - cbn [vsmul fold_right]. rewrite Qmult_0_r. apply Qeq_refl.
  - cbn [vsmul fold_right]. rewrite IH.
    rewrite Qmult_plus_distr_r. apply Qeq_refl.
Qed.

(** 递推在 w=1 处的一步形式：U_{m+2}(1) = (2m+5)·U_{m+1}(1) + (m+2)²·U_m(1)。 *)
Lemma padeU1_step : forall m : nat,
  padeU1 (S (S m)) ==
    ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q * padeU1 (S m)
    + ((Z.of_nat (S (S m) * S (S m))) # 1)%Q * padeU1 m.
Proof.
  intros m.
  unfold padeU1, padeU.
  destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
  rewrite (pade_pair_step (S m)).
  rewrite (pade_pair_step m).
  rewrite Em.
  cbn [fst snd].
  rewrite val1_vadd.
  rewrite (val1_vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q u1).
  rewrite (val1_vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: u0)).
  cbn [fold_right].
  rewrite Qplus_0_l.
  apply Qeq_refl.
Qed.

(** 同上，分母侧：V_{m+2}(1) = (2m+5)·V_{m+1}(1) + (m+2)²·V_m(1)。 *)
Lemma padeV1_step : forall m : nat,
  padeV1 (S (S m)) ==
    ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q * padeV1 (S m)
    + ((Z.of_nat (S (S m) * S (S m))) # 1)%Q * padeV1 m.
Proof.
  intros m.
  unfold padeV1, padeV.
  destruct (pade_pair m) as [[u0 u1][v0 v1]] eqn:Em.
  rewrite (pade_pair_step (S m)).
  rewrite (pade_pair_step m).
  rewrite Em.
  cbn [fst snd].
  rewrite val1_vadd.
  rewrite (val1_vsmul ((Z.of_nat (2 * S (S m) + 1)) # 1)%Q v1).
  rewrite (val1_vsmul ((Z.of_nat (S (S m) * S (S m))) # 1)%Q (0%Q :: v0)).
  cbn [fold_right].
  rewrite Qplus_0_l.
  apply Qeq_refl.
Qed.

(* ==================== §2 行列式恒等式 ==================== *)

(** 相邻对的行列式 D_j := V_{j+1}·U_j − V_j·U_{j+1}。 *)
Definition pade_det (j : nat) : Q :=
  padeV1 (S j) * padeU1 j - padeV1 j * padeU1 (S j).

(** 分子分母的 #1 形迁移（定义性恒等，供环归一化前重写系数形）。 *)
Lemma qneg_one_mul : forall z : Z, (Z.opp z # 1)%Q == (- (z # 1)%Q).
Proof.
  intros z. apply Qeq_refl.
Qed.

Lemma qmul_one : forall z w : Z, ((z * w) # 1)%Q == (z # 1)%Q * (w # 1)%Q.
Proof.
  intros z w. apply Qeq_refl.
Qed.

(** 行列式一步递推：D_{m+1} = −(m+2)²·D_m。代入递推后相消，纯环算术。 *)
Lemma pade_det_step : forall m : nat,
  pade_det (S m) == (-(Z.of_nat (S (S m) * S (S m))) # 1)%Q * pade_det m.
Proof.
  intros m. unfold pade_det.
  rewrite (padeV1_step m). rewrite (padeU1_step m).
  rewrite qneg_one_mul.
  ring.
Qed.

(** 交错符号一次反号。 *)
Lemma altsign_S : forall n : nat, altsign (S n) = (- altsign n)%Z.
Proof.
  intros n. unfold altsign.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even n); cbn [negb]; lia.
Qed.

(** 主定理（Set 层承载）：对一切 j，D_j = (−1)^j·((j+1)!)²。
    两步归纳：基例 j=0,1 直接计算；归纳步用 D_{m+2} = −(m+3)²·D_{m+1}
    连同 factorial 乘法展开与符号交错，收于整数环恒等式。 *)
Definition pade_det_identity (j : nat) : Set :=
  bid (Qeq_bool (padeV1 (S j) * padeU1 j - padeV1 j * padeU1 (S j))
                ((altsign j * Z.of_nat (natfact (S j) * natfact (S j))) # 1)%Q) true.

Lemma pade_det_identity_G : forall j : nat, pade_det_identity j.
Proof.
  apply nat_double_ind.
  - apply bidI. vm_compute. reflexivity.
  - apply bidI. vm_compute. reflexivity.
  - intros m IHm IHSm.
    apply bidE in IHSm. apply Qeq_bool_eq in IHSm.
    fold (pade_det (S m)) in IHSm.
    apply bidI. apply qeqbI.
    change (pade_det (S (S m))
              == ((altsign (S (S m))
                   * Z.of_nat (natfact (S (S (S m))) * natfact (S (S (S m))))) # 1)%Q).
    rewrite (pade_det_step (S m)).
    rewrite IHSm.
    rewrite (altsign_S (S m)).
    unfold altsign.
    rewrite Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even m) eqn:Em; cbn [negb] in *;
    unfold Qeq;
    cbn [Qnum Qden Qmult Qminus Qopp Qplus Pos.mul];
    cbn [natfact];
    rewrite ?Nat2Z.inj_mul;
    rewrite ?Nat2Z.inj_succ;
    rewrite <- ?Z.add_1_r;
    ring.
Qed.

(** 行列式数值锚：j = 0..9 的完整值表与 (−1)^j((j+1)!)² 逐一核对。 *)
Lemma pade_det_anchors :
  bid (vleeq (map pade_det (seq 0 10))
             (((1 # 1) :: ((-4) # 1) :: (36 # 1) :: ((-576) # 1) :: (14400 # 1) ::
               ((-518400) # 1) :: (25401600 # 1) :: ((-1625702400) # 1) ::
               (131681894400 # 1) :: ((-13168189440000) # 1) :: nil)%Q)) true.
Proof.
  apply bidI. vm_compute. reflexivity.
Qed.

(* ==================== §3 有理数序初等事实 ==================== *)

(** 分母恒正（正整数到整数的嵌入保持正性）。 *)
Lemma qden_pos : forall x : Q, (0 < Z.pos (Qden x))%Z.
Proof.
  intros [n d]. cbn [Qden]. apply Pos2Z.is_pos.
Qed.

(** 正乘正为正。 *)
Lemma qpos_mul : forall a b : Q, (0 # 1)%Q < a -> (0 # 1)%Q < b -> (0 # 1)%Q < a * b.
Proof.
  intros a b Ha Hb. unfold Qlt in *. cbn [Qnum Qden Qmult Z.mul Pos.mul] in *. nia.
Qed.

(** 正加非负为正。 *)
Lemma qpos_add_le : forall a b : Q,
  (0 # 1)%Q < a -> (0 # 1)%Q <= b -> (0 # 1)%Q < a + b.
Proof.
  intros a b Ha Hb.
  pose proof (qden_pos a). pose proof (qden_pos b).
  unfold Qlt, Qle in *. cbn [Qnum Qden Qplus Z.mul Pos.mul] in *.
  rewrite ?Z.mul_0_l, ?Z.mul_1_r in *.
  assert (Hp1 : (0 < Qnum a * QDen b)%Z) by nia.
  assert (Hp2 : (0 <= Qnum b * QDen a)%Z) by nia.
  apply (Z.lt_le_trans (0)%Z (Qnum a * QDen b) (Qnum a * QDen b + Qnum b * QDen a)).
  - exact Hp1.
  - rewrite <- (Z.add_0_r (Qnum a * QDen b)) at 1.
    apply Z.add_le_mono; [apply Z.le_refl | exact Hp2].
Qed.

(** 加非负不减。 *)
Lemma qle_add_r : forall x t : Q, (0 # 1)%Q <= t -> x <= x + t.
Proof.
  intros x t Ht.
  pose proof (qden_pos x). pose proof (qden_pos t).
  unfold Qle in Ht. unfold Qle. cbn [Qnum Qden Qplus Z.mul Pos.mul] in *.
  rewrite Z.mul_1_r in Ht.
  rewrite Pos2Z.inj_mul.
  assert (Hp1 : (0 <= Qnum t * QDen x)%Z) by nia.
  assert (Hp2 : (0 <= Qnum t * QDen x * QDen x)%Z) by nia.
  nia.
Qed.

(** 布尔序检验与序判断的相互转换。 *)
Lemma qleb_true : forall x y : Q, Qle_bool x y = true -> x <= y.
Proof.
  intros x y H. unfold Qle_bool in H. apply Z.leb_le in H. unfold Qle. exact H.
Qed.

Lemma qleb_of_le : forall x y : Q, x <= y -> Qle_bool x y = true.
Proof.
  intros x y H. unfold Qle_bool. apply Z.leb_le. unfold Qle. exact H.
Qed.

(** 分子平方的正性（阶乘非零的推论）。 *)
Lemma natfact_sq_qpos : forall k : nat,
  (0 # 1)%Q < ((Z.of_nat (natfact k) * Z.of_nat (natfact k)) # 1)%Q.
Proof.
  intros k.
  assert (Hp : (0 < natfact k)%nat) by apply natfact_pos.
  unfold Qlt. cbn [Qnum Qden]. nia.
Qed.

(** 正除正为正。 *)
Lemma qdiv_pos : forall a b : Q, (0 # 1)%Q < a -> (0 # 1)%Q < b -> (0 # 1)%Q < a / b.
Proof.
  intros a b Ha Hb. unfold Qdiv. apply qpos_mul; [exact Ha |].
  destruct b as [n d]. cbn [Qnum Qden] in Hb.
  destruct n as [|p|p].
  - unfold Qlt in Hb. unfold Qlt. cbn [Qnum Qden Qmult Z.mul] in *.
    lia.
  - cbn [Qinv]. unfold Qlt. cbn [Qnum Qden Qmult Pos.mul Z.mul].
    assert (Hd : (0 < Zpos d)%Z) by apply Pos2Z.is_pos.
    exact Hd.
  - unfold Qlt in Hb. unfold Qlt. cbn [Qnum Qden Qmult Pos.mul Z.mul] in *.
    assert (Hp : (0 < Zpos p)%Z) by apply Pos2Z.is_pos.
    lia.
Qed.

(** 非负乘正为非负（Z 层·显式情形分解）。 *)
Lemma qle_mul_pos : forall n d : Z, (0 <= n)%Z -> (0 < d)%Z -> (0 <= n * d)%Z.
Proof.
  intros n d Hn Hd.
  destruct (Z_lt_le_dec 0 n) as [H | H].
  - assert (Hp : (0 < n * d)%Z) by nia.
    apply Z.lt_le_incl. exact Hp.
  - nia.
Qed.

(** 非负乘非负为非负（Z 层）。 *)
Lemma qle_mul_nonneg_Z : forall n d : Z, (0 <= n)%Z -> (0 <= d)%Z -> (0 <= n * d)%Z.
Proof.
  intros n d Hn Hd.
  destruct (Z_lt_le_dec 0 d) as [H | H].
  - exact (qle_mul_pos n d Hn H).
  - assert (E : (d = 0)%Z) by (apply Z.le_antisymm; [exact H | exact Hd]).
    rewrite E, Z.mul_0_r. apply Z.le_refl.
Qed.

(** 非负乘非负为非负。 *)
Lemma qle_mul_nonneg : forall a b : Q,
  (0 # 1)%Q <= a -> (0 # 1)%Q <= b -> (0 # 1)%Q <= a * b.
Proof.
  intros a b Ha Hb.
  pose proof (qden_pos a) as Hda. pose proof (qden_pos b) as Hdb.
  unfold Qle in *. cbn [Qnum Qden Qmult Z.mul Pos.mul] in *.
  rewrite ?Z.mul_0_l, ?Z.mul_1_r in *.
  exact (qle_mul_nonneg_Z (Qnum a) (Qnum b) Ha Hb).
Qed.

(** 正乘负为负。 *)
Lemma qpos_qneg_mul : forall a b : Q,
  (0 # 1)%Q < a -> b < (0 # 1)%Q -> b * a < (0 # 1)%Q.
Proof.
  intros a b Ha Hb.
  pose proof (qden_pos a). pose proof (qden_pos b).
  unfold Qlt in *. cbn [Qnum Qden Qmult Z.mul Pos.mul] in *. nia.
Qed.

(** 分母侧表值恒正：V_k(1) > 0。两步归纳：基例 V_0(1) = 1、V_1(1) = 4；
    归纳步由一步递推的正系数分解（正项加非负项）。 *)
Lemma padeV1_pos : forall k : nat, (0 # 1)%Q < padeV1 k.
Proof.
  apply nat_double_ind.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros m IHm IHSm.
    rewrite padeV1_step.
    apply qpos_add_le.
    + apply qpos_mul.
      * assert (0 < 2 * S (S m) + 1)%nat by lia.
        unfold Qlt. cbn [Qnum Qden]. lia.
      * exact IHSm.
    + apply qle_mul_nonneg.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * apply Qlt_le_weak. exact IHm.
Qed.

(* ==================== §4 行列式的交错定号 ==================== *)

(** 行列式两步演化：D_{m+2} = (m+3)²·(m+4)²·D_m（两步递推相乘，负号消去）。 *)
Lemma pade_det_two_step : forall m : nat,
  pade_det (S (S m)) ==
    ((Z.of_nat (S (S (S m)) * S (S (S m))))
     * (Z.of_nat (S (S m) * S (S m))) # 1)%Q * pade_det m.

Proof.
  intros m.
  rewrite (pade_det_step (S m)).
  rewrite (pade_det_step m).
  rewrite qmul_one.
  rewrite qneg_one_mul.
  rewrite qneg_one_mul.
  ring.
Qed.

(** 偶指标行列式恒正：D_{2n} > 0。两步归纳：基例 D_0 = 1、D_2 = 36；
    归纳步 D_{2n+4} = 正系数 · D_{2n}，正乘正保持。 *)
Lemma pade_det_pos_even : forall n : nat, (0 # 1)%Q < pade_det (2 * n).
Proof.
  apply nat_double_ind.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros m IHm IHSm.
    replace (pade_det (2 * S (S m))) with (pade_det (S (S (S (S (2 * m)))))) by (f_equal; lia).
    rewrite pade_det_two_step.
    replace (pade_det (S (S (2 * m)))) with (pade_det (2 * S m)) by (f_equal; lia).
    apply qpos_mul.
    + unfold Qlt. cbn [Qnum Qden Qmult].
      rewrite ?Nat2Z.inj_mul.
      assert (Ha1 : (0 < Z.of_nat (S (S (S m))))%Z) by lia.
      assert (Ha2 : (0 < Z.of_nat (S (S m)))%Z) by lia.
      assert (Hb1 : (0 < Z.of_nat (S (S (S m))) * Z.of_nat (S (S (S m))))%Z)
        by (apply Z.mul_pos_pos; lia).
      assert (Hb2 : (0 < Z.of_nat (S (S m)) * Z.of_nat (S (S m)))%Z)
        by (apply Z.mul_pos_pos; lia).
      assert (Hc2 : (0 < Z.of_nat (S (S (S m))) * Z.of_nat (S (S (S m))) * (Z.of_nat (S (S m)) * Z.of_nat (S (S m))))%Z)
        by (apply Z.mul_pos_pos; [exact Hb1 | exact Hb2]).
      rewrite Z.mul_0_l, Z.mul_1_r.
      exact Hc2.
    + exact IHSm.
Qed.

(** 奇指标行列式恒负：D_{2n+1} = −(2n+2)²·D_{2n} < 0。 *)
Lemma pade_det_neg_odd : forall n : nat, pade_det (2 * n + 1) < (0 # 1)%Q.
Proof.
  intros n.
  replace (2 * n + 1)%nat with (S (2 * n))%nat by lia.
  rewrite (pade_det_step (2 * n)).
  pose proof (pade_det_pos_even n) as Hp.
  apply qpos_qneg_mul.
  - exact Hp.
  - unfold Qlt. cbn [Qnum Qden Qopp].
    rewrite ?Z.mul_0_l, ?Z.mul_1_r.
    rewrite Nat2Z.inj_mul.
    assert (H2 : (0 < Z.of_nat (S (S (2 * n))) * Z.of_nat (S (S (2 * n))))%Z)
      by (apply Z.mul_pos_pos; lia).
    lia.
Qed.

(** 相邻行列式反号（偶肢）：D_{2n+1}·D_{2n} < 0。 *)
Lemma pade_step_between_even : forall n : nat,
  pade_det (2 * n + 1) * pade_det (2 * n) < (0 # 1)%Q.
Proof.
  intros n. apply qpos_qneg_mul.
  - apply pade_det_pos_even.
  - apply pade_det_neg_odd.
Qed.

(** 相邻行列式反号（奇肢）：D_{2n+2}·D_{2n+1} < 0。两肢合取覆盖一切相邻对，
    即相邻间隔的符号逐位交错（嵌套性的代数内核）。 *)
Lemma pade_step_between_odd : forall n : nat,
  pade_det (S (2 * n + 1)) * pade_det (2 * n + 1) < (0 # 1)%Q.
Proof.
  intros n.
  rewrite (Qmult_comm (pade_det (S (2 * n + 1))) (pade_det (2 * n + 1))).
  apply qpos_qneg_mul.
  - replace (S (2 * n + 1))%nat with (2 * S n)%nat by lia.
    apply pade_det_pos_even.
  - apply pade_det_neg_odd.
Qed.

(* ==================== §5 非零下界 ==================== *)

(** 非零下界量：LB1_n := 3·((2n+1)!)²/V_{2n+1}(1)。 *)
Definition pade_LB1 (n : nat) : Q :=
  (3 # 1)%Q * (((Z.of_nat (natfact (2 * n + 1)) * Z.of_nat (natfact (2 * n + 1))) # 1)%Q
                 / padeV1 (2 * n + 1)).

(** 主定理：LB1_n > 0 对一切 n 成立（分子阶乘恒正、分母表值恒正）。 *)
Lemma pade_nz_lb_G : forall n : nat, (0 # 1)%Q < pade_LB1 n.
Proof.
  intros n. unfold pade_LB1. apply qpos_mul.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply qdiv_pos.
    + apply natfact_sq_qpos.
    + apply padeV1_pos.
Qed.

(* ==================== §6 相对衰减界 ==================== *)

(** 相邻间隔商：gap_n := ((2n+1)!)² / (V_{2n}(1)·V_{2n+1}(1))，
    即 c_{2n} − c_{2n+1} 的交叉相乘形。 *)
Definition pade_gapq (n : nat) : Q :=
  ((Z.of_nat (natfact (2 * n + 1)) * Z.of_nat (natfact (2 * n + 1))) # 1)%Q
    / (padeV1 (2 * n) * padeV1 (2 * n + 1)).

(** 相对衰减界主语句（Set 层承载，显式常数 71/100000，基 21/100）。 *)
Definition pade_rho_rel_bound (n : nat) : Set :=
  bid (Qle_bool (pade_gapq n) ((71 # 100000)%Q * q_pown pade_rho_hat n)) true.

(** 单步衰减前提（显式 Set 层承载前提；逐点实例为纯计算事实）。 *)
Definition pade_gap_step_premise (n : nat) : Set :=
  bid (Qle_bool (pade_gapq (S n)) ((21 # 100)%Q * pade_gapq n)) true.

(** gap_3 = 1/153364（精确计算锚）。 *)
Lemma pade_gapq_anchor_1 : bid (Qeq_bool (pade_gapq 1) ((1 # 136)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_gapq_anchor_2 : bid (Qeq_bool (pade_gapq 2) ((1 # 4551)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_gapq_anchor_3 : bid (Qeq_bool (pade_gapq 3) ((1 # 153364)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

(** gap_3 处的常数界成立（1/153364 ≤ 71/100000·(21/100)³）。 *)
Lemma pade_gap_3_anchor :
  bid (Qle_bool (pade_gapq 3) ((71 # 100000)%Q * q_pown pade_rho_hat 3)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_gapq_3_bound :
  pade_gapq 3 <= (71 # 100000)%Q * q_pown pade_rho_hat 3.
Proof.
  apply qleb_true. apply bidE. exact pade_gap_3_anchor.
Qed.

(** 偏移归纳：基例 n = 3 由常数锚承载；归纳步使用单步衰减前提，
    常数随幂次分解（ρ̂^{3+(d+1)} = ρ̂·ρ̂^{3+d}）。 *)
Lemma pade_gapq_rel_bound_aux : forall d n : nat,
  (n = 3 + d)%nat ->
  (forall k : nat, pade_gap_step_premise k) ->
  pade_gapq n <= (71 # 100000)%Q * q_pown pade_rho_hat n.
Proof.
  induction d as [|d IH]; intros n En Hstep.
  - subst n. exact pade_gapq_3_bound.
  - subst n.
    assert (Hs : pade_gapq (S (3 + d)) <= (21 # 100)%Q * pade_gapq (3 + d)).
    { apply qleb_true. apply bidE. apply (Hstep (3 + d)%nat). }
    assert (HI : pade_gapq (3 + d) <= (71 # 100000)%Q * q_pown pade_rho_hat (3 + d)).
    { apply (IH (3 + d)%nat); [lia | exact Hstep]. }
    apply Qle_trans with (y := (21 # 100)%Q * pade_gapq (3 + d)); [exact Hs |].
    apply Qle_trans
      with (y := (21 # 100)%Q * ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d))).
    + rewrite (Qmult_comm (21 # 100)%Q (pade_gapq (3 + d))).
      rewrite (Qmult_comm (21 # 100)%Q ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d))).
      apply Qmult_le_compat_r; [exact HI | unfold Qle; cbn [Qnum Qden]; lia].
    + replace (3 + S d)%nat with (S (3 + d))%nat by lia.
      assert (E : ((21 # 100)%Q * ((71 # 100000)%Q * q_pown pade_rho_hat (3 + d)))%Q
                  == ((71 # 100000)%Q * q_pown pade_rho_hat (S (3 + d)))).
      { cbn [q_pown]. unfold pade_rho_hat. ring. }
      rewrite E. apply Qle_refl.
Qed.

(** 主定理（Set 层承载）：n ≥ 3 且单步衰减前提逐点成立时，
    gap_n ≤ (71/100000)·(21/100)^n。前提的使用被显式披露于接口。 *)
Lemma pade_rho_rel_bound_general :
  forall n : nat, (3 <= n)%nat ->
    (forall k : nat, pade_gap_step_premise k) ->
    pade_rho_rel_bound n.
Proof.
  intros n Hn Hstep. unfold pade_rho_rel_bound. apply bidI. apply qleb_of_le.
  assert (E : (n = 3 + (n - 3))%nat) by lia.
  exact (pade_gapq_rel_bound_aux (n - 3)%nat n E Hstep).
Qed.

(** 计算锚：n = 0,1,2 处常数取 1 的实例（守卫内点的整段偿付）。 *)
Lemma pade_gapq_instance_n0 :
  bid (Qle_bool (pade_gapq 0) ((1 # 1)%Q * q_pown pade_rho_hat 0)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_gapq_instance_n1 :
  bid (Qle_bool (pade_gapq 1) ((1 # 1)%Q * q_pown pade_rho_hat 1)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_gapq_instance_n2 :
  bid (Qle_bool (pade_gapq 2) ((1 # 1)%Q * q_pown pade_rho_hat 2)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

(** LB1 精确值锚：LB1_1 = 9/17、LB1_2 = 60/41、LB1_3 = 15120/1667。 *)
Lemma pade_LB1_anchor_1 : bid (Qeq_bool (pade_LB1 1) ((9 # 17)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_LB1_anchor_2 : bid (Qeq_bool (pade_LB1 2) ((60 # 41)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

Lemma pade_LB1_anchor_3 : bid (Qeq_bool (pade_LB1 3) ((15120 # 1667)%Q)) true.
Proof. apply bidI. vm_compute. reflexivity. Qed.

(* 审计行：主语句链的全局上下文封闭性 *)
Print Assumptions pade_det_identity_G.
Print Assumptions pade_det_pos_even.
Print Assumptions pade_det_neg_odd.
Print Assumptions pade_step_between_even.
Print Assumptions pade_step_between_odd.
Print Assumptions pade_nz_lb_G.
Print Assumptions pade_rho_rel_bound_general.
