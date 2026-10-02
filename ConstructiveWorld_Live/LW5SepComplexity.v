(* 模块：LW5SepComplexity.v —— 分离 pi_L 与有理数的最小窗阶函数定义层。
   使命：以 pi 的有理包络列为窗族——eps_n := 1/(n+1)，M_n := 2*pie_modulus(eps_n/2)+1，
   lo_n := 4*pie_partial(M_n+1) − eps_n/4，hi_n := 4*pie_partial(M_n) + eps_n/4——
   给出 bool 分离判定器 lw5n_sep_dec 与最小分离窗阶 lw5n_nsep：lw5n_find 为结构递归
   有界搜索，lw5n_bnd 为显式预算（足用性不主张，见定义处注记），最小性特征定理
   lw5n_nsep_minimal 以 Set 面 nat 等词在预算假设位承载。另附：窗族合法性（pi_L
   严格含入、窗宽 < eps_n、窗宽为正、窗列嵌套）、入窗近距正确性（Q 投影形）、
   搜索机件定理包与格定义——增长律三档语句面以注记承载，闭证属后续工作。
   依赖：S01_BaseRing（NatLe 及 NatLe_drop/lift）、S02_CauchyComplete（Real/real_lt/
   real_const/qeq_le）、S03_QExp、S10_KVQuantTrig（cauchy_real_pi_leibniz）、
   S11_TP3B5（atan_sign_odd/atan_sign_even/q_pow）、PiEnvelope（pie_partial/pie_mag/
   pie_modulus/pie_modulus_bound/pie_even_mono/pie_odd_mono/pie_even_le_odd/
   pie_tail4/pie_real_lower_gen/pie_real_upper_gen/pie_v_eq/pie_q_add_halves/
   pie_qplus_lt_r/QltT'）、LW0LeibWindow（leiblw_Id/leiblw_id_eq/leiblw_id_inv/
   leiblw_Qleb/leiblw_Qleb_inv/leiblw_pos_succ/leiblw_qmake_le/leiblw_qmake_lt/
   leiblw_qabs_bound）、LW0MLicBridge（lw0m_xL）；Stdlib：QArith/Qabs/Qround/
   ZArith/Arith/Bool/Lia/Extraction。
   对标：PiEnvelope.v pi_rational_envelope（窗端点 4*pie_partial(2*pie_modulus(eps/2)
   +{1,2}) ± eps/4 与其包络见证逐字同源；lw5n_win_pi 按 pie_real_lower_gen/
   pie_real_upper_gen 同法端点自证）；LW0LeibWindow.v leiblw_dist_set 与
   leiblw_natwin_unbounded（leiblw_Id＋bool 判定器同工艺）。
   构造性：零公理/零承认式/零经典逻辑；主语句面全 Set（leiblw_Id＋bool 判定器，
   And:=prod）；辅助 Qle/Qlt 语句仅作脚手架；nat 序仅前提位（结论位 nat 序为
   nsep_bound/nsep_least 两件上界＋S2 增 shape_lower/shape_band 之
   m < 8·n0+9 下界序，特此如实注记）；逐点推理在 Q 层以
   引理链展开；提取面 Obj.magic=0；文末 Print Assumptions 全 Closed。
   编译配方：coqc.exe -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/
   ConstructiveWorld_vo" "" LW5SepComplexity.v（双 export COQLIB/ROCQLIB 后单发；
   工作目录取无同源 vo 的中性目录，防同件双根歧义）。
   作用域注记：Q 作用域随 QArith 导入全局开启（算术记号默认 Q 形），nat 算术
   逐点 %nat 注记；故本件不另开 nat_scope。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool.
From Stdlib Require Import Lia.
Require Import LW0LeibWindow.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.

(* ============================================================ *)
(* §1 窗族：包络列 eps_n := 1/(n+1)，端点显式                       *)
(* ============================================================ *)

Definition lw5n_eps (n : nat) : Q := (1 # Pos.of_succ_nat n)%Q.

Definition lw5n_M (n : nat) : nat := 2 * pie_modulus (lw5n_eps n / 2) + 1.

Definition lw5n_lo (n : nat) : Q :=
  (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4)%Q.

Definition lw5n_hi (n : nat) : Q :=
  (4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)%Q.

Lemma lw5n_eps_pos : forall n : nat, Qlt 0 (lw5n_eps n).
Proof. intros n. unfold Qlt. simpl. lia. Qed.

Lemma lw5n_eps_posT : forall n : nat, QltT' 0 (lw5n_eps n).
Proof. intros n. apply Qlt_to_QltT'. apply lw5n_eps_pos. Qed.

Lemma lw5n_eps2_pos : forall n : nat, Qlt 0 (lw5n_eps n / 2)%Q.
Proof.
  intros n. unfold Qdiv.
  apply (Qmult_lt_0_compat (lw5n_eps n) (/ (2 # 1))).
  - apply lw5n_eps_pos.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Qed.

Lemma lw5n_eps4_pos : forall n : nat, Qlt 0 (lw5n_eps n / 4)%Q.
Proof.
  intros n. unfold Qdiv.
  apply (Qmult_lt_0_compat (lw5n_eps n) (/ (4 # 1))).
  - apply lw5n_eps_pos.
  - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia.
Qed.

Lemma lw5n_eps_antitone : forall n : nat, Qle (lw5n_eps (Datatypes.S n)) (lw5n_eps n).
Proof.
  intros n. unfold lw5n_eps, Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_l.
  replace (Pos.of_succ_nat (Datatypes.S n))
    with (Pos.succ (Pos.of_succ_nat n)) by reflexivity.
  rewrite Pos2Z.inj_succ.
  replace (Z.succ (Z.pos (Pos.of_succ_nat n)))
    with (Z.pos (Pos.of_succ_nat n) + 1)%Z by reflexivity.
  lia.
Qed.

(* 4/(eps_n/2) 的整值性：eps_n/2 的两倍分母使 4 倍商恰为 8n+8 *)
Lemma lw5n_four_div_half : forall n : nat,
  (4 / (lw5n_eps n / 2))%Q == (Z.of_nat (8 * n + 8) # 1)%Q.
Proof.
  intros n.
  assert (H1 : (lw5n_eps n / 2)%Q == (1 # (Pos.of_succ_nat n * 2))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult. cbn [Qnum Qden].
  apply leiblw_qmake_eq.
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  rewrite leiblw_pos_succ.
  replace (Z.pos 2) with 2%Z by reflexivity.
  replace (Z.of_nat (8 * n + 8)) with (8 * Z.of_nat (Datatypes.S n))%Z.
  - lia.
  - replace (8 * n + 8)%nat with (8 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Qed.

(* 模量显式赋值：pie_modulus(eps_n/2) = 8n+9（4/(eps_n/2) 恰整，Qceiling 平截） *)
Lemma lw5n_modulus_val : forall n : nat,
  pie_modulus (lw5n_eps n / 2) = Datatypes.S (8 * n + 8)%nat.
Proof.
  intros n.
  assert (Hx := lw5n_four_div_half n).
  assert (Hz' : Qceiling ((Z.of_nat (8 * n + 8) # 1)%Q) = Z.of_nat (8 * n + 8)).
  { pose proof (Qle_ceiling (Z.of_nat (8 * n + 8) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (8 * n + 8) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (proj1 (leiblw_qmake_le _ _ _ _)) in Hub.
    apply (proj1 (leiblw_qmake_lt _ _ _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 2)) = Z.of_nat (8 * n + 8)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 2)) (Z.of_nat (8 * n + 8) # 1)%Q)
      by (apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (8 * n + 8) # 1)%Q (4 / (lw5n_eps n / 2)))
      by (apply qeq_le; apply Qeq_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1. lia. }
  unfold pie_modulus. rewrite Hz. f_equal.
  apply Nat2Z.inj.
  apply Z2Nat.id. apply Nat2Z.is_nonneg.
Qed.

Lemma lw5n_M_val : forall n : nat, lw5n_M n = (16 * n + 19)%nat.
Proof. intros n. unfold lw5n_M. rewrite lw5n_modulus_val. lia. Qed.

(* 相邻窗端点距的闭式：4*S_M − 4*S_{M+1} = 4*pie_mag(M)（M 为奇数阶） *)
Lemma lw5n_gap4 : forall n : nat,
  (4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1)
   == 4 * pie_mag (lw5n_M n))%Q.
Proof.
  intros n.
  assert (Hi : (lw5n_M n + 1)%nat = Datatypes.S (lw5n_M n)) by lia.
  rewrite Hi.
  setoid_replace (4 * pie_partial (lw5n_M n) - 4 * pie_partial (Datatypes.S (lw5n_M n)))
    with (- (4 * (pie_partial (Datatypes.S (lw5n_M n)) - pie_partial (lw5n_M n)))) by field.
  rewrite (pie_gap1 (lw5n_M n)).
  assert (Hs : pie_term (lw5n_M n) == (- pie_mag (lw5n_M n))%Q).
  { unfold lw5n_M, pie_term, pie_mag, Qdiv.
    rewrite (atan_sign_odd (pie_modulus (lw5n_eps n / 2))). ring. }
  rewrite Hs. ring.
Qed.

(* 窗族合法性一：pi_L 严格含入每扇窗（端点自证，与 pi_rational_envelope 同法） *)
Lemma lw5n_win_pi : forall n : nat,
  And (real_lt (real_const (lw5n_lo n)) cauchy_real_pi_leibniz)
      (real_lt cauchy_real_pi_leibniz (real_const (lw5n_hi n))).
Proof.
  intros n.
  split.
  - apply (pie_real_lower_gen (pie_modulus (lw5n_eps n / 2))
             (lw5n_eps n / 4) (lw5n_lo n)).
    + apply lw5n_eps4_pos.
    + unfold lw5n_lo.
      replace (lw5n_M n + 1)%nat with (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat
        by (unfold lw5n_M; lia).
      apply qeq_le. ring.
  - apply (pie_real_upper_gen (pie_modulus (lw5n_eps n / 2))
             (lw5n_eps n / 4) (lw5n_hi n)).
    + apply lw5n_eps4_pos.
    + unfold lw5n_hi. apply Qle_refl.
Qed.

(* 窗族合法性二：窗宽 < eps_n *)
Lemma lw5n_win_width : forall n : nat, QltT' (lw5n_hi n - lw5n_lo n) (lw5n_eps n).
Proof.
  intros n.
  pose proof (lw5n_eps2_pos n) as Hc2.
  assert (Hb : Qlt (4 * pie_mag (lw5n_M n)) (lw5n_eps n / 2)%Q).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (lw5n_eps n / 2))) _).
    - apply pie_mult4_le. apply pie_mag_antitone. unfold lw5n_M. lia.
    - apply (pie_modulus_bound (lw5n_eps n / 2) Hc2). }
  apply Qlt_to_QltT'.
  unfold lw5n_hi, lw5n_lo.
  setoid_replace ((4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)
                  - (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4))
    with ((4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1))
          + (lw5n_eps n / 4 + lw5n_eps n / 4)) by field.
  rewrite lw5n_gap4, pie_q_add_halves.
  apply (proj2 (Qlt_minus_iff (4 * pie_mag (lw5n_M n) + lw5n_eps n / 2) (lw5n_eps n))).
  setoid_replace (lw5n_eps n - (4 * pie_mag (lw5n_M n) + lw5n_eps n / 2))
    with (lw5n_eps n / 2 - 4 * pie_mag (lw5n_M n)) by field.
  exact (proj1 (Qlt_minus_iff (4 * pie_mag (lw5n_M n)) (lw5n_eps n / 2)) Hb).
Qed.

(* 窗族合法性三：窗宽为正 *)
Lemma lw5n_width_pos : forall n : nat, QltT' 0 (lw5n_hi n - lw5n_lo n).
Proof.
  intros n.
  pose proof (lw5n_eps2_pos n) as Hc2.
  pose proof (pie_mag_pos (lw5n_M n)) as Hm.
  assert (Ha : Qlt 0 (4 * pie_mag (lw5n_M n))).
  { apply (Qmult_lt_0_compat 4 (pie_mag (lw5n_M n))).
    - unfold Qlt. simpl. lia.
    - exact Hm. }
  apply Qlt_to_QltT'.
  unfold lw5n_hi, lw5n_lo.
  setoid_replace ((4 * pie_partial (lw5n_M n) + lw5n_eps n / 4)
                  - (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4))
    with ((4 * pie_partial (lw5n_M n) - 4 * pie_partial (lw5n_M n + 1))
          + (lw5n_eps n / 4 + lw5n_eps n / 4)) by field.
  rewrite lw5n_gap4, pie_q_add_halves.
  apply (Qlt_trans 0 (4 * pie_mag (lw5n_M n)) _).
  - exact Ha.
  - pose proof (pie_qplus_lt_r (4 * pie_mag (lw5n_M n)) 0 (lw5n_eps n / 2) Hc2) as H1.
    setoid_replace (4 * pie_mag (lw5n_M n) + 0) with (4 * pie_mag (lw5n_M n)) in H1 by field.
    exact H1.
Qed.

(* 窗族合法性四：窗列嵌套——n ≤ n' 时内窗含于外窗 *)
Lemma lw5n_win_nested : forall n n' : nat, (n <= n')%nat ->
  And (Qle (lw5n_lo n) (lw5n_lo n')) (Qle (lw5n_hi n') (lw5n_hi n)).
Proof.
  intros n n' Hnn'.
  assert (Hpm : (pie_modulus (lw5n_eps n / 2) <= pie_modulus (lw5n_eps n' / 2))%nat)
    by (rewrite !lw5n_modulus_val; lia).
  assert (Hev : Qle (4 * pie_partial (lw5n_M n + 1))
                    (4 * pie_partial (lw5n_M n' + 1))).
  { replace (lw5n_M n + 1)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1))%nat by (unfold lw5n_M; lia).
    replace (lw5n_M n' + 1)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1
                 + (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))))%nat
      by (unfold lw5n_M; lia).
    apply pie_mult4_le.
    apply (pie_even_mono (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))
                         (pie_modulus (lw5n_eps n / 2) + 1)). }
  assert (Hod : Qle (4 * pie_partial (lw5n_M n')) (4 * pie_partial (lw5n_M n))).
  { replace (lw5n_M n')%nat
      with (2 * (pie_modulus (lw5n_eps n / 2)
                 + (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))) + 1)%nat
      by (unfold lw5n_M; lia).
    replace (lw5n_M n)%nat with (2 * pie_modulus (lw5n_eps n / 2) + 1)%nat
      by (unfold lw5n_M; lia).
    apply pie_mult4_le.
    apply (pie_odd_mono (pie_modulus (lw5n_eps n' / 2) - pie_modulus (lw5n_eps n / 2))
                        (pie_modulus (lw5n_eps n / 2))). }
  assert (Hq4 : Qle (lw5n_eps n' / 4) (lw5n_eps n / 4)).
  { apply (Qmult_le_compat_r (lw5n_eps n') (lw5n_eps n) (/ (4 # 1))).
    - assert (Hgen : forall k : nat, Qle (lw5n_eps (n + k)%nat) (lw5n_eps n)).
      { intros k. induction k as [|k IHk].
        - rewrite Nat.add_0_r. apply Qle_refl.
        - replace (n + Datatypes.S k)%nat with (Datatypes.S (n + k)) by lia.
          exact (Qle_trans (lw5n_eps (Datatypes.S (n + k)))
                           (lw5n_eps (n + k)) (lw5n_eps n)
                           (lw5n_eps_antitone (n + k)) IHk). }
      replace n' with (n + (n' - n))%nat by lia.
      apply Hgen.
    - apply (Qlt_le_weak 0 (/ (4 # 1))). apply Qinv_lt_0_compat.
      unfold Qlt. simpl. lia. }
  split.
  - unfold lw5n_lo.
    setoid_replace (4 * pie_partial (lw5n_M n + 1) - lw5n_eps n / 4)
      with (4 * pie_partial (lw5n_M n + 1) + (- (lw5n_eps n / 4))) by field.
    setoid_replace (4 * pie_partial (lw5n_M n' + 1) - lw5n_eps n' / 4)
      with (4 * pie_partial (lw5n_M n' + 1) + (- (lw5n_eps n' / 4))) by field.
    apply (Qplus_le_compat (4 * pie_partial (lw5n_M n + 1))
                           (4 * pie_partial (lw5n_M n' + 1))
                           (- (lw5n_eps n / 4)) (- (lw5n_eps n' / 4))).
    + exact Hev.
    + destruct (lw5n_eps n) as [e1 e2]; destruct (lw5n_eps n') as [f1 f2].
      unfold Qle in Hq4 |- *. cbn [Qnum Qden] in Hq4 |- *.
      unfold Qopp. cbn [Qnum Qden]. lia.
  - unfold lw5n_hi.
    apply (Qle_trans _ (4 * pie_partial (lw5n_M n') + lw5n_eps n / 4) _).
    + apply (Qplus_le_compat (4 * pie_partial (lw5n_M n'))
                             (4 * pie_partial (lw5n_M n'))
                             (lw5n_eps n' / 4) (lw5n_eps n / 4)).
      * apply Qle_refl.
      * exact Hq4.
    + apply (Qplus_le_compat (4 * pie_partial (lw5n_M n'))
                             (4 * pie_partial (lw5n_M n))
                             (lw5n_eps n / 4) (lw5n_eps n / 4)).
      * exact Hod.
      * apply Qle_refl.
Qed.

(* ============================================================ *)
(* §2 bool 分离判定器：窗内/出窗（leiblw_Qleb 双侧）                  *)
(* ============================================================ *)

Definition lw5n_inwin (q : Q) (n : nat) : bool :=
  andb (leiblw_Qleb (lw5n_lo n) q) (leiblw_Qleb q (lw5n_hi n)).

Definition lw5n_sep_dec (q : Q) (n : nat) : bool := negb (lw5n_inwin q n).

Lemma lw5n_Qleb_false_lt : forall x y : Q, leiblw_Qleb x y = false -> Qlt y x.
Proof.
  intros x y H. unfold leiblw_Qleb in H.
  destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - discriminate.
  - discriminate.
  - unfold Qgt in Hgt. exact Hgt.
Qed.

(* 入窗=近距（余项界导出的正确性内容，Q 投影形）：
   q 落第 n 窗内时，包络投影列 lw0m_xL 自 M_n 的包络阶起逐点落入 q 的 eps_n 邻域 *)
Lemma lw5n_inwin_close_pt : forall (q : Q) (n : nat) (d : Q), QltT' 0 d ->
  leiblw_Id (lw5n_inwin q n) true ->
  sigT (fun N : nat => forall k : nat, NatLe N k ->
    QltT' (Qabs (lw0m_xL k - q)) (lw5n_eps n)).
Proof.
  intros q n d Hd Hin.
  apply leiblw_id_inv in Hin. unfold lw5n_inwin in Hin.
  apply andb_true_iff in Hin. destruct Hin as [Hl Hh].
  apply leiblw_Qleb_inv in Hl. apply leiblw_Qleb_inv in Hh.
  pose proof (lw5n_win_width n) as Hw. apply QltT'_to_Qlt in Hw.
  pose proof (lw5n_eps4_pos n) as Hc4.
  assert (HhiS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1)
                  == lw5n_hi n - lw5n_eps n / 4)%Q)
    by (unfold lw5n_hi, lw5n_M; ring).
  assert (HloS : (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)
                  == lw5n_lo n + lw5n_eps n / 4)%Q).
  { unfold lw5n_lo, lw5n_M.
    replace (2 * pie_modulus (lw5n_eps n / 2) + 1 + 1)%nat
      with (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat by lia.
    ring. }
  exists (pie_modulus (lw5n_eps n / 2)). intros k Hk.
  apply NatLe_drop in Hk.
  apply Qlt_to_QltT'.
  assert (Hev1 : Qle (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
                     (4 * pie_partial (2 * k + 2))).
  { replace (2 * pie_modulus (lw5n_eps n / 2) + 2)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1))%nat by lia.
    replace (2 * k + 2)%nat
      with (2 * (pie_modulus (lw5n_eps n / 2) + 1
                 + (k - pie_modulus (lw5n_eps n / 2))))%nat by lia.
    apply pie_mult4_le.
    apply (pie_even_mono (k - pie_modulus (lw5n_eps n / 2))
                         (pie_modulus (lw5n_eps n / 2) + 1)). }
  assert (Hev2 : Qle (4 * pie_partial (2 * k + 2))
                     (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))).
  { replace (2 * k + 2)%nat with (2 * (k + 1))%nat by lia.
    apply pie_mult4_le.
    apply (pie_even_le_odd (k + 1) (pie_modulus (lw5n_eps n / 2))). }
  assert (Hub : Qle (lw0m_xL k - q)
                    (lw5n_eps n - lw5n_eps n / 4)).
  { apply (Qle_trans _ (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1) - q) _).
    - exact (proj2 (Qplus_le_l _ _ _)
               (Qle_trans (lw0m_xL k) ((4 * pie_partial (2 * k + 2))%Q)
                          (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))
                          (qeq_le _ _ (pie_v_eq k)) Hev2)).
    - setoid_replace (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 1))
        with (lw5n_hi n - lw5n_eps n / 4) by exact HhiS.
      apply (Qle_trans _ ((lw5n_hi n - lw5n_eps n / 4) - lw5n_lo n) _).
      + apply (proj2 (Qplus_le_r _ _ _)).
        exact (Qopp_le_compat (lw5n_lo n) q Hl).
      + setoid_replace ((lw5n_hi n - lw5n_eps n / 4) - lw5n_lo n)
          with ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4) by field.
        apply Qlt_le_weak.
        apply (proj2 (Qlt_minus_iff _ _)).
        setoid_replace ((lw5n_eps n - lw5n_eps n / 4)
                        - ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_eps n - (lw5n_hi n - lw5n_lo n)) by field.
        exact (proj1 (Qlt_minus_iff (lw5n_hi n - lw5n_lo n) (lw5n_eps n)) Hw). }
  assert (Hlb : Qle (q - lw0m_xL k)
                    (lw5n_eps n - lw5n_eps n / 4)).
  { apply (Qle_trans _ (q - 4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2)) _).
    - exact (proj2 (Qplus_le_r _ _ _)
               (Qopp_le_compat ((4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))%Q)
                               (lw0m_xL k)
                               (Qle_trans (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
                                          ((4 * pie_partial (2 * k + 2))%Q) (lw0m_xL k)
                                          Hev1 (qeq_le _ _ (Qeq_sym _ _ (pie_v_eq k)))))).
    - setoid_replace (4 * pie_partial (2 * pie_modulus (lw5n_eps n / 2) + 2))
        with (lw5n_lo n + lw5n_eps n / 4) by exact HloS.
      apply (Qle_trans _ ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4) _).
      + setoid_replace (q - (lw5n_lo n + lw5n_eps n / 4))
          with ((q - lw5n_lo n) - lw5n_eps n / 4) by field.
        apply (proj2 (Qle_minus_iff _ _)).
        setoid_replace (((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4)
                        - ((q - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_hi n - q) by field.
        exact (proj1 (Qle_minus_iff q (lw5n_hi n)) Hh).
      + apply Qlt_le_weak.
        apply (proj2 (Qlt_minus_iff _ _)).
        setoid_replace ((lw5n_eps n - lw5n_eps n / 4)
                        - ((lw5n_hi n - lw5n_lo n) - lw5n_eps n / 4))
          with (lw5n_eps n - (lw5n_hi n - lw5n_lo n)) by field.
        exact (proj1 (Qlt_minus_iff (lw5n_hi n - lw5n_lo n) (lw5n_eps n)) Hw). }
  apply (Qle_lt_trans _ (lw5n_eps n - lw5n_eps n / 4) (lw5n_eps n)).
  - apply leiblw_qabs_bound.
    + exact Hub.
    + setoid_replace (- (lw0m_xL k - q))
        with (q - lw0m_xL k) by field.
      exact Hlb.
  - apply (proj2 (Qlt_minus_iff (lw5n_eps n - lw5n_eps n / 4) (lw5n_eps n))).
    setoid_replace (lw5n_eps n - (lw5n_eps n - lw5n_eps n / 4))
      with (lw5n_eps n / 4) by field.
    exact Hc4.
Qed.

(* ============================================================ *)
(* §3 有界线性搜索与最小分离窗阶                                     *)
(*    lw5n_find 自 n 起逐阶试 sep_dec，燃料尽返回 n（返回预算端点）；     *)
(*    预算 lw5n_bnd 取包络列在 eps := 1/(分母 q + 1) 处的阶。预算的足用性 *)
(*    （分离见证落入预算）不在本件主张；下列定理对任意预算参数成立。      *)
(* ============================================================ *)

Fixpoint lw5n_find (q : Q) (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | Datatypes.S f =>
      if lw5n_sep_dec q n then n else lw5n_find q (Datatypes.S n) f
  end.

(* 预算分母取 Qden q 的后继（1/(Qden q + 1) 的包络阶） *)
Definition lw5n_dlt (q : Q) : Q :=
  ((1 # 1) / (Z.pos (Pos.succ (Qden q)) # 1))%Q.

Definition lw5n_bnd (q : Q) : nat := Datatypes.S (pie_modulus (lw5n_dlt q)).

Definition lw5n_nsep (q : Q) : nat := lw5n_find q 0 (lw5n_bnd q).

(* 搜索上界：find 不越 n + fuel *)
Lemma lw5n_find_ub : forall (q : Q) (fuel n : nat),
  (lw5n_find q n fuel <= n + fuel)%nat.
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n.
  - simpl. lia.
  - simpl. destruct (lw5n_sep_dec q n).
    + lia.
    + specialize (IH (Datatypes.S n)). lia.
Qed.

(* 命中：若 [n, n+fuel] 内 n0 分离，则 find 停在分离阶且不越过 n0 *)
Lemma lw5n_find_hit : forall (q : Q) (fuel n n0 : nat),
  (n <= n0)%nat -> (n0 <= n + fuel)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  And (leiblw_Id (lw5n_sep_dec q (lw5n_find q n fuel)) true)
      (leiblw_Id (Nat.leb (lw5n_find q n fuel) n0) true).
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n n0 Hn1 Hn2 Hhit.
  - assert (Heq : n = n0) by lia. subst n0. simpl.
    split; [exact Hhit|].
    apply leiblw_id_eq. apply Nat.leb_le. lia.
  - simpl. destruct (lw5n_sep_dec q n) eqn:E.
    + split.
      * rewrite E. apply leiblw_id_intro.
      * apply leiblw_id_eq. apply Nat.leb_le. lia.
    + apply IH.
      * destruct (Nat.eq_dec n n0) as [Heq|Hne].
        -- subst n0. apply leiblw_id_inv in Hhit. rewrite E in Hhit. discriminate Hhit.
        -- lia.
      * lia.
      * exact Hhit.
Qed.

(* 搜索最小性：find 停在分离阶时，区间 [n, find) 内无分离阶 *)
Lemma lw5n_find_min : forall (q : Q) (fuel n m : nat),
  (n <= m)%nat -> (m < lw5n_find q n fuel)%nat ->
  leiblw_Id (lw5n_sep_dec q m) false.
Proof.
  intros q fuel. induction fuel as [|f IH]; intros n m Hn1 Hlt.
  - simpl in Hlt. lia.
  - simpl. destruct (lw5n_sep_dec q n) eqn:E.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt. lia.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt.
      destruct (Nat.eq_dec n m) as [Heq|Hne].
      * subst m. rewrite E. apply leiblw_id_intro.
      * apply (IH (Datatypes.S n) m); lia.
Qed.

(* 分离阶搜索上界定理：nsep 不越预算 *)
Theorem lw5n_nsep_bound : forall q : Q,
  (lw5n_nsep q <= lw5n_bnd q)%nat.
Proof.
  intros q. unfold lw5n_nsep.
  pose proof (lw5n_find_ub q (lw5n_bnd q) 0) as H. lia.
Qed.

(* 命中定理：预算内存在分离阶则 nsep 停在分离阶 *)
Theorem lw5n_nsep_hit : forall (q : Q) (n0 : nat),
  (n0 <= lw5n_bnd q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  leiblw_Id (lw5n_sep_dec q (lw5n_nsep q)) true.
Proof.
  intros q n0 Hb Hhit. unfold lw5n_nsep.
  destruct (lw5n_find_hit q (lw5n_bnd q) 0 n0 (Nat.le_0_l n0) Hb Hhit) as [H _].
  exact H.
Qed.

(* 不越定理：nsep 不越过预算内任一分离阶 *)
Theorem lw5n_nsep_least : forall (q : Q) (n0 : nat),
  (n0 <= lw5n_bnd q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  (lw5n_nsep q <= n0)%nat.
Proof.
  intros q n0 Hb Hhit.
  apply Nat.leb_le. apply leiblw_id_inv.
  destruct (lw5n_find_hit q (lw5n_bnd q) 0 n0 (Nat.le_0_l n0) Hb Hhit) as [_ H].
  exact H.
Qed.

(* 最小性特征定理：预算内的最小分离阶被 nsep 逐字取到
   （存在分离阶 n0 且 [0,n0) 内无分离阶，则 n_sep = n0 的 Set 面 nat 等词） *)
Theorem lw5n_nsep_minimal : forall (q : Q) (n0 : nat),
  (n0 <= lw5n_bnd q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  (forall m : nat, (m < n0)%nat -> leiblw_Id (lw5n_sep_dec q m) false) ->
  leiblw_Id (lw5n_nsep q) n0.
Proof.
  intros q n0 Hb Hn Hmin.
  assert (Hhit := lw5n_nsep_hit q n0 Hb Hn).
  assert (Hle := lw5n_nsep_least q n0 Hb Hn).
  destruct (Nat.eq_dec (lw5n_nsep q) n0) as [E|E].
  - rewrite E. apply leiblw_id_intro.
  - exfalso.
    assert (Hlt : (lw5n_nsep q < n0)%nat) by lia.
    specialize (Hmin _ Hlt).
    assert (Ht : lw5n_sep_dec q (lw5n_nsep q) = true)
      by (apply leiblw_id_inv; exact Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Qed.

(* ============================================================ *)
(* §4 增长律语句面（格定义＋三档注记；本件不闭证）                      *)
(*    第 m 格：[4*S_{2m+2}, 4*S_{2m+1}]，格宽 4*pie_mag(2m+1) =        *)
(*    相邻部分和 4 倍距（lw5n_gap4 同族闭式）。                         *)
(* ============================================================ *)

Definition lw5n_cell_hi (m : nat) : Q := (4 * pie_partial (2 * m + 1))%Q.

Definition lw5n_cell_lo (m : nat) : Q := (4 * pie_partial (2 * m + 2))%Q.

(* 增长律三档语句面（后续工作闭证）：
   档一·障碍形互界：q 落第 m 格（lw5n_cell_lo m ≤ q ≤ lw5n_cell_hi m）且格序与
   窗阶序相容（leb (4*m+3) (K*n+K') 形的具体常数待闭证时定值）时，
   lw5n_sep_dec q n = false——证法：pie_even_mono（lo 侧含入）＋pie_tail4
   （hi 侧余项界）＋eps_n 的 Q 算术；与 §3 机件合成下界：存在预算内分离阶则
   n_sep q 不低于最小越界阶。
   档二·参数化上界：置 lw5n_B c := Datatypes.S (pie_modulus (c/2))；给定 0 < c 与
   pi_L 到 q 距离 ≥ c 的逐点证书（Q 投影形：forall d > 0, 存在 N, 任意 k ≥ N,
   c < |lw0m_xL k − q|），存在 n0 ≤ lw5n_B c 使 lw5n_sep_dec q n0 = true——
   证法：入窗则近距（lw5n_inwin_close_pt），窗宽 < c 处必出窗；
   pie_modulus_bound 保证 B c 阶窗宽 < c。
   档三·闭合增长律：以分离阶闭式 c(q) 插入档二得 n_sep q ≤ B(c(q)) 的显式带，
   与档一合成 n_lo(cell(q)) ≤ n_sep q ≤ B(c(q))。上界非最优，不主张精确最优或
   渐近紧致。 *)

(* ============================================================ *)
(* §5 计算抽查＋提取＋假设审计                                        *)
(* ============================================================ *)

From Stdlib Require Import Extraction.

Eval vm_compute in (lw5n_lo 0, (lw5n_hi 0, lw5n_nsep (22 # 7)%Q)).
Eval vm_compute in (lw5n_lo 3, (lw5n_hi 3, lw5n_nsep (19 # 6)%Q)).

Separate Extraction lw5n_sep_dec lw5n_find lw5n_nsep lw5n_bnd lw5n_lo lw5n_hi.

Print Assumptions lw5n_win_pi.
Print Assumptions lw5n_win_width.
Print Assumptions lw5n_win_nested.
Print Assumptions lw5n_inwin_close_pt.
Print Assumptions lw5n_nsep_bound.
Print Assumptions lw5n_nsep_hit.
Print Assumptions lw5n_nsep_least.
Print Assumptions lw5n_nsep_minimal.

(* ============================================================ *)
(* §6 形态定理（family_separation 联动）——窗族分离的阶-宽-传递三面      *)
(* ============================================================ *)

Require Import LW2SepTransport.
Require Import UpReqIrrationalCriterion.
From Stdlib Require Import Lqa.

(* 三桥口径（传递收缩因子，558 §五.2「传递常数只减不增」）：
   k₃=2 兼容特化（lw2t_sep_transport :120 先例）；k₁=4 窗端点余量口径；
   k₂=8 预算内核复合口径（c·Qinv(2·4)=c/8）。 *)
Definition lw5n_k3 : Q := 2%Q.
Definition lw5n_k1 : Q := 4%Q.
Definition lw5n_k2 : Q := 8%Q.

Lemma lw5n_QleT_k3 : QleT 2 lw5n_k3.
Proof. unfold lw5n_k3. exact (inr id_refl). Qed.
Lemma lw5n_QleT_k1 : QleT 2 lw5n_k1.
Proof. unfold lw5n_k1. left. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.
Lemma lw5n_QleT_k2 : QleT 2 lw5n_k2.
Proof. unfold lw5n_k2. left. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.

(* leiblw_Qleb 双向桥（S1 :302 只含 false 向，本席补 true 向与逆真向） *)
Lemma lw5n_Qle_Qleb_true : forall x y : Q, Qle x y -> leiblw_Qleb x y = true.
Proof.
  intros x y H. unfold leiblw_Qleb. destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - reflexivity.
  - reflexivity.
  - exfalso. unfold Qgt, Qle in *. cbn [Qnum Qden] in *. nia.
Qed.

Lemma lw5n_Qlt_Qleb_false : forall x y : Q, Qlt y x -> leiblw_Qleb x y = false.
Proof.
  intros x y H. unfold leiblw_Qleb. destruct (Qcompare_spec x y) as [Heq|Hlt|Hgt].
  - exfalso. rewrite Heq in H. unfold Qlt in H. cbn [Qnum Qden] in H. lia.
  - exfalso. unfold Qlt in H, Hlt. cbn [Qnum Qden] in H, Hlt. lia.
  - reflexivity.
Qed.

(* 模量反单调砖：半径缩 ⟹ 阶预算不缩（pie_modulus PiEnvelope :575 本体一手）。
   【607 落刀改判登记】601 图 §四.一代码块方向（mod c' ≤ mod c）与其步骤序定谳形
   （mod c ≤ mod c'）互相矛盾，且两形均缺 c' 正性前提（反例 c'=-5, c=1：Qle c' c
   真而 pie_modulus 1 = 5 > 1 = pie_modulus (-5) 假）——按 TLW1028-FALSEPROP
   「前提位参数化」处方补 QltT' 0 c'，方向取步骤序定谳形；施工席禁回退。
   消费方 bnd_caliber 两侧正性自有。Qinv_le_mu 实测不存在（探针发0红），
   Qinv 反单调改 num/den 直算。 *)
Lemma lw5n_modulus_antitone : forall c c' : Q, QltT' 0 c -> QltT' 0 c' -> Qle c' c ->
  (pie_modulus c <= pie_modulus c')%nat.
Proof.
  intros c c' Hc Hc' Hle.
  apply QltT'_to_Qlt in Hc. apply QltT'_to_Qlt in Hc'.
  assert (Hx1 : Qle (4 / c) (4 / c')).
  { destruct c as [cn cd]; destruct c' as [c'n c'd].
    unfold Qlt in Hc, Hc'. cbn [Qnum Qden] in Hc, Hc'.
    unfold Qle in Hle. cbn [Qnum Qden] in Hle.
    unfold Qdiv, Qinv, Qmult, Qle. cbn.
    destruct cn as [|p|p]; destruct c'n as [|p'|p']; cbn in *; lia. }
  assert (Hx2 : (Qceiling (4 / c) <= Qceiling (4 / c'))%Z)
    by (apply Qceiling_resp_le; exact Hx1).
  assert (Hcz : (0 <= Qceiling (4 / c))%Z).
  { assert (Hq0 : Qlt 0 (4 / c)).
    { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv c)).
      - unfold Qlt. simpl. lia.
      - apply Qinv_lt_0_compat. exact Hc. }
    assert (Hcq : Qle 0 (Qceiling (4 / c) # 1)).
    { apply (Qle_trans 0 (4 / c) (Qceiling (4 / c) # 1)).
      - apply (Qlt_le_weak 0 (4 / c)). exact Hq0.
      - apply Qle_ceiling. }
    unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hc'z : (0 <= Qceiling (4 / c'))%Z).
  { assert (Hq0 : Qlt 0 (4 / c')).
    { unfold Qdiv. apply (Qmult_lt_0_compat 4 (Qinv c')).
      - unfold Qlt. simpl. lia.
      - apply Qinv_lt_0_compat. exact Hc'. }
    assert (Hcq : Qle 0 (Qceiling (4 / c') # 1)).
    { apply (Qle_trans 0 (4 / c') (Qceiling (4 / c') # 1)).
      - apply (Qlt_le_weak 0 (4 / c')). exact Hq0.
      - apply Qle_ceiling. }
    unfold Qle in Hcq. simpl in Hcq. lia. }
  assert (Hz : (Z.to_nat (Qceiling (4 / c)) <= Z.to_nat (Qceiling (4 / c')))%nat)
    by (apply (proj1 (Z2Nat.inj_le _ _ Hcz Hc'z) Hx2)).
  unfold pie_modulus. lia.
Qed.

(* §6.1 单调性：嵌套窗列下分离沿阶单调升、入窗沿阶单调降（And:=A×B 逐字） *)
Theorem lw5n_shape_mono : forall (q : Q) (m n : nat), (m <= n)%nat ->
  And (leiblw_Id (lw5n_sep_dec q m) true -> leiblw_Id (lw5n_sep_dec q n) true)
      (leiblw_Id (lw5n_inwin q n) true -> leiblw_Id (lw5n_inwin q m) true).
Proof.
  intros q m n Hmn.
  destruct (lw5n_win_nested m n Hmn) as [Hlo Hhi].
  split.
  - intros Hs. apply leiblw_id_inv in Hs.
    unfold lw5n_sep_dec in Hs. apply negb_true_iff in Hs.
    unfold lw5n_inwin in Hs.
    destruct (leiblw_Qleb (lw5n_lo m) q) eqn:E1.
    + cbn [andb] in Hs. apply lw5n_Qleb_false_lt in Hs.
      apply leiblw_id_eq. unfold lw5n_sep_dec, lw5n_inwin.
      rewrite (lw5n_Qlt_Qleb_false q (lw5n_hi n)
                 (Qle_lt_trans (lw5n_hi n) (lw5n_hi m) q Hhi Hs)).
      rewrite andb_false_r. cbn [negb]. reflexivity.
    + apply lw5n_Qleb_false_lt in E1.
      apply leiblw_id_eq. unfold lw5n_sep_dec, lw5n_inwin.
      rewrite (lw5n_Qlt_Qleb_false (lw5n_lo n) q
                 (Qlt_le_trans q (lw5n_lo m) (lw5n_lo n) E1 Hlo)).
      cbn [andb negb]. reflexivity.
  - intros Hi. apply leiblw_id_inv in Hi. unfold lw5n_inwin in Hi.
    apply andb_true_iff in Hi. destruct Hi as [Hl Hh].
    apply leiblw_Qleb_inv in Hl. apply leiblw_Qleb_inv in Hh.
    apply leiblw_id_eq. unfold lw5n_inwin.
    rewrite (lw5n_Qle_Qleb_true (lw5n_lo m) q
               (Qle_trans (lw5n_lo m) (lw5n_lo n) q Hlo Hl)).
    rewrite (lw5n_Qle_Qleb_true q (lw5n_hi m)
               (Qle_trans q (lw5n_hi n) (lw5n_hi m) Hh Hhi)).
    reflexivity.
Qed.

(* §6.2 反演性带形：预算内分离判定与 n_sep 序完全对偶。
   【601 改判】分量二无条件形被证伪（燃料耗尽反例），存在分离阶 n0 提为
   定理级假设位承载（590 §五.1 诚实边界一的落刀形态；施工席禁回退）。 *)
Theorem lw5n_shape_inversion : forall (q : Q) (n n0 : nat),
  (n0 <= lw5n_bnd q)%nat -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And ((n <= lw5n_bnd q)%nat ->
       (leiblw_Id (lw5n_sep_dec q n) true ->
        leiblw_Id (Nat.leb (lw5n_nsep q) n) true))
      ((lw5n_nsep q <= n)%nat -> leiblw_Id (lw5n_sep_dec q n) true).
Proof.
  intros q n n0 Hb0 Hs0. split.
  - intros Hb Hs. apply leiblw_id_eq. apply Nat.leb_le.
    exact (lw5n_nsep_least q n Hb Hs).
  - intros Hle.
    destruct (lw5n_shape_mono q (lw5n_nsep q) n Hle) as [Hmono _].
    exact (Hmono (lw5n_nsep_hit q n0 Hb0 Hs0)).
Qed.

(* §6.3 格障碍（escape_obstacle 障碍形包络族重立，形态如实分立）：
   m ≥ 8n+9 ⟹ 第 m 格 ⊆ 第 n 窗。常数链：M n = 16n+19（lw5n_M_val :139）；
   8n+9 ≤ m ⟹ 2m+1 ≥ 16n+19 = M n（奇列 pie_odd_mono :411）且
   ⟹ 2m+2 ≥ 16n+20 = M n+1（偶列 pie_even_mono :399）。零 tail4 项，双侧纯列单调。 *)
Theorem lw5n_cell_obstacle : forall (q : Q) (m n : nat),
  (8 * n + 9 <= m)%nat ->
  Qle (lw5n_cell_lo m) q -> Qle q (lw5n_cell_hi m) ->
  leiblw_Id (lw5n_sep_dec q n) false.
Proof.
  intros q m n Hge Hloq Hqhi.
  assert (Ha : Qle (lw5n_lo n) (lw5n_cell_lo m)).
  { unfold lw5n_lo, lw5n_cell_lo.
    assert (Hcore : Qle (4 * pie_partial (lw5n_M n + 1))
                        (4 * pie_partial (2 * m + 2))).
    { replace (lw5n_M n + 1)%nat with (2 * (8 * n + 10))%nat
        by (rewrite lw5n_M_val; lia).
      (* 偶列驯化：pie_even_mono d j 形需 2*(j+d) ≡ 2m+2，d := m-(8n+9)
         （【607 改判】601 图骨架此行误书 m-(8n+10)，差一常数，lia 正确拒证假边
         条件——8n+9 ≤ m 下 (m-(8n+9))+(8n+9) = m 即 2*(8n+10)+d = 2m+2 ✓） *)
      assert (Hd : ((m - (8 * n + 9)) + (8 * n + 9))%nat = m) by lia.
      remember (m - (8 * n + 9))%nat as d eqn:Hde.
      replace (2 * m + 2)%nat with (2 * ((8 * n + 10) + d))%nat by lia.
      apply pie_mult4_le.
      apply (pie_even_mono d (8 * n + 10)). }
    pose proof (lw5n_eps4_pos n) as He4.
    apply Qlt_le_weak in He4. lra. }
  assert (Hb : Qle (lw5n_cell_hi m) (lw5n_hi n)).
  { unfold lw5n_hi, lw5n_cell_hi.
    assert (Hcore : Qle (4 * pie_partial (2 * m + 1))
                        (4 * pie_partial (lw5n_M n))).
    { assert (Hd : ((m - (8 * n + 9)) + (8 * n + 9))%nat = m) by lia.
      remember (m - (8 * n + 9))%nat as d eqn:Hde.
      replace (2 * m + 1)%nat with (2 * ((8 * n + 9) + d) + 1)%nat by lia.
      replace (lw5n_M n)%nat with (2 * (8 * n + 9) + 1)%nat
        by (rewrite lw5n_M_val; lia).
      apply pie_mult4_le.
      apply (pie_odd_mono d (8 * n + 9)). }
    pose proof (lw5n_eps4_pos n) as He4.
    apply Qlt_le_weak in He4. lra. }
  assert (Hin : lw5n_inwin q n = true).
  { unfold lw5n_inwin.
    rewrite (lw5n_Qle_Qleb_true (lw5n_lo n) q
               (Qle_trans (lw5n_lo n) (lw5n_cell_lo m) q Ha Hloq)).
    rewrite (lw5n_Qle_Qleb_true q (lw5n_hi n)
               (Qle_trans q (lw5n_cell_hi m) (lw5n_hi n) Hqhi Hb)).
    reflexivity. }
  unfold lw5n_sep_dec. rewrite Hin. reflexivity.
Qed.

(* 下界律：预算内存在分离阶 n0 则格序被压在 8·n0+9 之下（obstacle 逆否＋lia 收口） *)
Theorem lw5n_shape_lower : forall (q : Q) (m n0 : nat),
  (n0 <= lw5n_bnd q)%nat -> leiblw_Id (lw5n_sep_dec q n0) true ->
  Qle (lw5n_cell_lo m) q -> Qle q (lw5n_cell_hi m) ->
  (m < 8 * n0 + 9)%nat.
Proof.
  intros q m n0 Hb Hs Hlo Hhi.
  destruct (Nat.le_gt_cases (8 * n0 + 9) m) as [Hge | Hlt].
  - exfalso.
    pose proof (lw5n_cell_obstacle q m n0 Hge Hlo Hhi) as Hf.
    apply leiblw_id_inv in Hs.
    rewrite Hs in Hf. inversion Hf.
  - exact Hlt.
Qed.

(* §6.3 形态定理主句（Set 面带形；= obstacle 逆否＋nsep_least＋nsep_hit 三件合带）。
   注：分量一系 Prop 位 nat 序（B 档注记沿 nsep_bound 先例；本件永不入提取单）。 *)
Theorem lw5n_shape_band : forall (q : Q) (m n0 : nat),
  Qle (lw5n_cell_lo m) q -> Qle q (lw5n_cell_hi m) ->
  (n0 <= lw5n_bnd q)%nat -> leiblw_Id (lw5n_sep_dec q n0) true ->
  And ((m < 8 * n0 + 9)%nat)
      (And ((lw5n_nsep q <= n0)%nat)
           (leiblw_Id (lw5n_sep_dec q (lw5n_nsep q)) true)).
Proof.
  intros q m n0 Hlo Hhi Hb Hs. split.
  - exact (lw5n_shape_lower q m n0 Hb Hs Hlo Hhi).
  - split.
    + exact (lw5n_nsep_least q n0 Hb Hs).
    + exact (lw5n_nsep_hit q n0 Hb Hs).
Qed.

(* §6.4 eps_n 联动常数链（§五 定谳规程：vm_compute 四发实测冻结后回填——
   C1=(17,17) C2=(65,65) C3=(33,33) C4=(129,129)，16n+17/32n+33 与实测全符，
   禁硬凑律满足；k=2 口 8n+9＝直引 lw5n_modulus_val :113，零新行零重证） *)
Lemma lw5n_four_div_quarter : forall n : nat,
  (4 / (lw5n_eps n / 4))%Q == (Z.of_nat (16 * n + 16) # 1)%Q.
Proof.
  intros n.
  assert (H1 : (lw5n_eps n / 4)%Q == (1 # (Pos.of_succ_nat n * 4))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult. cbn [Qnum Qden].
  apply leiblw_qmake_eq.
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  rewrite leiblw_pos_succ.
  replace (Z.pos 4) with 4%Z by reflexivity.
  replace (Z.of_nat (16 * n + 16)) with (16 * Z.of_nat (Datatypes.S n))%Z.
  - lia.
  - replace (16 * n + 16)%nat with (16 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Qed.

(* 模量显式链第二口：pie_modulus(eps_n/4) = 16n+17（vm_compute 定谳回填） *)
Lemma lw5n_modulus_div4_val : forall n : nat,
  pie_modulus (lw5n_eps n / 4) = (16 * n + 17)%nat.
Proof.
  intros n.
  assert (Hx := lw5n_four_div_quarter n).
  assert (Hz' : Qceiling ((Z.of_nat (16 * n + 16) # 1)%Q) = Z.of_nat (16 * n + 16)).
  { pose proof (Qle_ceiling (Z.of_nat (16 * n + 16) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (16 * n + 16) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (proj1 (leiblw_qmake_le _ _ _ _)) in Hub.
    apply (proj1 (leiblw_qmake_lt _ _ _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 4)) = Z.of_nat (16 * n + 16)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 4)) (Z.of_nat (16 * n + 16) # 1)%Q)
      by (apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (16 * n + 16) # 1)%Q (4 / (lw5n_eps n / 4)))
      by (apply qeq_le; apply Qeq_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1. lia. }
  assert (Hs : pie_modulus (lw5n_eps n / 4) = Datatypes.S (16 * n + 16)%nat).
  { unfold pie_modulus. rewrite Hz. f_equal.
    apply Nat2Z.inj.
    apply Z2Nat.id. apply Nat2Z.is_nonneg. }
  rewrite Hs. lia.
Qed.

Lemma lw5n_four_div_eighth : forall n : nat,
  (4 / (lw5n_eps n / 8))%Q == (Z.of_nat (32 * n + 32) # 1)%Q.
Proof.
  intros n.
  assert (H1 : (lw5n_eps n / 8)%Q == (1 # (Pos.of_succ_nat n * 8))%Q).
  { unfold lw5n_eps, Qdiv, Qinv, Qmult. cbn [Qnum Qden]. reflexivity. }
  rewrite H1.
  unfold Qdiv, Qinv, Qmult. cbn [Qnum Qden].
  apply leiblw_qmake_eq.
  rewrite !Z.mul_1_r.
  rewrite Pos2Z.inj_mul.
  rewrite leiblw_pos_succ.
  replace (Z.pos 8) with 8%Z by reflexivity.
  replace (Z.of_nat (32 * n + 32)) with (32 * Z.of_nat (Datatypes.S n))%Z.
  - lia.
  - replace (32 * n + 32)%nat with (32 * Datatypes.S n)%nat by lia.
    symmetry. apply Nat2Z.inj_mul.
Qed.

(* 模量显式链第三口：pie_modulus(eps_n/8) = 32n+33（vm_compute 定谳回填） *)
Lemma lw5n_modulus_div8_val : forall n : nat,
  pie_modulus (lw5n_eps n / 8) = (32 * n + 33)%nat.
Proof.
  intros n.
  assert (Hx := lw5n_four_div_eighth n).
  assert (Hz' : Qceiling ((Z.of_nat (32 * n + 32) # 1)%Q) = Z.of_nat (32 * n + 32)).
  { pose proof (Qle_ceiling (Z.of_nat (32 * n + 32) # 1)%Q) as Hub.
    pose proof (Qceiling_lt (Z.of_nat (32 * n + 32) # 1)%Q) as Hlt.
    cbn [inject_Z] in Hub, Hlt.
    apply (proj1 (leiblw_qmake_le _ _ _ _)) in Hub.
    apply (proj1 (leiblw_qmake_lt _ _ _ _)) in Hlt.
    rewrite !Z.mul_1_r in Hub, Hlt.
    lia. }
  assert (Hz : Qceiling (4 / (lw5n_eps n / 8)) = Z.of_nat (32 * n + 32)).
  { assert (Hle1 : Qle (4 / (lw5n_eps n / 8)) (Z.of_nat (32 * n + 32) # 1)%Q)
      by (apply qeq_le; exact Hx).
    assert (Hle2 : Qle (Z.of_nat (32 * n + 32) # 1)%Q (4 / (lw5n_eps n / 8)))
      by (apply qeq_le; apply Qeq_sym; exact Hx).
    pose proof (Qceiling_resp_le _ _ Hle1) as K1.
    pose proof (Qceiling_resp_le _ _ Hle2) as K2.
    rewrite Hz' in K1. lia. }
  assert (Hs : pie_modulus (lw5n_eps n / 8) = Datatypes.S (32 * n + 32)%nat).
  { unfold pie_modulus. rewrite Hz. f_equal.
    apply Nat2Z.inj.
    apply Z2Nat.id. apply Nat2Z.is_nonneg. }
  rewrite Hs. lia.
Qed.

(* ============================================================ *)
(* §6.5 family_separation 联动面（出窗分离证书＋传递收缩＋口径收尾）      *)
(* ============================================================ *)

(* 出窗=分离证书（实层升格；分离距由 win_pi 自带松量零折半承载）。
   【607 落刀改判】出窗二择一弃 andb_false_iff＋or 分裂——or 非 singleton
   eliminable，Set 目标下 Prop 消去被拒（本席 r10 红案同款）；改 bool 级
   eqn 二分（mono 同款先例），零 Prop 消去。 *)
Theorem lw5n_outwin_sepdist : forall (q : Q) (n : nat),
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)))).
Proof.
  intros q n Hs.
  apply leiblw_id_inv in Hs. unfold lw5n_sep_dec in Hs.
  apply negb_true_iff in Hs. unfold lw5n_inwin in Hs.
  destruct (lw5n_win_pi n) as [Hlo_pi Hhi_pi].
  destruct (leiblw_Qleb (lw5n_lo n) q) eqn:E1.
  - cbn [andb] in Hs.
    apply lw5n_Qleb_false_lt in Hs.
    destruct Hhi_pi as [eps0 [He0 [N0 HN0]]].
    exists (q - lw5n_hi n)%Q. split.
    + apply Qlt_to_QltT. pose proof (QltT_to_Qlt 0 eps0 He0). lra.
    + exists eps0. split.
      * exact He0.
      * exists N0. intros k Hk.
        pose proof (HN0 k Hk) as Hpt. apply QltT_to_Qlt in Hpt.
        change (Qlt eps0 (lw5n_hi n - projT1 cauchy_real_pi_leibniz k)) in Hpt.
        apply Qlt_to_QltT.
        change (Qlt eps0
                  (Qabs (projT1 cauchy_real_pi_leibniz k - q)
                   - (q - lw5n_hi n))%Q).
        apply (Qabs_case (projT1 cauchy_real_pi_leibniz k - q)).
        { intro Hp. lra. }
        { intro Hp. lra. }
  - apply lw5n_Qleb_false_lt in E1.
    destruct Hlo_pi as [eps0 [He0 [N0 HN0]]].
    exists (lw5n_lo n - q)%Q. split.
    + apply Qlt_to_QltT. pose proof (QltT_to_Qlt 0 eps0 He0). lra.
    + exists eps0. split.
      * exact He0.
      * exists N0. intros k Hk.
        pose proof (HN0 k Hk) as Hpt. apply QltT_to_Qlt in Hpt.
        change (Qlt eps0 (projT1 cauchy_real_pi_leibniz k - lw5n_lo n)) in Hpt.
        apply Qlt_to_QltT.
        change (Qlt eps0
                  (Qabs (projT1 cauchy_real_pi_leibniz k - q)
                   - (lw5n_lo n - q))%Q).
        apply (Qabs_case (projT1 cauchy_real_pi_leibniz k - q)).
        { intro Hp. lra. }
        { intro Hp. lra. }
Qed.

(* n_sep 变换律（联动主句）：证书-半径-预算三层变换，非 n_sep^Y 新函数
   （590 §三.五设计注记：禁冒立 Y 侧窗族） *)
Theorem lw5n_nsep_transform : forall (Y : Real) (q : Q) (n : nat) (k : Q),
  real_eq cauchy_real_pi_leibniz Y -> QleT 2 k ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / k)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n k Hseq Hk Hs.
  destruct (lw5n_outwin_sepdist q n Hs) as [c [Hc Hsep]].
  exists c. split.
  - exact Hc.
  - exact (lw2t_sep_transport_k cauchy_real_pi_leibniz Y q c k Hc Hk Hseq Hsep).
Qed.

Theorem lw5n_nsep_transform_k3 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 2)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k3 Hseq lw5n_QleT_k3 Hs).
Qed.

Theorem lw5n_nsep_transform_k1 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 4)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k1 Hseq lw5n_QleT_k1 Hs).
Qed.

Theorem lw5n_nsep_transform_k2 : forall (Y : Real) (q : Q) (n : nat),
  real_eq cauchy_real_pi_leibniz Y ->
  leiblw_Id (lw5n_sep_dec q n) true ->
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const (c / 8)%Q) (real_metric Y (real_const q)))).
Proof.
  intros Y q n Hseq Hs.
  exact (lw5n_nsep_transform Y q n lw5n_k2 Hseq lw5n_QleT_k2 Hs).
Qed.

(* 口径联动收尾：半径缩 k 倍 ⟹ 预算按模量反单调不缩（与 §6.4 显式链对账） *)
Corollary lw5n_bnd_caliber : forall (c : Q) (k : Q), QltT' 0 c -> QleT 2 k ->
  (pie_modulus (c / 2) <= pie_modulus (c / k / 2))%nat.
Proof.
  intros c k Hc Hk.
  assert (Hc2 : QltT' 0 (c / 2)%Q).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat c (Qinv (2 # 1))).
    - exact (QltT'_to_Qlt 0 c Hc).
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  assert (Hck : QltT' 0 (c / k / 2)%Q).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat (c * Qinv k) (Qinv (2 # 1))).
    - apply (Qmult_lt_0_compat c (Qinv k)).
      + exact (QltT'_to_Qlt 0 c Hc).
      + apply Qinv_lt_0_compat.
        pose proof Hk as Hkc. destruct Hkc as [Hklt | Hkid].
        * apply QltT_to_Qlt in Hklt. lra.
        * destruct Hkid. unfold Qlt. simpl. lia.
    - apply Qinv_lt_0_compat. unfold Qlt. simpl. lia. }
  assert (Hle1 : Qle (c / k)%Q c).
  { unfold Qdiv.
    apply (Qle_trans _ (Qinv k * c)%Q).
    - apply qeq_le. apply Qmult_comm.
    - apply (Qle_trans _ (1 * c)%Q).
      + apply (Qmult_le_compat_r (Qinv k) 1 c).
        * pose proof (lw2t_k_inv2_le k Hk) as Hk2. lra.
        * pose proof (QltT'_to_Qlt 0 c Hc) as Hcp. apply Qlt_le_weak. exact Hcp.
      + apply qeq_le. apply Qmult_1_l. }
  assert (Hle2 : Qle (c / k / 2)%Q (c / 2)%Q).
  { unfold Qdiv.
    apply (Qmult_le_compat_r (c * Qinv k) c (Qinv (2 # 1))).
    - exact Hle1.
    - apply (Qlt_le_weak 0 (Qinv (2 # 1))). apply Qinv_lt_0_compat.
      unfold Qlt. simpl. lia. }
  apply lw5n_modulus_antitone.
  - exact Hc2.
  - exact Hck.
  - exact Hle2.
Qed.

(* 中途 PA 站（双发之一；防终验覆盖型漂移，锚＝此刻已闭件全集；§6.5 尾位） *)
Print Assumptions lw5n_QleT_k3.
Print Assumptions lw5n_QleT_k1.
Print Assumptions lw5n_QleT_k2.
Print Assumptions lw5n_modulus_antitone.
Print Assumptions lw5n_shape_mono.
Print Assumptions lw5n_shape_inversion.
Print Assumptions lw5n_cell_obstacle.
Print Assumptions lw5n_shape_lower.
Print Assumptions lw5n_shape_band.
Print Assumptions lw5n_modulus_div4_val.
Print Assumptions lw5n_modulus_div8_val.
Print Assumptions lw5n_outwin_sepdist.
Print Assumptions lw5n_nsep_transform.
Print Assumptions lw5n_nsep_transform_k3.
Print Assumptions lw5n_nsep_transform_k1.
Print Assumptions lw5n_nsep_transform_k2.
Print Assumptions lw5n_bnd_caliber.

(* ============================================================ *)
(* §7 计算抽查＋提取＋假设审计（S2 追加站；S1 :560-:574 一行不动）        *)
(* ============================================================ *)

Eval vm_compute in (lw5n_cell_lo 0, lw5n_cell_hi 0).
Eval vm_compute in (lw5n_sep_dec (22 # 7)%Q 5, lw5n_inwin (22 # 7)%Q 5).
Eval vm_compute in (pie_modulus (lw5n_eps 3 / 4)%Q, (16 * 3 + 17)%nat).

Separate Extraction lw5n_inwin lw5n_k3 lw5n_k1 lw5n_k2 lw5n_cell_hi lw5n_cell_lo.

Print Assumptions lw5n_win_pi.
Print Assumptions lw5n_win_width.
Print Assumptions lw5n_win_nested.
Print Assumptions lw5n_inwin_close_pt.
Print Assumptions lw5n_nsep_bound.
Print Assumptions lw5n_nsep_hit.
Print Assumptions lw5n_nsep_least.
Print Assumptions lw5n_nsep_minimal.
Print Assumptions lw5n_shape_mono.
Print Assumptions lw5n_shape_inversion.
Print Assumptions lw5n_cell_obstacle.
Print Assumptions lw5n_shape_lower.
Print Assumptions lw5n_shape_band.
Print Assumptions lw5n_modulus_div4_val.
Print Assumptions lw5n_modulus_div8_val.
Print Assumptions lw5n_modulus_antitone.
Print Assumptions lw5n_outwin_sepdist.
Print Assumptions lw5n_nsep_transform.
Print Assumptions lw5n_nsep_transform_k3.
Print Assumptions lw5n_nsep_transform_k1.
Print Assumptions lw5n_nsep_transform_k2.
Print Assumptions lw5n_bnd_caliber.
Print Assumptions lw5n_QleT_k3.
Print Assumptions lw5n_QleT_k1.
Print Assumptions lw5n_QleT_k2.
