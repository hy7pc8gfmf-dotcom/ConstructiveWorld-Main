(* ============================================================ *)
(* abl_normconv_real.v —— M 判别（级数收敛判别）的 Real 脸两步（移植式）          *)
(*                                                                          *)
(* 使命：级数泛型 BanachAlg 脸独大（UpReqNormConv ncv_ 族在役）而 Real 脸     *)
(*   全零；勘定：BanachAlg.bnorm : BA -> Q 硬连字段封死实例式——本件走        *)
(*   「移植式」：把 M 判别数学核（优势项级数收敛⟹原级数收敛的夹界论证）       *)
(*   在 Real 脸直建，非实例化。两步：①rnv_compare_cauchy 比较判别核（        *)
(*   |a_k| ≤_R b_k 逐项夹界＋b 尾和直控⟹段和柯西＋部分和差形                *)
(*   rnv_compare_cauchy_partial）；②rnv_m_test_geom M 判别特化（见构造性）。 *)
(* 容器核实（锚点实拍）：Real 级数在本库无可反引容器——本件自立部分和函数     *)
(*   容器 rnv_sum／段和容器 rnv_seg（nat 折叠 real_plus）及收敛谓词           *)
(*   rnv_conv／rnv_tail_small／rnv_conv_partial（「先立容器」结论的落地）。   *)
(* 依赖：全在册零外前置：S01_BaseRing（NatLe/NatLe_drop/NatLe_lift）；        *)
(*   S02_CauchyComplete（Real/real_eq/real_lt/real_le Or 形/QeqT/Qeq 系/     *)
(*   real_eq_trans/real_eq_of_zero_diff/real_plus 系/real_const 系/界与序系）；*)
(*   S03_QExp（q_pow/arch_decay/Qle_to_QleT'/real_abs 系/q_abs_abs_triangle）；*)
(*   S07_RealSetoidExpLog（real_const 系/plus_compat 系/real_abs 系＋        *)
(*   Module RealSetoid real_eq_plus_compat）；Stdlib QArith/Qring/Arith/Lia。 *)
(* 构造性：零承认语句、零经典逻辑、零未证前提位；语句面纯 Set（real_eq/       *)
(*   real_lt/real_le Or 形/QeqT/QltT/NatLe 全 Set 值，禁 Prop 泄露——序索引  *)
(*   记录用 S01 NatLe 非 (<=)%nat）。句前缀 rnv_：与 ncv_ 族整库相撞，改取    *)
(*   避让（全库 0 命中）。诚实边界：①取「b 尾和直控形」（rnv_tail_small：     *)
(*   非负优函数级数尾的上界收敛）而非 |b 尾| 双侧柯西形——后者需 x ≤ |x| 的   *)
(*   Or 形精确自反界，与库内 abs 族全 eps 形同源的构造性不可证事实，如实取   *)
(*   单侧判别面；三角不等式沿 real_abs_triangle_le_eps 走 eps/2 穿线（主     *)
(*   会计成本所在）。②特化基率固定 ½·C，一般 0<c<1 实数基引擎留待后续件     *)
(*   （本件不虚报）。零新分析引擎：全链有限和＋Q 几何账＋逐 eps 放缩。       *)
(* 编译配方：ulimit -s 65532 && nice -19 rocq c -native-compiler no -Q        *)
(*   <缓存根> "" abl_normconv_real.v；尾 Print Assumptions 四定理全 Closed。  *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(* 第 0 部分：容器（部分和／段和／收敛谓词）——「需先立部分和函数容器」落地      *)
(* ============================================================ *)

(* 部分和：s_n := Σ_{k<n} a k（nat 折叠 real_plus，右结合追加） *)
Fixpoint rnv_sum (a : nat -> Real) (n : nat) : Real :=
  match n with
  | O%nat => real_zero
  | Datatypes.S k => real_plus (rnv_sum a k) (a k)
  end.

(* 段和：rnv_seg a m d ＝ Σ_{k=m}^{m+d-1} a k（左结合取项，d 为段长；           *)
(*   使几何尾界归纳与常值段投影逐点对位） *)
Fixpoint rnv_seg (a : nat -> Real) (m d : nat) : Real :=
  match d with
  | O%nat => real_zero
  | Datatypes.S d' => real_plus (a m) (rnv_seg a (Datatypes.S m) d')
  end.

(* 段和柯西形收敛谓词：∀eps>0(Q) ∃N ∀m≥N ∀d, |seg a m d| < eps *)
Definition rnv_conv (a : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall (m d : nat), NatLe N m ->
      real_lt (real_abs (rnv_seg a m d)) (real_const eps)).

(* 优函数尾和直控形（比较判别的判别面前提，见头注诚实边界） *)
Definition rnv_tail_small (b : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall (m d : nat), NatLe N m ->
      real_lt (rnv_seg b m d) (real_const eps)).

(* 部分和差形收敛谓词（AI 草案原形：∀m n≥N, |s_m − s_n| < eps） *)
Definition rnv_conv_partial (a : nat -> Real) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      real_lt (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a n))))
              (real_const eps)).

(* ============================================================ *)
(* 第 1 部分：Real 环／序小件（库内缺位的零级联补件）                            *)
(* ============================================================ *)

(* eps/2 正性小件（Qlt_shift_div_l 配方，同 real_const_pos 内账） *)
Lemma rnv_half_pos0 : forall eps : Q, QltT 0 eps -> QltT 0 (eps / 2)%Q.
Proof.
  intros eps Heps. apply Qlt_to_QltT. apply Qlt_shift_div_l.
  - change (Qlt 0 2). compute. reflexivity.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* eps/2 + eps/2 == eps（Q 层预算闭合） *)
Lemma rnv_half2 : forall eps : Q, (eps / 2 + eps / 2)%Q == eps.
Proof.
  intros eps. replace (eps / 2) with (eps * (1#2))%Q by reflexivity. ring.
Qed.

(* 0 + x ≈ x（real_eq_of_zero_diff 逐点 ring） *)
Lemma rnv_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x + 0 ≈ x *)
Lemma rnv_plus_zero_r : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x + y) + (−x) ≈ y（和差消去） *)
Lemma rnv_plus_opp_r : forall x y : Real,
  real_eq (real_plus (real_plus x y) (real_opp x)) y.
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x − y ≈ −(y − x)（差的反号） *)
Lemma rnv_opp_minus : forall x y : Real,
  real_eq (real_plus x (real_opp y)) (real_opp (real_plus y (real_opp x))).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 加法四元重排：(x + (y + z)) + w ≈ (x + y) + (z + w)（assoc/compat 链） *)
Lemma rnv_plus_shuffle : forall x y z w : Real,
  real_eq (real_plus (real_plus x (real_plus y z)) w)
          (real_plus (real_plus x y) (real_plus z w)).
Proof.
  intros x y z w.
  apply (real_eq_trans _ (real_plus x (real_plus (real_plus y z) w))).
  - exact (real_eq_sym _ _ (real_plus_assoc x (real_plus y z) w)).
  - apply (real_eq_trans _ (real_plus x (real_plus y (real_plus z w)))).
    + exact (RealSetoid.real_eq_plus_compat x (real_plus (real_plus y z) w) x
               (real_plus y (real_plus z w))
               (real_eq_refl x) (real_eq_sym _ _ (real_plus_assoc y z w))).
    + exact (real_plus_assoc x y (real_plus z w)).
Qed.

(* real_le 的 real_eq 双侧运输（Or 形两支：lt 走 eq_lt_lt 链、eq 走 trans） *)
Lemma rnv_le_eq : forall x y x' y' : Real,
  real_le x y -> real_eq x x' -> real_eq y y' -> real_le x' y'.
Proof.
  intros x y x' y' Hxy Hxx' Hyy'.
  destruct Hxy as [Hlt | Heq].
  - exact (inl (real_lt_eq_lt x' y y'
                       (real_eq_lt_lt x' x y (real_eq_sym x x' Hxx') Hlt) Hyy')).
  - exact (inr (real_eq_trans x' x y' (real_eq_sym x x' Hxx')
                       (real_eq_trans x y y' Heq Hyy'))).
Qed.

(* real_abs 与 real_eq 交换（destruct 消形：real_abs/real_const 均透明可约） *)
Lemma rnv_abs_eq_compat : forall x y : Real,
  real_eq x y -> real_eq (real_abs x) (real_abs y).
Proof.
  intros x y Hxy eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N. intros n Hn.
  destruct x as [u Hu]. destruct y as [v Hv]. cbn [projT1 real_abs].
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (Qabs (Qabs (u n) - Qabs (v n))) (Qabs (u n - v n)) eps).
  - exact (q_abs_abs_triangle (u n) (v n)).
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.

(* 常值升脸共用小件：QeqT c d ⟹ real_eq (real_const c) (real_const d) *)
(*   （同 ②-A pir_const_qeqT 配方；本件内联自给） *)
Lemma rnv_const_qeqT : forall c d : Q, QeqT c d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd eps Heps. exists 0%nat. intros n _.
  apply Qlt_to_QltT. apply (Qle_lt_trans _ 0).
  - pose proof (qeqT_imp_qeq c d Hcd) as Heq.
    pose proof (Qminus_comp c d Heq d d (Qeq_refl d)) as Hm.
    assert (Hdd : (d - d)%Q == 0) by ring.
    pose proof (Qeq_trans _ _ _ Hm Hdd) as Hm2.
    pose proof (Qabs_wd (c - d) 0 Hm2) as Habs1.
    pose proof (Qabs_pos 0 (Qle_refl 0)) as Habs2.
    apply qeq_le. exact (Qeq_trans _ _ _ Habs1 Habs2).
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* |real_const c| ≈ real_const |c|（abs 换形的常值特例） *)
Lemma rnv_abs_const : forall c : Q, real_eq (real_abs (real_const c)) (real_const (Qabs c)).
Proof.
  intros c. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_abs real_const]. ring.
Qed.

(* ============================================================ *)
(* 第 2 部分：和代数（部分和—段和桥）                                          *)
(* ============================================================ *)

(* 部分和—段和代数桥：s_{m+d} ≈ s_m + seg a m d（归纳 d，compat/assoc 两步账） *)
Lemma rnv_sum_seg : forall (a : nat -> Real) (d m : nat),
  real_eq (rnv_sum a (m + d)) (real_plus (rnv_sum a m) (rnv_seg a m d)).
Proof.
  intros a d. induction d as [| d IH]; intro m.
  - rewrite Nat.add_0_r. exact (real_eq_sym _ _ (rnv_plus_zero_r (rnv_sum a m))).
  - rewrite Nat.add_succ_r. cbn [rnv_sum rnv_seg].
    pose proof (IH (Datatypes.S m)) as IHh.
    apply (real_eq_trans _ (real_plus (rnv_sum a (Datatypes.S m)) (rnv_seg a (Datatypes.S m) d))).
    + exact IHh.
    + exact (real_eq_sym _ _ (real_plus_assoc (rnv_sum a m) (a m) (rnv_seg a (Datatypes.S m) d))).
Qed.

(* 部分和差的段和换形：s_{m+d} − s_m ≈ seg a m d *)
Lemma rnv_diff_seg : forall (a : nat -> Real) (d m : nat),
  real_eq (real_plus (rnv_sum a (m + d)) (real_opp (rnv_sum a m))) (rnv_seg a m d).
Proof.
  intros a d m.
  pose proof (rnv_sum_seg a d m) as Hs.
  apply (real_eq_trans
           (real_plus (rnv_sum a (m + d)) (real_opp (rnv_sum a m)))
           (real_plus (real_plus (rnv_sum a m) (rnv_seg a m d)) (real_opp (rnv_sum a m)))
           (rnv_seg a m d)).
  - exact (RealSetoid.real_eq_plus_compat (rnv_sum a (m + d)) (real_opp (rnv_sum a m))
             (real_plus (rnv_sum a m) (rnv_seg a m d)) (real_opp (rnv_sum a m))
             Hs (real_eq_refl _)).
  - exact (rnv_plus_opp_r (rnv_sum a m) (rnv_seg a m d)).
Qed.

(* ============================================================ *)
(* 第 3 部分：Q 层几何账（½ 基：正性／单调衰减／几何段和上界）                    *)
(* ============================================================ *)

(* Qle 的 Qeq 双侧运输 *)
Lemma rnv_qle_eq : forall a b a' b' : Q,
  Qle a b -> Qeq a a' -> Qeq b b' -> Qle a' b'.
Proof.
  intros a b a' b' Hab Haa Hbb.
  exact (Qle_trans a' a b' (qeq_le a' a (Qeq_sym a a' Haa))
           (Qle_trans a b b' Hab (qeq_le b b' Hbb))).
Qed.

(* 0 ≤ 1/2（QleT' 计算直读 + QleT'_to_Qle 桥） *)
Lemma rnv_qle_0_half : Qle 0 (1#2)%Q.
Proof. exact (QleT'_to_Qle 0 (1#2)%Q id_refl). Qed.

(* (1/2)^d ≥ 0 *)
Lemma rnv_q_pow_half_pos : forall d : nat, Qle 0 (q_pow (1#2)%Q d).
Proof.
  induction d as [| d IH].
  - change (0 <= 1)%Q. apply Qlt_le_weak. compute. reflexivity.
  - cbn [q_pow].
    apply (rnv_qle_eq (0 * (1#2))%Q (q_pow (1#2)%Q d * (1#2))%Q 0%Q
             ((1#2) * q_pow (1#2)%Q d)%Q).
    + exact (Qmult_le_compat_r 0%Q (q_pow (1#2)%Q d) (1#2)%Q IH rnv_qle_0_half).
    + ring.
    + ring.
Qed.

(* 几何衰减单调：(1/2)^{m+d} ≤ (1/2)^m *)
Lemma rnv_q_pow_half_dec : forall (d m : nat),
  Qle (q_pow (1#2)%Q (m + d)) (q_pow (1#2)%Q m).
Proof.
  intros d m. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d))%nat by lia.
    cbn [q_pow].
    apply (Qle_trans _ (q_pow (1#2)%Q (m + d))).
    + (* (1#2)·qp(m+d) ≤ qp(m+d)：×1 收缩 + ring 换形 *)
      apply (rnv_qle_eq ((1#2) * q_pow (1#2)%Q (m + d))%Q
               (1%Q * q_pow (1#2)%Q (m + d))%Q
               ((1#2) * q_pow (1#2)%Q (m + d))%Q
               (q_pow (1#2)%Q (m + d))).
      * exact (Qmult_le_compat_r (1#2)%Q 1%Q (q_pow (1#2)%Q (m + d))
                 (QleT'_to_Qle (1#2)%Q 1%Q id_refl)
                 (rnv_q_pow_half_pos (m + d))).
      * apply Qeq_refl.
      * ring.
    + exact IH.
Qed.

(* 常值段逐点投影（Q 侧左递归段和） *)
Fixpoint rnv_q_segL (f : nat -> Q) (m d : nat) : Q :=
  match d with
  | O%nat => 0%Q
  | Datatypes.S d' => f m + rnv_q_segL f (Datatypes.S m) d'
  end.

(* 几何段和上界：segL(C·(1/2)^k) m d ≤ (1/2)^m · (C·2)（归纳 d，m 随步进移位） *)
Lemma rnv_q_segL_pow_bound : forall (C : Q) (d m : nat),
  Qle 0 C ->
  Qle (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) m d)
      (q_pow (1#2)%Q m * (C * 2))%Q.
Proof.
  intros C d. induction d as [| d IH]; intros m HC.
  - assert (Hzc : Qle 0 (C * 2)%Q)
      by exact (Qmult_le_compat_r 0%Q C 2%Q HC (QleT'_to_Qle 0%Q 2%Q id_refl)).
    apply (rnv_qle_eq (0 * (C * 2))%Q (q_pow (1#2)%Q m * (C * 2))%Q 0%Q
             (q_pow (1#2)%Q m * (C * 2))%Q).
    + exact (Qmult_le_compat_r 0%Q (q_pow (1#2)%Q m) (C * 2)%Q
               (rnv_q_pow_half_pos m) Hzc).
    + ring.
    + apply Qeq_refl.
  - cbn [rnv_q_segL].
    pose proof (IH (Datatypes.S m) HC) as IHh.
    pose proof (Qplus_le_compat (C * q_pow (1#2)%Q m) (C * q_pow (1#2)%Q m)
                  (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)
                  (q_pow (1#2)%Q (Datatypes.S m) * (C * 2))%Q
                  (Qle_refl (C * q_pow (1#2)%Q m)) IHh) as H1.
    apply (rnv_qle_eq
             (C * q_pow (1#2)%Q m
              + rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)%Q
             (C * q_pow (1#2)%Q m + q_pow (1#2)%Q (Datatypes.S m) * (C * 2))%Q
             (C * q_pow (1#2)%Q m
              + rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) (Datatypes.S m) d)%Q
             (q_pow (1#2)%Q m * (C * 2))%Q).
    + exact H1.
    + apply Qeq_refl.
    + replace (q_pow (1#2)%Q (Datatypes.S m)) with ((1#2) * q_pow (1#2)%Q m)%Q by reflexivity.
      ring.
Qed.

(* ============================================================ *)
(* 第 4 部分：段和三件（三角 eps 形／逐项支配单调／常值段直读）                   *)
(* ============================================================ *)

(* 段和三角（Bishop eps 形，eps/2 穿线）：|seg a m d| ≤ seg|a| m d + eps *)
Lemma rnv_seg_triangle_eps : forall (a : nat -> Real) (d m : nat) (eps : Q),
  QltT 0 eps ->
  real_le (real_abs (rnv_seg a m d))
          (real_plus (rnv_seg (fun k : nat => real_abs (a k)) m d) (real_const eps)).
Proof.
  intros a d. induction d as [| d IH]; intros m eps Heps.
  - cbn [rnv_seg].
    pose proof (real_lt_eq_lt real_zero (real_const eps)
                  (real_plus real_zero (real_const eps))
                  (real_const_pos eps Heps)
                  (real_eq_sym _ _ (rnv_plus_zero_l (real_const eps)))) as Hlt0.
    exact (inl (real_eq_lt_lt (real_abs real_zero) real_zero
                  (real_plus real_zero (real_const eps)) real_abs_zero_req Hlt0)).
  - cbn [rnv_seg].
    pose proof (rnv_half_pos0 eps Heps) as Hh.
    pose proof (real_abs_triangle_le_eps (a m) (rnv_seg a (Datatypes.S m) d)
                  (real_const (eps / 2)%Q) (real_const_pos (eps / 2)%Q Hh)) as Htri.
    pose proof (IH (Datatypes.S m) (eps / 2)%Q Hh) as IHh.
    (* (|a m| + |seg'|) + eps/2 ≤ (|a m| + (segabs' + eps/2)) + eps/2 *)
    pose proof (real_le_plus_compat (real_abs (a m)) (real_abs (a m))
                  (real_abs (rnv_seg a (Datatypes.S m) d))
                  (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                             (real_const (eps / 2)%Q))
                  (real_le_refl (real_abs (a m))) IHh) as H1.
    pose proof (real_le_plus_compat
                  (real_plus (real_abs (a m)) (real_abs (rnv_seg a (Datatypes.S m) d)))
                  (real_plus (real_abs (a m))
                             (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                        (real_const (eps / 2)%Q)))
                  (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                  H1 (real_le_refl (real_const (eps / 2)%Q))) as H2.
    (* RHS 运输：((A + (B + c)) + c) ≈ ((A + B) + eps)（shuffle ＋ 常值 c+c≈eps） *)
    pose proof (rnv_le_eq
                  (real_plus (real_plus (real_abs (a m))
                               (real_abs (rnv_seg a (Datatypes.S m) d)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                          (real_const (eps / 2)%Q)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (real_abs (rnv_seg a (Datatypes.S m) d)))
                             (real_const (eps / 2)%Q))
                  (real_plus (real_plus (real_abs (a m))
                               (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                             (real_const eps))
                  H2 (real_eq_refl _)
                  (real_eq_trans
                     (real_plus (real_plus (real_abs (a m))
                                  (real_plus (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                                             (real_const (eps / 2)%Q)))
                                (real_const (eps / 2)%Q))
                     (real_plus (real_plus (real_abs (a m))
                                  (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                                (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)))
                     (real_plus (real_plus (real_abs (a m))
                                  (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                                (real_const eps))
                     (rnv_plus_shuffle (real_abs (a m))
                        (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d)
                        (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                     (RealSetoid.real_eq_plus_compat
                        (real_plus (real_abs (a m))
                                   (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                        (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                        (real_plus (real_abs (a m))
                                   (rnv_seg (fun k : nat => real_abs (a k)) (Datatypes.S m) d))
                        (real_const eps)
                        (real_eq_refl _)
                        (rnv_const_qeqT (eps / 2 + eps / 2)%Q eps
                           (qeq_imp_qeqT _ _ (rnv_half2 eps)))))) as H2'.
    apply (real_le_trans _ (real_plus (real_plus (real_abs (a m))
                            (real_abs (rnv_seg a (Datatypes.S m) d)))
                          (real_const (eps / 2)%Q))).
    + exact Htri.
    + exact H2'.
Qed.

(* 逐项 real_le 支配 ⟹ 段和 real_le（real_le_plus_compat 沿归纳） *)
Lemma rnv_seg_le : forall (f g : nat -> Real) (d m : nat),
  (forall k : nat, real_le (f k) (g k)) -> real_le (rnv_seg f m d) (rnv_seg g m d).
Proof.
  intros f g d. induction d as [| d IH]; intros m H.
  - exact (inr (real_eq_refl real_zero)).
  - cbn [rnv_seg].
    exact (real_le_plus_compat (f m) (g m) (rnv_seg f (Datatypes.S m) d) (rnv_seg g (Datatypes.S m) d)
             (H m) (IH (Datatypes.S m) H)).
Qed.

(* 常值段逐点投影：projT1 (rnv_seg F m d) j ≈ Q 段和（左递归对位） *)
Lemma rnv_seg_const_proj : forall (f : nat -> Q) (F : nat -> Real) (d m j : nat),
  (forall k j0 : nat, projT1 (F k) j0 == f k) ->
  projT1 (rnv_seg F m d) j == rnv_q_segL f m d.
Proof.
  intros f F d. induction d as [| d IH]; intros m j H.
  - reflexivity.
  - cbn [rnv_seg rnv_q_segL].
    rewrite real_plus_proj.
    rewrite (IH (Datatypes.S m) j H). rewrite (H m j). reflexivity.
Qed.

(* Qeq⟹Qlt 左侧运输（Qlt_compat Proper 实例直读） *)
Lemma rnv_qeq_qlt_l : forall a b c : Q, Qeq a b -> Qlt b c -> Qlt a c.
Proof.
  intros a b c Hab Hbc.
  exact (proj1 (Qlt_compat b a (Qeq_sym a b Hab) c c (Qeq_refl c)) Hbc).
Qed.

(* Q 加法右移：q + e0 < eps ⟹ e0 < eps − q（Qplus_lt_l ＋ Qlt_compat 换形） *)
Lemma rnv_qlt_shift : forall q e0 eps : Q, Qlt (q + e0) eps -> Qlt e0 (eps - q)%Q.
Proof.
  intros q e0 eps Hq.
  apply (proj1 (Qplus_lt_l e0 (eps - q)%Q q)).
  assert (Hr1 : (e0 + q)%Q == (q + e0)%Q) by ring.
  assert (Hr2 : eps == ((eps - q)%Q + q)%Q) by ring.
  pose proof (Qlt_compat (q + e0)%Q (e0 + q)%Q (Qeq_sym _ _ Hr1)
                eps ((eps - q)%Q + q)%Q Hr2) as Hiff.
  exact (proj1 Hiff Hq).
Qed.

(* Qeq⟹Qlt 右侧运输（Qlt_compat Proper 实例直读） *)
Lemma rnv_qeq_qlt_r : forall a b c : Q, Qeq b c -> Qlt a b -> Qlt a c.
Proof.
  intros a b c Hbc Hab.
  exact (proj1 (Qlt_compat a a (Qeq_refl a) b c Hbc) Hab).
Qed.

(* Q 值直读实严格界：常值段和 + e0 < eps ⟹ real_lt (rnv_seg F m d) (real_const eps) *)
Lemma rnv_seg_const_lt : forall (f : nat -> Q) (F : nat -> Real) (d m : nat) (eps e0 : Q),
  QltT 0 e0 ->
  (forall k j : nat, projT1 (F k) j == f k) ->
  Qlt (rnv_q_segL f m d + e0) eps ->
  real_lt (rnv_seg F m d) (real_const eps).
Proof.
  intros f F d m eps e0 He0 Hpt Hq. unfold real_lt.
  exists e0. split.
  - exact He0.
  - exists 0%nat. intros j _.
    pose proof (rnv_seg_const_proj f F d m j Hpt) as Hpr.
    pose proof (Qminus_comp eps eps (Qeq_refl eps)
                  (projT1 (rnv_seg F m d) j) (rnv_q_segL f m d) Hpr) as Hm.
    apply Qlt_to_QltT.
    apply (rnv_qeq_qlt_r _ _ _ (Qeq_sym _ _ Hm) (rnv_qlt_shift _ _ _ Hq)).
Qed.

(* ============================================================ *)
(* 定理 ①：比较判别核（夹界＋b 尾直控 ⟹ 段和柯西）                              *)
(* ============================================================ *)

Theorem rnv_compare_cauchy : forall (a b : nat -> Real),
  (forall k : nat, real_le (real_abs (a k)) (b k)) ->
  rnv_tail_small b ->
  rnv_conv a.
Proof.
  intros a b Hab Hb eps Heps.
  pose proof (rnv_half_pos0 eps Heps) as Hh.
  destruct (Hb (eps / 2)%Q Hh) as [N HN].
  exists N. intros m d Hm.
  (* |sega| ≤ seg|a| + eps/2 ≤ segb + eps/2 < eps/2 + eps/2 = eps *)
  pose proof (rnv_seg_triangle_eps a d m (eps / 2)%Q Hh) as Htri.
  pose proof (rnv_seg_le (fun k : nat => real_abs (a k)) b d m Hab) as Hmono.
  pose proof (real_le_plus_compat
                (rnv_seg (fun k : nat => real_abs (a k)) m d) (rnv_seg b m d)
                (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                Hmono (real_le_refl (real_const (eps / 2)%Q))) as H1.
  pose proof (real_le_trans (real_abs (rnv_seg a m d))
                (real_plus (rnv_seg (fun k : nat => real_abs (a k)) m d)
                           (real_const (eps / 2)%Q))
                (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q)) Htri H1) as H2.
  pose proof (HN m d Hm) as H3.
  pose proof (real_lt_plus_compat_lt_le (rnv_seg b m d) (real_const (eps / 2)%Q)
                (real_const (eps / 2)%Q) (real_const (eps / 2)%Q)
                H3 (real_le_refl (real_const (eps / 2)%Q))) as H4.
  pose proof (real_lt_eq_lt (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q))
                (real_plus (real_const (eps / 2)%Q) (real_const (eps / 2)%Q))
                (real_const eps) H4
                (rnv_const_qeqT (eps / 2 + eps / 2)%Q eps
                   (qeq_imp_qeqT _ _ (rnv_half2 eps)))) as H5.
  exact (real_le_lt_trans (real_abs (rnv_seg a m d))
           (real_plus (rnv_seg b m d) (real_const (eps / 2)%Q)) (real_const eps) H2 H5).
Qed.

(* 定理 ①'：部分和差形（AI 草案原形 ∀m n≥N）——①核＋代数桥的换形出口 *)
Theorem rnv_compare_cauchy_partial : forall (a b : nat -> Real),
  (forall k : nat, real_le (real_abs (a k)) (b k)) ->
  rnv_tail_small b ->
  rnv_conv_partial a.
Proof.
  intros a b Hab Hb eps Heps.
  destruct (rnv_compare_cauchy a b Hab Hb eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  pose proof (NatLe_drop N m Hm) as Hdm.
  pose proof (NatLe_drop N n Hn) as Hdn.
  destruct (le_lt_dec m n) as [Hmn | Hnm].
  - (* m ≤ n：s_m − s_n ≈ −seg a m (n−m)，|−x| ≈ |x| 换形后用核件 *)
    replace n with (m + (n - m)%nat)%nat by lia.
    pose proof (rnv_diff_seg a (n - m)%nat m) as Hdf.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat))))
                  (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m))))
                  (rnv_opp_minus (rnv_sum a m) (rnv_sum a (m + (n - m)%nat)))) as Heq1.
    pose proof (real_abs_opp
                  (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))) as Heq2.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))
                  (rnv_seg a m (n - m)%nat) Hdf) as Heq3.
    pose proof (real_eq_trans
                  (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat)))))
                  (real_abs (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))))
                  (real_abs (rnv_seg a m (n - m)%nat)) Heq1
                  (real_eq_trans
                     (real_abs (real_opp (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m)))))
                     (real_abs (real_plus (rnv_sum a (m + (n - m)%nat)) (real_opp (rnv_sum a m))))
                     (real_abs (rnv_seg a m (n - m)%nat)) Heq2 Heq3)) as Hchain.
    pose proof (HN m (n - m)%nat (NatLe_lift N m Hdm)) as Hsmall.
    exact (real_eq_lt_lt
             (real_abs (real_plus (rnv_sum a m) (real_opp (rnv_sum a (m + (n - m)%nat)))))
             (real_abs (rnv_seg a m (n - m)%nat)) (real_const eps) Hchain Hsmall).
  - (* n < m：直接换形 s_m − s_n ≈ seg a n (m−n) *)
    replace m with (n + (m - n)%nat)%nat by lia.
    pose proof (rnv_diff_seg a (m - n)%nat n) as Hdf.
    pose proof (rnv_abs_eq_compat
                  (real_plus (rnv_sum a (n + (m - n)%nat)) (real_opp (rnv_sum a n)))
                  (rnv_seg a n (m - n)%nat) Hdf) as Hchain.
    exact (real_eq_lt_lt
             (real_abs (real_plus (rnv_sum a (n + (m - n)%nat)) (real_opp (rnv_sum a n))))
             (real_abs (rnv_seg a n (m - n)%nat)) (real_const eps) Hchain
             (HN n (m - n)%nat (NatLe_lift N n Hdn))).
Qed.

(* ============================================================ *)
(* 定理 ②：M 判别特化（几何率 C·(1/2)^k，库内 arch_decay 形态）                   *)
(* ============================================================ *)

Theorem rnv_m_test_geom : forall (a : nat -> Real) (C : Q),
  QleT' 0 C ->
  (forall k : nat, real_le (real_abs (a k)) (real_const (C * q_pow (1#2)%Q k))) ->
  rnv_conv a.
Proof.
  intros a C HC Hab.
  apply (rnv_compare_cauchy a (fun k : nat => real_const (C * q_pow (1#2)%Q k)) Hab).
  (* b := C·(1/2)^k 的尾直控：Q 几何账＋arch_decay 选 t *)
  intros eps Heps.
  pose proof (rnv_half_pos0 eps Heps) as Hh.
  pose proof (QleT'_to_Qle 0 C HC) as HC0.
  pose proof (Qmult_le_compat_r 0%Q C 2%Q HC0 (QleT'_to_Qle 0%Q 2%Q id_refl)) as Hzc.
  pose proof (Qle_to_QleT' (0 * 4)%Q (C * 4)%Q
                (Qmult_le_compat_r 0%Q C 4%Q HC0 (QleT'_to_Qle 0%Q 4%Q id_refl))) as Hq4.
  destruct (arch_decay (C * 4)%Q (eps / 2)%Q Hq4 Hh) as [t Ht].
  exists t. intros m d Hm.
  pose proof (NatLe_drop t m Hm) as Hle.
  assert (Hmt : Qle (q_pow (1#2)%Q m) (q_pow (1#2)%Q t)).
  { replace m with (t + (m - t))%nat by lia.
    apply rnv_q_pow_half_dec. }
  pose proof (rnv_q_segL_pow_bound C d m HC0) as Hbound.
  pose proof (Qmult_le_compat_r (q_pow (1#2)%Q m) (q_pow (1#2)%Q t) (C * 2)%Q Hmt Hzc) as Hs1.
  assert (Hq2 : q_pow (1#2)%Q t * (C * 2)%Q
                == (C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t)).
  { replace (q_pow (1#2)%Q (Datatypes.S t)) with ((1#2) * q_pow (1#2)%Q t)%Q by reflexivity.
    ring. }
  pose proof (Qle_trans _ _ _ Hs1 (qeq_le _ _ Hq2)) as Hs2.
  pose proof (Qle_trans _ _ _ Hbound Hs2) as Hb2.
  apply (rnv_seg_const_lt (fun k : nat => C * q_pow (1#2)%Q k)
           (fun k : nat => real_const (C * q_pow (1#2)%Q k)) d m eps (eps / 2)%Q Hh).
  - intros k j. exact (real_const_proj _ j).
  - apply (Qle_lt_trans _ ((C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t) + (eps / 2)%Q) eps).
    + exact (Qplus_le_compat
               (rnv_q_segL (fun k : nat => C * q_pow (1#2)%Q k) m d)
               ((C * 4)%Q * q_pow (1#2)%Q (Datatypes.S t))
               (eps / 2)%Q (eps / 2)%Q Hb2 (Qle_refl (eps / 2)%Q)).
    + apply (Qlt_le_trans _ ((eps / 2 + eps / 2)%Q)).
      * exact (Qplus_lt_le_compat (C * 4 * q_pow (1#2)%Q (Datatypes.S t)) (eps / 2)%Q
                  (eps / 2)%Q (eps / 2)%Q (QltT_to_Qlt _ _ Ht)
                  (Qle_refl (eps / 2)%Q)).
      * exact (qeq_le (eps / 2 + eps / 2)%Q eps (rnv_half2 eps)).
Qed.

(* 使用面示件：½ 几何级数本体收敛（C := 1） *)
Theorem rnv_geom_series_conv : rnv_conv (fun k : nat => real_const (q_pow (1#2)%Q k)).
Proof.
  apply (rnv_m_test_geom (fun k : nat => real_const (q_pow (1#2)%Q k)) 1%Q id_refl).
  intros k.
  pose proof (rnv_q_pow_half_pos k) as Hpos.
  assert (Habs : Qabs (q_pow (1#2)%Q k) == q_pow (1#2)%Q k)
    by (apply Qabs_pos; exact Hpos).
  assert (Hq : q_pow (1#2)%Q k == 1 * q_pow (1#2)%Q k) by ring.
  exact (inr (real_eq_trans
           (real_abs (real_const (q_pow (1#2)%Q k)))
           (real_const (Qabs (q_pow (1#2)%Q k)))
           (real_const (1 * q_pow (1#2)%Q k))
           (rnv_abs_const (q_pow (1#2)%Q k))
           (rnv_const_qeqT (Qabs (q_pow (1#2)%Q k)) (1 * q_pow (1#2)%Q k)
              (qeq_imp_qeqT _ _
                 (Qeq_trans (Qabs (q_pow (1#2)%Q k)) (q_pow (1#2)%Q k)
                            (1 * q_pow (1#2)%Q k)
                            Habs
                            Hq))))).
Qed.

(* ============================================================ *)
(* 绿判四件组尾面：Print Assumptions（四定理）                                   *)
(* ============================================================ *)
Print Assumptions rnv_compare_cauchy.
Print Assumptions rnv_compare_cauchy_partial.
Print Assumptions rnv_m_test_geom.
Print Assumptions rnv_geom_series_conv.
