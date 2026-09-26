(* ============================================================ *)
(* UpReqSymplecticBridge.v —— spec2x2 判别式框架 × 辛旋转特征刻画桥接件 *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S12_B5RecycleSF、S13_NLiveAudit、UpReqSpec2x2、SymplecticRotationSpec。 *)
(* 编译配方：coqc -q -Q . "" UpReqSymplecticBridge.v（9.1 工具链）。 *)
(*                                                                *)
(* 使命：桥接两座已注册模块——                                      *)
(*   供体一 UpReqSpec2x2.v（M2(Q) 2×2 判别式/特征值率框架：          *)
(*     sp2_qdisc / sp2_qgap / sp2_qnewton / sp2_sqrt_rate_core:692 / *)
(*     sp2_sqrt_rate:864 / sp2_eig_gap:926）；                       *)
(*   供体二 SymplecticRotationSpec.v（辛旋转特征刻画：               *)
(*     srs_rot_characterization:43 / srs_power_rate:140 /            *)
(*     srs_power_contract:190）。                                    *)
(*   两件各自成立但 A∘B 复合此前无人陈述——本件补足该组合。           *)
(*                                                                *)
(* 数学内容（全 Q 载体、分量展开形，避 M2(Q) 矩阵环实例；             *)
(*   复数特征值不可在 Q 载体直接陈述——诚实形态=特征多项式层）：       *)
(*   槽1 特征方程：rot(c,s)=[[c,-s],[s,c]] 的 char-poly 恒等式       *)
(*     (t-c)²+s² == t²-2ct+(c²+s²)；单位档 == t²-2ct+1；             *)
(*     Q 根强制退化：char-poly 取零 ⟹ t==c ∧ s==0                   *)
(*     （Δ<0 支的 Q 载体诚实形态=无 genuine Q 根，非空化禁臆造）。    *)
(*   槽2 判别式对账：sp2_qdisc 对称槽值(c,c,-s)==4s²≥0，旋转真特征    *)
(*     判别式 (a-d)²+4bb'==-4s²≤0——互补相反、恰在 s==0 重合          *)
(*     （syb_slot_agree：对称槽看不见 Δ<0 支——障碍账定理化）；       *)
(*     负判别式支非负性假言 ⟹ s==0（Q 有序域构造性论证）。           *)
(*   槽3 速率对接：‖rot p‖² == ‖p‖² − qgap(c²+s²,1)·‖p‖²；           *)
(*     n 步版 ‖rotⁿp‖² == ‖p‖² − qgap·geomsum_n·‖p‖²                *)
(*     （srs_power_exact × 几何和恒等式 1-qⁿ==(1-q)·Σ 真组合）；      *)
(*     等距经 qgap 槽归零复原 srs_power_rate（双向忠实性）；          *)
(*     压缩档 0≤q≤1 ⟹ 亏损≥0（srs_power_contract 的 qgap 槽重述）。  *)
(*                                                                *)
(* 出口面：QId / And / QleT'（全 Set 层语句位）。内部支撑件允许      *)
(*   Qle/Qeq 位（先例：供体 srs_qnpow_bnd Qle 前提件）。             *)
(*                                                                *)
(* 构造性注记：本件零公理、零承认件、零参数、零猜想、零弃证；         *)
(*   零经典逻辑（无排中法）；纯构造性；                              *)
(*   出口件无 Prop 层前提位；无 Obj.magic。                          *)
(*   文末 Print Assumptions 全表（预期仅基座闭包）。                  *)
(* 非平凡性：char-poly/几何和恒等式=环层真实现（非定义复读）；        *)
(*   判别式对账与退化定理=Qmult_integral 两级+Qle_antisym 有序域论证；*)
(*   亏损恒等式=双供体件 srs_power_exact × sp2_qgap 的真组合。        *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import UpReqSpec2x2.
Require Import SymplecticRotationSpec.
From Stdlib Require Import QArith.QArith QArith.Qabs.

Open Scope Q_scope.

Section UpReqSymplecticBridge.

(* ============================================================ *)
(* §0 内部支撑件                                                    *)
(* ============================================================ *)

(* Q 层平方零消去（Qmult_integral 双支同形）。内部 Prop 位支撑件。 *)
Lemma syb_qsq0_inv : forall q : Q, (q * q == 0)%Q -> (q == 0)%Q.
Proof.
  intros q H. apply Qmult_integral in H. destruct H as [H | H]; exact H.
Qed.

(* 几何和：Σ_{k<n} q^k（步进式 = 前缀和 + q^k，配 1-qⁿ 因式分解）。 *)
Fixpoint syb_geomsum (n : nat) (q : Q) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S k => syb_geomsum k q + srs_qnpow k q
  end.

(* 几何和恒等式：1 − qⁿ == (1 − q)·Σ_{k<n} q^k。 *)
Theorem syb_geomsum_pow : forall (n : nat) (q : Q),
  QId (1 - srs_qnpow n q) ((1 - q) * syb_geomsum n q).
Proof.
  intros n. induction n as [| k IH]; intro q.
  - apply qid_intro. cbn [srs_qnpow syb_geomsum]. ring.
  - apply qid_intro.
    cbn [srs_qnpow syb_geomsum].
    assert (Hi : 1 - srs_qnpow k q
                 == (1 - q) * syb_geomsum k q)
      by exact (qid_elim _ _ (IH q)).
    assert (Hexp : (1 - q) * (syb_geomsum k q + srs_qnpow k q)
                   == (1 - q) * syb_geomsum k q + (1 - q) * srs_qnpow k q)
      by ring.
    rewrite Hexp, <- Hi. ring.
Qed.

(* q ≥ 0 ⟹ qⁿ ≥ 0（压缩档几何和正负性之支）。 *)
Lemma syb_qnpow_nn : forall (n : nat) (q : Q), Qle 0 q -> Qle 0 (srs_qnpow n q).
Proof.
  intros n. induction n as [| k IH]; intros q H0.
  - cbn [srs_qnpow]. exact sp2_qle_lit1.
  - cbn [srs_qnpow]. apply Qmult_le_0_compat; [exact H0 | exact (IH q H0)].
Qed.

(* q ≥ 0 ⟹ Σ_{k<n} q^k ≥ 0。 *)
Lemma syb_geomsum_nn : forall (n : nat) (q : Q), Qle 0 q -> Qle 0 (syb_geomsum n q).
Proof.
  intros n. induction n as [| k IH]; intros q H0.
  - cbn [syb_geomsum]. apply Qle_refl.
  - cbn [syb_geomsum].
    assert (Hs : Qle (0 + 0) (syb_geomsum k q + srs_qnpow k q)).
    { apply Qplus_le_compat; [exact (IH q H0) | exact (syb_qnpow_nn k q H0)]. }
    assert (Hz : (0 == 0 + 0)%Q) by ring.
    exact (sp2_qle_eq_l (0 + 0)%Q 0%Q
             (syb_geomsum k q + srs_qnpow k q)%Q Hz Hs).
Qed.

(* ============================================================ *)
(* §1 G1 槽1：特征多项式恒等（Q 环层）+ Q 根强制退化                  *)
(* ============================================================ *)

(* char-poly 恒等：rot(c,s)=[[c,-s],[s,c]] 的特征多项式在 t 处的值
   (t−c)²+s² 展开为 t²−2ct+(c²+s²)（迹 2c、行列式 c²+s²）。 *)
Theorem syb_charpoly : forall c s t : Q,
  QId ((t - c) * (t - c) + s * s) (t * t - 2 * (c * t) + (c * c + s * s)).
Proof.
  intros c s t. apply qid_intro. ring.
Qed.

(* 单位档（c²+s²==1）：char-poly == t²−2ct+1。 *)
Theorem syb_charpoly_unit : forall c s t : Q,
  QId (c * c + s * s) 1 ->
  QId ((t - c) * (t - c) + s * s) (t * t - 2 * (c * t) + 1).
Proof.
  intros c s t H.
  pose proof (qid_elim _ _ (syb_charpoly c s t)) as H1.
  apply qid_intro. rewrite H1, (qid_elim _ _ H). apply Qeq_refl.
Qed.

(* Q 根强制退化：char-poly 在 t 处取零 ⟹ t==c ∧ s==0。
   Δ<0 支的 Q 载体诚实形态：非退化旋转（s≠0）无 genuine Q 根——
   论证纯构造（两平方均非负 + 和为零 ⟹ 各自为零，Qle_antisym）。 *)
Theorem syb_root_forces_degenerate : forall c s t : Q,
  QId ((t - c) * (t - c) + s * s) 0 ->
  And (QId t c) (QId s 0).
Proof.
  intros c s t H.
  assert (Hq : (t - c) * (t - c) + s * s == 0) by exact (qid_elim _ _ H).
  assert (Ha : Qle 0 ((t - c) * (t - c))) by apply srs_qsq_nonneg.
  assert (Hb : Qle 0 (s * s)) by apply srs_qsq_nonneg.
  (* (t−c)² ≤ (t−c)²+s² == 0 ⟹ (t−c)² == 0 *)
  assert (Hale : Qle ((t - c) * (t - c)) ((t - c) * (t - c) + s * s))
    by exact (sp2_qle_plus_r _ _ Hb).
  assert (Ha0 : (t - c) * (t - c) == 0).
  { apply Qle_antisym.
    - exact (Qle_trans _ _ _ Hale (sp2_qeq_le _ _ Hq)).
    - exact Ha. }
  (* s² ≤ s²+(t−c)² == (t−c)²+s² == 0 ⟹ s² == 0 *)
  assert (Hble : Qle (s * s) (s * s + (t - c) * (t - c)))
    by exact (sp2_qle_plus_r _ _ Ha).
  assert (Hcomm : (s * s + (t - c) * (t - c))%Q
                  == ((t - c) * (t - c) + s * s)%Q) by ring.
  assert (Hb0 : s * s == 0).
  { apply Qle_antisym.
    - exact (Qle_trans _ _ _ Hble
               (sp2_qle_eq_l _ _ _ Hcomm (sp2_qeq_le _ _ Hq))).
    - exact Hb. }
  assert (Htc : t - c == 0).
  { apply Qmult_integral in Ha0. destruct Ha0 as [Hm1 | Hm2]; [exact Hm1 | exact Hm2]. }
  split; apply qid_intro.
  - assert (Ht : t == c + (t - c)) by ring.
    rewrite Htc, Qplus_0_r in Ht. exact Ht.
  - exact (syb_qsq0_inv s Hb0).
Qed.

(* ============================================================ *)
(* §2 G1 槽2：保范/保辛在桥语句面的重述（对接 srs_rot_characterization）*)
(* ============================================================ *)

Theorem syb_symplectic_isometry : forall c s : Q,
  QId (c * c + s * s) 1 ->
  And (forall p : (Q * Q)%type, QId (norms2 (rot c s p)) (norms2 p))
      (forall p q : (Q * Q)%type,
         QId (symp2 (rot c s p) (rot c s q)) (symp2 p q)).
Proof.
  intros c s H.
  destruct (srs_rot_characterization c s) as [Hfwd _].
  exact (Hfwd H).
Qed.

(* ============================================================ *)
(* §3 G2 槽2：判别式对账——sp2 对称槽 vs 旋转真特征判别式              *)
(*   （组合缝的精确刻画 + 障碍账定理化）                              *)
(* ============================================================ *)

(* 一般 2×2 特征判别式恒等：(a+d)²−4(ad−bb′) == (a−d)²+4bb′。
   对称阵（b==b′）时退化为 sp2_qdisc 形 (a−d)²+4b²——sp2 槽的适用域
   恰为对称位。 *)
Theorem syb_chardisc_gen : forall a d b b' : Q,
  QId ((a + d) * (a + d) - 4 * (a * d - b * b'))
      ((a - d) * (a - d) + 4 * b * b').
Proof.
  intros a d b b'. apply qid_intro. ring.
Qed.

(* 旋转 rot(c,s) 的真特征判别式（(a−d)²+4bb′ 形在 a=d=c,b=−s,b′=s）：
   == −4s² ≤ 0——负判别式支的具体载体。 *)
Theorem syb_chardisc_rot : forall c s : Q,
  QId ((c - c) * (c - c) + 4 * (- s) * s) (-4 * (s * s)).
Proof.
  intros c s. apply qid_intro. ring.
Qed.

(* sp2 对称槽在旋转阵位（c,c,−s）的槽值：== 4s² ≥ 0。 *)
Theorem syb_qdisc_slot_rot : forall c s : Q,
  QId (sp2_qdisc c c (- s)) (4 * (s * s)).
Proof.
  intros c s. apply qid_intro. unfold sp2_qdisc. ring.
Qed.

(* 障碍账定理化：若对称槽值 == 真特征判别式，则 s == 0。
   即 sp2_qdisc 槽恰在退化旋转处才看见旋转的特征判别式；
   Δ<0 支（s≠0）被对称槽结构性遮蔽——组合缝的精确定理化。 *)
Theorem syb_slot_agree : forall c s : Q,
  QId (sp2_qdisc c c (- s)) ((c - c) * (c - c) + 4 * (- s) * s) ->
  QId s 0.
Proof.
  intros c s H.
  assert (Hq : sp2_qdisc c c (- s) == (c - c) * (c - c) + 4 * (- s) * s)
    by exact (qid_elim _ _ H).
  assert (Hz : (sp2_qdisc c c (- s)
                - ((c - c) * (c - c) + 4 * (- s) * s))%Q == 0).
  { rewrite Hq. ring. }
  unfold sp2_qdisc in Hz.
  (* 槽差 == 8s²（恒等）；差为零 ⟹ 8s² == 0 ⟹ s² == 0 ⟹ s == 0 *)
  assert (H8 : (8 * (s * s))%Q == 0).
  { apply (Qeq_trans (8 * (s * s))%Q
             (((c - c) * (c - c) + 4 * - s * - s)
              - ((c - c) * (c - c) + 4 * - s * s))%Q 0%Q).
    - ring.
    - exact Hz. }
  assert (Hm : ((1#8) * (8 * (s * s)))%Q == 0).
  { rewrite H8. apply Qmult_0_r. }
  assert (Has : ((1#8) * (8 * (s * s)))%Q == (((1#8) * 8) * (s * s))%Q)
    by ring.
  rewrite Has in Hm.
  assert (Hunit : (((1#8) * 8)%Q) == 1) by reflexivity.
  rewrite Hunit, Qmult_1_l in Hm.
  apply qid_intro. exact (syb_qsq0_inv s Hm).
Qed.

(* 负判别式支非负性假言 ⟹ 退化：把「真特征判别式 ≥ 0」当假言，
   在 Q 有序域上构造性推出 s == 0（4s² ≥ 0 与 −4s² ≥ 0 夹逼）。
   这是 sp2_eig_gap 的 real_le 前提在旋转载体上取等的唯一路径。 *)
Theorem syb_negdisc_degenerate : forall c s : Q,
  QleT' 0 ((c - c) * (c - c) + 4 * (- s) * s) ->
  QId s 0.
Proof.
  intros c s H.
  assert (Hq : Qle 0 ((c - c) * (c - c) + 4 * (- s) * s))
    by (apply QleT'_to_Qle; exact H).
  assert (H0 : (4 * (- s) * s == (c - c) * (c - c) + 4 * (- s) * s)%Q)
    by ring.
  assert (Hg : Qle 0 (4 * (- s) * s)) by exact (sp2_qle_eq_r _ _ _ H0 Hq).
  assert (Hpos : Qle 0 (4 * (s * s))).
  { assert (Hid : (4 * (s * s) == (2 * s) * (2 * s))%Q) by ring.
    exact (sp2_qle_eq_r 0%Q ((2 * s) * (2 * s))%Q (4 * (s * s))%Q Hid
             (srs_qsq_nonneg (2 * s)%Q)). }
  assert (Hid2 : (4 * (- s) * s == - (4 * (s * s)))%Q) by ring.
  assert (Ho : Qle (- (4 * (s * s))) (- 0))
    by exact (Qopp_le_compat _ _ Hpos).
  assert (Hflip0 : Qle (4 * (- s) * s) (- 0))
    by exact (sp2_qle_eq_l (-(4 * (s * s)))%Q (4 * (- s) * s)%Q
               (- 0)%Q Hid2 Ho).
  assert (Hn0 : (- 0)%Q == 0) by ring.
  assert (Hflip : Qle (4 * (- s) * s) 0)
    by exact (sp2_qle_eq_r _ _ _ Hn0 Hflip0).
  assert (Hza : (4 * (- s) * s == 0)%Q)
    by (apply Qle_antisym; [exact Hflip | exact Hg]).
  (* 纯 Qeq 链回负化：4s² == 0（零 Prop 消除——Set 目标位红线） *)
  assert (Hneg : (- (4 * (s * s)))%Q == 0)
    by exact (Qeq_trans _ _ _ (Qeq_sym _ _ Hid2) Hza).
  assert (H4 : (4 * (s * s))%Q == 0).
  { pose proof (Qopp_involutive (4 * (s * s))%Q) as Hi.
    rewrite Hneg in Hi.
    assert (Hn0b : (- 0)%Q == 0) by ring.
    rewrite Hn0b in Hi. exact (Qeq_sym _ _ Hi). }
  (* (1#4) 乘法链：4s² == 0 ⟹ s² == 0 ⟹ s == 0 *)
  assert (Hm : ((1#4) * (4 * (s * s)))%Q == 0).
  { rewrite H4. apply Qmult_0_r. }
  assert (Has : ((1#4) * (4 * (s * s)))%Q == (((1#4) * 4) * (s * s))%Q)
    by ring.
  rewrite Has in Hm.
  assert (Hunit : (((1#4) * 4)%Q) == 1) by reflexivity.
  rewrite Hunit, Qmult_1_l in Hm.
  apply qid_intro. exact (syb_qsq0_inv s Hm).
Qed.

(* ============================================================ *)
(* §4 G2 槽3：速率对接——单步亏损恒等式（qgap 槽）                     *)
(* ============================================================ *)

(* 单步亏损恒等式：‖rot p‖² == ‖p‖² − qgap(c²+s², 1)·‖p‖²。
   srs_rot_amp（放大因子 D·‖p‖²）与 sp2_qgap（1−D）的真组合：
   亏损恰为单位点处的谱隙 × 范数。 *)
Theorem syb_rot_qgap_defect : forall (c s : Q) (p : (Q * Q)%type),
  QId (norms2 (rot c s p))
      (norms2 p - sp2_qgap (c * c + s * s) 1 * norms2 p).
Proof.
  intros c s p.
  assert (Hamp : norms2 (rot c s p) == (c * c + s * s) * norms2 p)
    by exact (srs_rot_amp c s p).
  apply qid_intro. unfold sp2_qgap. rewrite Hamp. ring.
Qed.

(* n 步亏损恒等式：‖rotⁿ p‖² == ‖p‖² − qgap·geomsum_n·‖p‖²。
   srs_power_exact（(c²+s²)ⁿ 速率律）× syb_geomsum_pow（几何和）
   的真组合——G3 幂速率对接主件。 *)
Theorem syb_power_qgap_defect : forall (n : nat) (c s : Q) (p : (Q * Q)%type),
  QId (norms2 (srs_rot_pow n c s p))
      (norms2 p - sp2_qgap (c * c + s * s) 1
                   * syb_geomsum n (c * c + s * s) * norms2 p).
Proof.
  intros n c s p.
  assert (Hex : norms2 (srs_rot_pow n c s p)
                == srs_qnpow n (c * c + s * s) * norms2 p)
    by exact (qid_elim _ _ (srs_power_exact n c s p)).
  assert (Hg : 1 - srs_qnpow n (c * c + s * s)
               == (1 - (c * c + s * s)) * syb_geomsum n (c * c + s * s))
    by exact (qid_elim _ _ (syb_geomsum_pow n (c * c + s * s))).
  apply qid_intro. unfold sp2_qgap.
  rewrite Hex, Qmult_1_l, <- Hg. ring.
Qed.

(* 等距的 qgap 槽复原：c²+s²==1 ⟹ qgap 归零 ⟹ 亏损恒等式退化回
   srs_power_rate——桥的双向忠实性验证（经 sp2_qgap 槽，非直抄）。 *)
Theorem syb_power_isometry_via_qgap : forall (n : nat) (c s : Q)
    (p : (Q * Q)%type),
  QId (c * c + s * s) 1 ->
  QId (norms2 (srs_rot_pow n c s p)) (norms2 p).
Proof.
  intros n c s p H.
  assert (Hz : sp2_qgap (c * c + s * s) 1 == 0).
  { unfold sp2_qgap. rewrite (qid_elim _ _ H). ring. }
  pose proof (qid_elim _ _ (syb_power_qgap_defect n c s p)) as Hd.
  rewrite Hz in Hd.
  repeat rewrite Qmult_0_l in Hd.
  rewrite sp2_qminus_0_r in Hd.
  apply qid_intro. exact Hd.
Qed.

(* 压缩档对接：0 ≤ q ≤ 1（q := c²+s²）⟹ 亏损 ≥ 0——
   srs_power_contract 前提组的 sp2_qgap 槽重述（QleT' 入口、出口）。 *)
Theorem syb_contract_defect_nonneg : forall (n : nat) (c s : Q)
    (p : (Q * Q)%type),
  QleT' (c * c + s * s) 1 -> QleT' 0 (c * c + s * s) ->
  QleT' 0 (sp2_qgap (c * c + s * s) 1
           * syb_geomsum n (c * c + s * s) * norms2 p).
Proof.
  intros n c s p H1 H0.
  assert (Hq1 : Qle (c * c + s * s) 1) by (apply QleT'_to_Qle; exact H1).
  assert (Hq0 : Qle 0 (c * c + s * s)) by (apply QleT'_to_Qle; exact H0).
  assert (Hu : (1 * 1)%Q == 1) by reflexivity.
  assert (Hle : Qle (c * c + s * s) (1 * 1))
    by exact (sp2_qle_eq_r _ _ _ Hu Hq1).
  assert (Hgap : Qle 0 (sp2_qgap (c * c + s * s) 1))
    by exact (sp2_qgap_ge0 _ _ Hle).
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  - apply Qmult_le_0_compat; [exact Hgap | exact (syb_geomsum_nn n (c * c + s * s) Hq0)].
  - exact (srs_norms2_nonneg p).
Qed.

(* ============================================================ *)
(* §5 桥接闭合件：三槽逐一核验的 And 桥                              *)
(* ============================================================ *)

Theorem syb_spec_bridge : forall c s t : Q,
  And (* 槽1 特征方程：char-poly 恒等（Q 环层） *)
      (QId ((t - c) * (t - c) + s * s)
           (t * t - 2 * (c * t) + (c * c + s * s)))
      (And (* 槽2 判别式：sp2 对称槽值 / 旋转真判别式 / 障碍账重合定理 *)
        (And (QId (sp2_qdisc c c (- s)) (4 * (s * s)))
             (And (QId ((c - c) * (c - c) + 4 * (- s) * s) (-4 * (s * s)))
                  (QId (sp2_qdisc c c (- s))
                       ((c - c) * (c - c) + 4 * (- s) * s) -> QId s 0)))
        (* 槽3 速率：单步亏损恒等式（sp2_qgap 槽对接） *)
        (forall p : (Q * Q)%type,
           QId (norms2 (rot c s p))
               (norms2 p - sp2_qgap (c * c + s * s) 1 * norms2 p))).
Proof.
  intros c s t. split.
  - exact (syb_charpoly c s t).
  - split.
    + split.
      * exact (syb_qdisc_slot_rot c s).
      * split.
        -- exact (syb_chardisc_rot c s).
        -- exact (syb_slot_agree c s).
    + exact (syb_rot_qgap_defect c s).
Qed.

End UpReqSymplecticBridge.

(* ============================================================ *)
(* 审查留痕：出口件全表 Print Assumptions                             *)
(* ============================================================ *)

Print Assumptions syb_charpoly.
Print Assumptions syb_charpoly_unit.
Print Assumptions syb_root_forces_degenerate.
Print Assumptions syb_symplectic_isometry.
Print Assumptions syb_chardisc_gen.
Print Assumptions syb_chardisc_rot.
Print Assumptions syb_qdisc_slot_rot.
Print Assumptions syb_slot_agree.
Print Assumptions syb_negdisc_degenerate.
Print Assumptions syb_rot_qgap_defect.
Print Assumptions syb_geomsum_pow.
Print Assumptions syb_power_qgap_defect.
Print Assumptions syb_power_isometry_via_qgap.
Print Assumptions syb_contract_defect_nonneg.
Print Assumptions syb_spec_bridge.
