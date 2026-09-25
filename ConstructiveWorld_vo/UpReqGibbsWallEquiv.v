(* ============================================================ *)
(* UpReqGibbsWallEquiv.v                                                *)
(*                                                                     *)
(* 使命：gibbs plain-le 结构不可证结果与受限 LPO 的双向归约。            *)
(* 主件：gwe_plain_le_lpo / gwe_lpo_plain_le 双向件与 GibbsWall 等价器   *)
(*   gwe_equivalence。                                                  *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、UpReqLpoEquiv；Stdlib         *)
(*   QArith.QArith、QArith.Qabs、Lia。                                  *)
(* 备注：零公理；主件零假设负载；不证该命题为假，证其与受限 LPO 等价    *)
(*   （构造性边界）。                                                   *)
(* ============================================================ *)
(*                                                                     *)
(* 公理面：本件零公理——三重机制证据：①req 面（S02:460），              *)
(*   Or := A + B 是 Set 值和（S01:69）——证 plain-le 须交左支或右支      *)
(*   见证；②左支 real_lt 需一致有理 gap（S02:456），而 p==q 点 KL==0    *)
(*   无 gap；③req 接口刻意无三分律字段（Id 层 lt_dec 三分律在 S01:333   *)
(*   在案、req 接口全降逐 eps）——「序无消去」是接口设计使然，该         *)
(*   不可证结果属结构性永久参数位，非未消解项。                         *)
(*                                                                     *)
(*   本件把该结论升级为机器检验的双向归约：                             *)
(*                                                                     *)
(*   GibbsWall : Set := forall p q : Real,                              *)
(*     real_le real_zero (gwe_G p q)   （gibbs 泛函族 plain-le 形）     *)
(*   载体 gwe_G p q := (p − q)·(p − q)：gibbs 相对熵的 Pinsker 型       *)
(*   二次形——对角零点参数位（真 KL 的 KL(p,p)=0 恒等式的机制代表）      *)
(*   gwe_diag_zero 机检在件；真泛函的泛型参数位由 GibbMechanism 段      *)
(*   抽象承载（接口 GWf + 对角零点参数位 + 载体编码参数位）。           *)
(*                                                                     *)
(*   gwe_plain_le_lpo : GibbsWall -> rLPO（保底件，不可证结果 ⟹ 受限    *)
(*       LPO：左支在 real_zero 载体位灭绝（gwe_diag_no_gap 出 ⊥），     *)
(*       全部判据数据只能来自 real_eq 支=逐点归零见证——                 *)
(*       「Or 的两支只剩一支可给」=受限 LPO 的数据内容）。              *)
(*   gwe_lpo_plain_le : rLPO -> GibbsWall（受限 LPO ⟹ 该不可证结果：    *)
(*       决策器两支分别供 real_lt 间隙与 real_eq 逐点归零见证，         *)
(*       经 lpn_backward 在载体差位直连）。                             *)
(*   gwe_equivalence : And (GibbsWall -> rLPO) (rLPO -> GibbsWall)。    *)
(*                                                                     *)
(*   组合式：SqWall/rLPO/lpn_forward/lpn_backward 逐字复用作            *)
(*   congruence 升维——第二类不可证结果与第一类同归约强度。              *)
(*                                                                     *)
(*   注意：本件不证 GibbsWall 假，证 GibbsWall 与 rLPO 等价——           *)
(*   「不可证性」以条件定理（若不可证结果成立则受限 LPO）承载，         *)
(*   不可证结果等价登记口径。                                           *)
(*                                                                     *)
(* 纪律：纯构造性 Set 层、语句面全 Type/sigT/自定义 And/Or/QltT，        *)
(*       零 Prop 泄露；两面均机器检验完整证明。                         *)
(* 对标：构造性分析序三分不可证结果（LPO 族）的等价登记形。             *)
(* 构造性注记：零承认、公理面为空；主件零假设负载；Part 5 机制段三      *)
(*   节参为显式接口前提（真前提登记，见该段申报注）。                   *)
(* 编译配方：Rocq 9.1 直调 rocq c -Q . "" UpReqGibbsWallEquiv.v，        *)
(*   cpu_guard 包装。                                                   *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqLpoEquiv.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：机制桥三件——real_eq 兼容（congruence）与 Q 层负界        *)
(* ============================================================ *)

(* Q 层：a ≤ |a|（UpReqLpoEquiv q_abs_nonneg 同族引理） *)
Lemma gwe_q_le_abs : forall a : Q, a <= Qabs a.
Proof.
  intros a.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    apply Qle_refl.
  - rewrite (q_abs_neg_eq a Hneg).
    apply (Qle_trans a 0 (- a)).
    + exact Hneg.
    + apply (Qopp_le_compat a 0).
      exact Hneg.
Qed.

(* Q 层：−|a| ≤ a（下界半边，供 real_eq 兼容链的负向界） *)
Lemma gwe_q_negabs_le : forall w : Q, - Qabs w <= w.
Proof.
  intros w.
  assert (Hlb : Qle (- (Qabs w)) (- w)).
  { apply (Qopp_le_compat w (Qabs w)).
    apply gwe_q_le_abs. }
  destruct (Qlt_le_dec 0 w) as [Hpos | Hneg].
  - apply (Qle_trans (- (Qabs w)) (- w) w).
    + exact Hlb.
    + apply (Qle_trans (- w) 0 w).
      * apply (Qle_trans (- w) (- 0) 0).
        -- apply (Qopp_le_compat 0 w). apply Qlt_le_weak. exact Hpos.
        -- assert (Hn0 : - 0 == 0) by exact (Qeq_refl 0).
           rewrite Hn0.
           apply Qle_refl.
      * apply Qlt_le_weak. exact Hpos.
  - rewrite (q_abs_neg_eq w Hneg).
    assert (Hnn : - - w == w) by ring.
    rewrite Hnn.
    apply Qle_refl.
Qed.

(* real_eq 右元兼容：y == z ⟹ real_lt x y -> real_lt x z        *)
(* （供隙 eps' := eps/2；z_n − x_n = (y_n − x_n) + (z_n − y_n)，  *)
(*   y_n − x_n > eps、−eps/2 ≤ z_n − y_n ⟹ eps/2 < z_n − x_n）    *)
Lemma gwe_lt_congr_r : forall x y z : Real,
  real_eq y z -> real_lt x y -> real_lt x z.
Proof.
  intros x y z Hyz [eps [Heps [N HN]]].
  assert (Hh : Qlt 0 (1#2)) by exact Z.lt_0_1.
  assert (Hpos : QltT 0 (eps * (1#2))).
  { apply Qlt_to_QltT.
    assert (H0 : 0 * (1#2) < eps * (1#2))
      by (apply Qmult_lt_compat_r; [exact Hh | apply QltT_to_Qlt; exact Heps]).
    rewrite Qmult_0_l in H0.
    exact H0. }
  destruct (Hyz (eps * (1#2)) Hpos) as [N2 HN2].
  exists (eps * (1#2)). split.
  - exact Hpos.
  - exists (max N N2). intros n Hn.
    assert (H1 : QltT eps (projT1 y n - projT1 x n)).
    { apply HN. apply NatLe_lift.
      exact (PeanoNat.Nat.le_trans N (max N N2) n
               (PeanoNat.Nat.le_max_l N N2) (NatLe_drop (max N N2) n Hn)). }
    assert (H2 : QltT (Qabs (projT1 y n - projT1 z n)) (eps * (1#2))).
    { apply HN2. apply NatLe_lift.
      exact (PeanoNat.Nat.le_trans N2 (max N N2) n
               (PeanoNat.Nat.le_max_r N N2) (NatLe_drop (max N N2) n Hn)). }
    apply Qlt_to_QltT.
    (* Q 层链（Qlt 语句面重写全通，QltT 位只进不出——AA15R 前科规避） *)
    assert (Hsum : projT1 z n - projT1 x n
                   == (projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)) by ring.
    rewrite Hsum.
    assert (H1q : Qlt eps (projT1 y n - projT1 x n)) by (apply QltT_to_Qlt; exact H1).
    assert (H2q : Qlt (Qabs (projT1 y n - projT1 z n)) (eps * (1#2)))
      by (apply QltT_to_Qlt; exact H2).
    (* −eps/2 ≤ z_n − y_n：|y_n−z_n| == |z_n−y_n| 顶面换形 + Qopp 翻转 *)
    assert (Hab : Qabs (projT1 y n - projT1 z n) == Qabs (projT1 z n - projT1 y n)).
    { assert (Hopp : projT1 z n - projT1 y n == - (projT1 y n - projT1 z n)) by ring.
      rewrite Hopp.
      apply Qeq_sym.
      apply Qabs_opp. }
    assert (Hflip : Qlt (- (eps * (1#2))) (- (Qabs (projT1 z n - projT1 y n)))).
    { assert (Hflip0 : Qlt (- (eps * (1#2))) (- (Qabs (projT1 y n - projT1 z n))))
        by (apply (Qopp_lt_compat (Qabs (projT1 y n - projT1 z n))
                                  (eps * (1#2))); exact H2q).
      rewrite Hab in Hflip0.
      exact Hflip0. }
    assert (Hb : Qle (- (eps * (1#2))) (projT1 z n - projT1 y n)).
    { apply Qlt_le_weak.
      apply (Qlt_le_trans (- (eps * (1#2)))
                          (- (Qabs (projT1 z n - projT1 y n)))
                          (projT1 z n - projT1 y n)).
      - exact Hflip.
      - exact (gwe_q_negabs_le (projT1 z n - projT1 y n)). }
    assert (Hfin : Qlt (eps + - (eps * (1#2)))
                       ((projT1 y n - projT1 x n) + (projT1 z n - projT1 y n)))
      by (apply (Qplus_lt_le_compat eps (projT1 y n - projT1 x n)
                       (- (eps * (1#2))) (projT1 z n - projT1 y n) H1q Hb)).
    assert (Hhalf : eps + - (eps * (1#2)) == eps * (1#2)) by ring.
    rewrite Hhalf in Hfin.
    exact Hfin.
Qed.

(* real_eq 右元兼容：y == z ⟹ real_eq x y -> real_eq x z（传递直连） *)
Lemma gwe_eq_congr_r : forall x y z : Real,
  real_eq y z -> real_eq x y -> real_eq x z.
Proof.
  intros x y z Hyz Hxy.
  exact (real_eq_trans x y z Hxy Hyz).
Qed.

(* real_le 右元兼容：real_le = Or(rt,re) 两支分别经上两件——        *)
(*   CWC 结论①的机制位：Or 两支对兼容性的封闭性。                   *)
Lemma gwe_le_congr_r : forall x y z : Real,
  real_eq y z -> real_le x y -> real_le x z.
Proof.
  intros x y z Hyz Hle.
  destruct Hle as [Hlt | Heq].
  - apply inl. exact (gwe_lt_congr_r x y z Hyz Hlt).
  - apply inr. exact (gwe_eq_congr_r x y z Hyz Heq).
Qed.

(* ============================================================ *)
(* Part 2：gibbs 泛函族与两面语句                                 *)
(* ============================================================ *)

(* 载体差：d(p,q) := p − q（对角归零的 gibbs 差分位） *)
Definition gwe_diff (p q : Real) : Real := real_plus p (real_opp q).

(* gibbs 泛函族载体：KL 的 Pinsker 型二次形 (p−q)²                   *)
(*   对角零点 = 真 KL 的 KL(p,p)=0 恒等式结构参数位（Part 3 机检）；  *)
(*   真泛函的泛型参数位抽象见 Part 5 GibbMechanism 段。              *)
Definition gwe_G (p q : Real) : Real :=
  real_mult (gwe_diff p q) (gwe_diff p q).

(* 不可证结果的全称数据形：gibbs plain-le 形（Or 形语句面）       *)
Definition GibbsWall : Set :=
  forall p q : Real, real_le real_zero (gwe_G p q).

(* ============================================================ *)
(* Part 3：结构参数位两件——对角零点（KL(p,p)=0）与左支灭绝（无 gap）*)
(* ============================================================ *)

(* 参数位①：对角零点——KL(p,p)=0 恒等式的载体机制形                    *)
(*   逐点差 projT1 real_zero n − projT1 (gwe_G p p) n == 0，          *)
(*   经 real_eq_of_zero_diff（S02:2308，N=0 统一证明模式）完成。       *)
Lemma gwe_diag_zero : forall p : Real, real_eq real_zero (gwe_G p p).
Proof.
  intros p.
  apply (real_eq_of_zero_diff real_zero (gwe_G p p)).
  intros n.
  unfold gwe_G.
  rewrite (real_mult_proj (real_plus p (real_opp p)) (real_plus p (real_opp p)) n).
  rewrite (real_plus_proj p (real_opp p) n).
  rewrite (real_opp_proj p n).
  assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
  rewrite Hz.
  ring.
Qed.

(* 参数位②：左支灭绝——p==q 点 KL==0 无一致有理 gap（机检形）          *)
(*   real_lt real_zero (G p p) 给 eps 界下：G_n > eps；对角零点给      *)
(*   G_n == 0——Qlt 0 < eps < 0 矛盾出 ⊥，任意 A 可得。                *)
Lemma gwe_diag_no_gap : forall p : Real,
  real_lt real_zero (gwe_G p p) -> forall A : Set, A.
Proof.
  intros p [eps [Heps [N HN]]] A.
  pose proof (QltT_to_Qlt 0 eps Heps) as HepsQ.
  destruct (gwe_diag_zero p eps Heps) as [N2 HN2].
  assert (H1 : QltT eps (projT1 (gwe_G p p) (max N N2)
                         - projT1 real_zero (max N N2))).
  { apply HN. apply NatLe_lift. exact (PeanoNat.Nat.le_max_l N N2). }
  assert (Hzero : projT1 (gwe_G p p) (max N N2)
                  - projT1 real_zero (max N N2) == 0).
  { unfold gwe_G.
    rewrite (real_mult_proj (real_plus p (real_opp p)) (real_plus p (real_opp p))
                            (max N N2)).
    rewrite (real_plus_proj p (real_opp p) (max N N2)).
    rewrite (real_opp_proj p (max N N2)).
    assert (Hz : projT1 real_zero (max N N2) == 0) by exact (Qeq_refl 0).
    rewrite Hz.
    ring. }
  apply QltT_to_Qlt in H1.
  rewrite Hzero in H1.
  destruct (Qlt_irrefl 0 (Qlt_trans 0 eps 0 HepsQ H1)).
Qed.

(* ============================================================ *)
(* Part 4：两面定理——保底件与主件                                  *)
(* ============================================================ *)

(* 载体桥：gwe_G x real_zero == x·x（real_eq_of_zero_diff 直连）     *)
Lemma gwe_sq_bridge : forall x : Real,
  real_eq (gwe_G x real_zero) (real_mult x x).
Proof.
  intros x.
  apply (real_eq_of_zero_diff (gwe_G x real_zero) (real_mult x x)).
  intros n.
  unfold gwe_G.
  rewrite (real_mult_proj (real_plus x (real_opp real_zero))
                          (real_plus x (real_opp real_zero)) n).
  rewrite (real_mult_proj x x n).
  rewrite (real_plus_proj x (real_opp real_zero) n).
  rewrite (real_opp_proj real_zero n).
  assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
  rewrite Hz.
  ring.
Qed.

(* 保底件：不可证结果 ⟹ 受限 LPO（正向归约在 gibbs 载体位的          *)
(*   congruence 升维——Hwall 在载体位 (x, real_zero) 的 plain-le 见证，经载体桥 *)
(*   换形为 SqWall 实例，lpn_forward 提取零问题决策数据）。           *)
Theorem gwe_plain_le_lpo : GibbsWall -> rLPO.
Proof.
  intros Hwall.
  apply lpn_forward.
  intros x.
  exact (gwe_le_congr_r real_zero (gwe_G x real_zero) (real_mult x x)
           (gwe_sq_bridge x) (Hwall x real_zero)).
Qed.

(* 反向：受限 LPO ⟹ 该不可证结果（决策器在载体差位 d(p,q) 直接供     *)
(*   plain-le 见证——gwe_G p q 与 real_mult (gwe_diff p q)            *)
(*   (gwe_diff p q) 定义性同项，lpn_backward 实例零桥直连）。         *)
Theorem gwe_lpo_plain_le : rLPO -> GibbsWall.
Proof.
  intros Hdec p q.
  exact (lpn_backward Hdec (gwe_diff p q)).
Qed.

(* 主件（判定件）：双向归约 *)
Definition gwe_equivalence : And (GibbsWall -> rLPO) (rLPO -> GibbsWall) :=
  (gwe_plain_le_lpo, gwe_lpo_plain_le).

(* ============================================================ *)
(* Part 5：结构性永久参数位的抽象定型（GibbMechanism 段）             *)
(*   任一 (p,q) 族泛函 GWf 带两参数位——参数位A 对角零点（KL(p,p)=0    *)
(*   接口位）+ 参数位B 载体编码（任意实数可编码进 GWf p q 的平方位）   *)
(*   ——则其 plain-le 形给出 SqWall，经 lpn_forward 升为受限 LPO。      *)
(*   真 gibbs 泛函的参数位A 由 log 链恒等式供给，参数位B 由温度对      *)
(*   编码供给；req 接口刻意不供三分律，故两参数位不可在接口内消去      *)
(*   ——不可证结果是接口设计使然，登记入结构性永久参数位。             *)
(*   （抽象反向无参数位可走：GWf 无界时 rLPO 不供 GWf 族的 plain-le，  *)
(*   故泛型段只做正向；具体载体族的两向在 Part 4 全验。）              *)
(* 机制段假设面申报：本段三节参（GWf、gmech_diag、gmech_carr）为显式   *)
(*   接口前提——①使用核查：两前提均被段内定理真实使用（gmech_carr 供   *)
(*   编码对、gmech_diag 供对角零点）；②供给核查：具体 GWf 实例的供给   *)
(*   （log 链恒等式）在本件 Require 面之外，禁反向引入；抽象段即本件   *)
(*   使命，前提保留为条件定理前件（真前提登记）。                      *)
(* ============================================================ *)

Section GibbMechanism.

Variable GWf : Real -> Real -> Real.
Hypothesis gmech_diag : forall p : Real, real_eq real_zero (GWf p p).
Hypothesis gmech_carr : forall x : Real,
  sigT (fun p : Real => sigT (fun q : Real =>
    real_eq (GWf p q) (real_mult x x))).

Theorem gmech_wall_sqwall :
  (forall p q : Real, real_le real_zero (GWf p q)) -> SqWall.
Proof.
  intros Hwall x.
  destruct (gmech_carr x) as [p [q Heq]].
  exact (gwe_le_congr_r real_zero (GWf p q) (real_mult x x) Heq (Hwall p q)).
Qed.

Theorem gmech_wall_lpo :
  (forall p q : Real, real_le real_zero (GWf p q)) -> rLPO.
Proof.
  intros Hwall.
  exact (lpn_forward (gmech_wall_sqwall Hwall)).
Qed.

End GibbMechanism.

(* ============================================================ *)
(* Part 6：判定打印                                                 *)
(* ============================================================ *)

Print Assumptions gwe_plain_le_lpo.
Print Assumptions gwe_lpo_plain_le.
Print Assumptions gwe_equivalence.
Print Assumptions gmech_wall_sqwall.
Print Assumptions gmech_wall_lpo.
