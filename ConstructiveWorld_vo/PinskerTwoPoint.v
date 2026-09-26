(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   p2_kl2_nonneg_b（原 L425，5 句玩具证）                               *)
(*   p2_c_pos（原 L360，3 句玩具证）                                      *)
(* ============================================================ *)

(* ============================================================ *)
(* PinskerTwoPoint.v —— 席位 C14：构造性 Pinsker 型 eps 形前置件        *)
(*   （A4 移植榜 T5 的可着陆核；二点分布 p=(p,1−p)、q=(q,1−q)）          *)
(*                                                                *)
(* 使命：二点 TV-KL 下界（Real 层）。全称 list 形不在本件；本件交付：    *)
(*   主件（降档见证形，如实注明）：TV²>0 且 KL>0 时给出显式闭式常数      *)
(*     c := KL·inv(TV²)（p2_c），满足 0<c（7a）且 c·TV² == KL，从而     *)
(*     Bishop 形 real_le_b (c·TV²) (KL)（7b）。                          *)
(*   降档说明：经典 Pinsker 常数 2（KL ≥ 2·TV²）需 log 的调和型下界      *)
(*     （log t ≥ 2(t−1)/(t+1)）。库内 log 引擎实测仅有：切线上界双支      *)
(*     klst_log_tangent_pos/neg（log x < x−1）、log(1+t) ≤ t、           *)
(*     log(1+t) ≥ t−t²（S06 log_one_plus_ge，二次系数 1 过粗）。         *)
(*     逐项估计链试算表明：仅凭这三件，二次项损失与增益在 p≈q 处精确    *)
(*     相消，得不到任何显式正常数（差一份级数/导数型引擎）。故按任务书   *)
(*     允许的第三档落地「见证真形」：常数 c 为闭式显式项、KL>0 时真正    *)
(*     常数、下界以 real_le_b（∀eps>0, x<y+eps）Set 面出口。            *)
(*     附带真非平凡支承：库内 G07 严格 Gibbs 逐点核只有 p<q 支，本件补   *)
(*     齐 q<p 镜像支（p2_gibbs_core_strict_pgtq），并两支合成二点非停    *)
(*     正能量 kl2>0（Or 前提纪律照 klstb_kl_energy_nonconst_B）。        *)
(*                                                                *)
(* 引擎链（全只读消费）：                                             *)
(*   S08:482 real_kl_term（p·(−log(q/p))）；G07:301 klst_gap_shape      *)
(*   （kl_term(p,q)+(q−p) == p·((x−1)−log x)，x:=q·inv(p)）；           *)
(*   G07:173 klst_log_tangent_pos / G07:2573 klst_log_tangent_neg；     *)
(*   G07:349 klst_gibbs_core_strict（p<q 支）；S03 real_inv_pos_correct；*)
(*   S02/S07 代数与序引擎（real_eq_of_zero_diff 逐点环）；UpRealLeB:63  *)
(*   real_le_b + UpRealLeB3 leb3 桥。                                   *)
(* 支承件 ≥2：p2_tvsq_sym（TV² 对称件）、p2_gibbs_core_strict_pgtq      *)
(*   （镜像 Gibbs 核）、p2_one_minus_antitone（1−x 反序传递）、           *)
(*   p2_kl2_pos（二点非停正能量）。                                     *)
(* 红线自审：出口序谓词全 real_lt/real_le_b（Set 值，零 Prop 语句面）；  *)
(*   Or 前提显式；纯构造（Or 两支显式消解，无排中形态）；全部 Qed；      *)
(*   文尾 Print Assumptions ≥1。                                        *)
(* 编译：coqc -Q ../vorebuild "" -Q . "" PinskerTwoPoint.v              *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import G07_KLWall.
Require Import UpRealLeB.
Require Import UpRealLeB3.

(* ---- 0. 二点分布载件定义 ---- *)

(* p−q（二点 TV=|p−q| 的差元） *)
Definition p2_diff (p q : Real) : Real :=
  real_plus p (real_opp q).

(* TV² := (p−q)² *)
Definition p2_tvsq (p q : Real) : Real :=
  real_mult (p2_diff p q) (p2_diff p q).

(* 1−p *)
Definition p2_one_minus (p : Real) : Real :=
  real_plus real_one (real_opp p).

(* KL := kl_term(p,q) + kl_term(1−p,1−q)（real_kl_term@S08:482） *)
Definition p2_kl2 (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q)) : Real :=
  real_plus (real_kl_term p q Hp Hq)
            (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1).

(* 见证常数 c := KL·inv(TV²)（闭式显式项；TV²>0 证书消 inv） *)
Definition p2_c (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)) : Real :=
  real_mult (p2_kl2 p q Hp Hq Hp1 Hq1) (real_inv_pos (p2_tvsq p q) Htv).

(* 逐点 Q 环放电（real_eq_of_zero_diff@S02:2308 路线，纯差元/单项目标） *)
Ltac p2_ring_eq :=
  apply real_eq_of_zero_diff; intro n0;
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  cbn [projT1 p2_diff p2_one_minus p2_tvsq
       real_plus real_mult real_opp real_one real_zero];
  ring.

(* ---- 1. 支承件一：TV² 对称件 TV²(p,q) == TV²(q,p) ---- *)
Lemma p2_tvsq_sym : forall p q : Real,
  real_eq (p2_tvsq p q) (p2_tvsq q p).
Proof.
  intros p q. p2_ring_eq.
Qed.

(* ---- 2. 差元代数支承：(1−p)+(−(1−q)) == q−p（点级环恒等） ---- *)
Lemma p2_one_minus_diff : forall p q : Real,
  real_eq (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))
          (p2_diff q p).
Proof.
  intros p q. p2_ring_eq.
Qed.

(* ---- 3. 差元正性传递：p<q ⟹ 0 < q−p ---- *)
Lemma p2_diff_pos_of_lt : forall p q : Real,
  real_lt p q -> real_lt real_zero (p2_diff q p).
Proof.
  intros p q Hpq.
  assert (H' : real_lt (real_plus (real_opp p) p)
                       (real_plus (real_opp p) q))
    by exact (real_lt_plus_translate (real_opp p) p q Hpq).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_plus (real_opp p) q) (p2_diff q p)).
  - p2_ring_eq.
  - apply (RealSetoid.real_lt_id_l real_zero
             (real_plus (real_opp p) p) (real_plus (real_opp p) q)).
    + p2_ring_eq.
    + exact H'.
Qed.

(* ---- 4. 支承件二：one-minus 反序传递 p<q ⟹ (1−q) < (1−p) ---- *)
Lemma p2_one_minus_antitone : forall p q : Real,
  real_lt p q -> real_lt (p2_one_minus q) (p2_one_minus p).
Proof.
  intros p q Hpq.
  apply real_lt_zero_minus.
  apply (RealSetoid.real_lt_id_r real_zero
           (p2_diff q p)
           (real_plus (p2_one_minus p) (real_opp (p2_one_minus q)))).
  - apply real_eq_sym. exact (p2_one_minus_diff p q).
  - exact (p2_diff_pos_of_lt p q Hpq).
Qed.

(* ---- 5. 支承件三：镜像严格 Gibbs 逐点核（q<p 支；补 G07 缺支） ---- *)
(*   G07 klst_gibbs_core_strict 只有 p<q 支；本件按同一 klst_gap_shape   *)
(*   环形换形 + klst_log_tangent_neg（x<1 支切线上界）补 q<p 支。        *)
Lemma p2_gibbs_core_strict_pgtq : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hqp : real_lt q p),
  real_lt real_zero
    (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p))).
Proof.
  intros p q Hp Hq Hqp.
  unfold real_kl_term.
  set (X := real_mult q (real_inv_pos p Hp)).
  set (HX := real_mult_positive q (real_inv_pos p Hp) Hq
               (real_inv_pos_pos p Hp)).
  set (L := real_log X HX).
  assert (Hxpos : real_lt real_zero X) by exact HX.
  assert (Hxlt : real_lt X real_one).
  { apply (RealSetoid.real_lt_id_r (real_mult q (real_inv_pos p Hp))
             (real_mult p (real_inv_pos p Hp)) real_one).
    - exact (real_inv_pos_correct p Hp).
    - exact (real_mult_lt_compat q p (real_inv_pos p Hp) Hqp
               (real_inv_pos_pos p Hp)). }
  assert (Htan : real_lt L (real_plus X (real_opp real_one)))
    by exact (klst_log_tangent_neg X HX Hxlt).
  assert (Hgap : real_lt real_zero
                   (real_plus (real_plus X (real_opp real_one))
                              (real_opp L))).
  { apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (real_opp L) (real_plus X (real_opp real_one)))
             (real_plus (real_plus X (real_opp real_one)) (real_opp L))).
    - apply real_plus_comm.
    - apply (RealSetoid.real_lt_id_l real_zero
               (real_plus (real_opp L) L)
               (real_plus (real_opp L) (real_plus X (real_opp real_one)))).
      + apply real_eq_sym.
        apply (real_eq_trans _ (real_plus L (real_opp L)) _).
        * apply real_plus_comm.
        * apply real_plus_opp.
      + exact (real_lt_plus_translate (real_opp L) L
                 (real_plus X (real_opp real_one)) Htan). }
  assert (Hprod : real_lt real_zero
                    (real_mult p (real_plus (real_plus X (real_opp real_one))
                                            (real_opp L))))
    by exact (real_mult_pos_compat p
                (real_plus (real_plus X (real_opp real_one)) (real_opp L))
                Hp Hgap).
  apply (RealSetoid.real_lt_id_r real_zero
           (real_mult p (real_plus (real_plus X (real_opp real_one))
                                   (real_opp L)))
           (real_plus (real_kl_term p q Hp Hq) (real_plus q (real_opp p)))).
  - apply real_eq_sym. exact (klst_gap_shape p q Hp Hq).
  - exact Hprod.
Qed.

(* ---- 6. 支承件四：二点非停正能量（kl2 > 0，p≠q 两支合一） ---- *)
(*   组装：kl2 == [kl(p,q)+(q−p)] + [kl(1−p,1−q)+(p−q)]，p<q 支取        *)
(*   （G07 核 + 镜像核于 (1−p,1−q)），q<p 支对调；±(p−q) 点级相消。      *)
Theorem p2_kl2_pos : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  destruct Hne as [Hpq | Hqp].
  - (* 支 p<q：核 G07 于 (p,q)，镜像核于 (1−p,1−q)（补元换形至 p−q） *)
    assert (H2 : real_lt real_zero
                   (real_plus (real_kl_term (p2_one_minus p)
                                       (p2_one_minus q) Hp1 Hq1)
                              (p2_diff p q))).
    { apply (RealSetoid.real_lt_id_r real_zero
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (p2_diff p q))).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (p2_diff p q)).  (* 续接席注：S07 实签交叉腿序 (a≈c)(b≈d)，成对序误排（9.1 适配税#2） *)
        + apply real_eq_refl.
        + exact (p2_one_minus_diff q p).
      - exact (p2_gibbs_core_strict_pgtq (p2_one_minus p) (p2_one_minus q)
                 Hp1 Hq1 (p2_one_minus_antitone p q Hpq)). }
    assert (Hsum : real_lt real_zero
                     (real_plus
                        (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                        (real_plus (real_kl_term (p2_one_minus p)
                                             (p2_one_minus q) Hp1 Hq1)
                                   (p2_diff p q)))).
    { apply (RealSetoid.real_lt_id_l real_zero real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))).
      - apply real_eq_refl.
      - exact (real_lt_plus_compat real_zero
                 (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                 real_zero
                 (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                      Hp1 Hq1)
                            (p2_diff p q))
                 (klst_gibbs_core_strict p q Hp Hq Hpq) H2). }
    apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_plus (p2_diff q p) (p2_diff p q)))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply (real_eq_trans
               _ (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_plus (p2_diff q p) (p2_diff p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).  (* 续接席注：交叉腿序重排（同前） *)
      -- p2_ring_eq.
      -- apply real_eq_sym. p2_ring_eq.
      * apply real_plus_zero.
    + apply (RealSetoid.real_lt_id_r real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))
               (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_plus (p2_diff q p) (p2_diff p q)))).
      * (* 续接席注：B'-C' 纯 assoc/comm 项链重建（S02 实例，trans/sym/compat 参全显式） *)
        exact (real_eq_trans
          (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
          (real_eq_sym (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))
             (real_plus_assoc (real_kl_term p q Hp Hq) (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))))
          (real_eq_trans
             (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
             (RealSetoid.real_eq_plus_compat (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                (real_eq_refl (real_kl_term p q Hp Hq))
                (real_eq_trans (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                   (real_plus_assoc (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))
                   (real_eq_trans (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                      (RealSetoid.real_eq_plus_compat (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)
                         (real_plus_comm (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_eq_refl (p2_diff p q)))
                      (real_eq_sym (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q))
                         (real_plus_assoc (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p) (p2_diff p q))))))
             (real_plus_assoc (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))))).
      * exact Hsum.
  - (* 支 q<p：镜像核于 (p,q)，核 G07 于 (1−p,1−q)（1−p<1−q） *)
    assert (H2 : real_lt real_zero
                   (real_plus (real_kl_term (p2_one_minus p)
                                       (p2_one_minus q) Hp1 Hq1)
                              (p2_diff p q))).
    { apply (RealSetoid.real_lt_id_r real_zero
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (real_plus (p2_one_minus q)
                                    (real_opp (p2_one_minus p))))
               (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                            Hp1 Hq1)
                          (p2_diff p q))).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (real_plus (p2_one_minus q) (real_opp (p2_one_minus p)))
                 (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)
                 (p2_diff p q)).  (* 续接席注：S07 实签交叉腿序 (a≈c)(b≈d)，成对序误排（9.1 适配税#2） *)
        + apply real_eq_refl.
        + exact (p2_one_minus_diff q p).
      - exact (klst_gibbs_core_strict (p2_one_minus p) (p2_one_minus q)
                 Hp1 Hq1 (p2_one_minus_antitone q p Hqp)). }
    assert (Hsum : real_lt real_zero
                     (real_plus
                        (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                        (real_plus (real_kl_term (p2_one_minus p)
                                             (p2_one_minus q) Hp1 Hq1)
                                   (p2_diff p q)))).
    { apply (RealSetoid.real_lt_id_l real_zero real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))).
      - apply real_eq_refl.
      - exact (real_lt_plus_compat real_zero
                 (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                 real_zero
                 (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                      Hp1 Hq1)
                            (p2_diff p q))
                 (p2_gibbs_core_strict_pgtq p q Hp Hq Hqp) H2). }
    apply (RealSetoid.real_lt_id_r real_zero
             (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_plus (p2_diff q p) (p2_diff p q)))
             (p2_kl2 p q Hp Hq Hp1 Hq1)).
    + apply (real_eq_trans
               _ (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_plus (p2_diff q p) (p2_diff p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_zero).  (* 续接席注：交叉腿序重排（同前） *)
      -- p2_ring_eq.
      -- apply real_eq_sym. p2_ring_eq.
      * apply real_plus_zero.
    + apply (RealSetoid.real_lt_id_r real_zero
               (real_plus
                  (real_plus (real_kl_term p q Hp Hq) (p2_diff q p))
                  (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q)
                                       Hp1 Hq1)
                             (p2_diff p q)))
               (real_plus (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_plus (p2_diff q p) (p2_diff p q)))).
      * (* 续接席注：B'-C' 纯 assoc/comm 项链重建（S02 实例，trans/sym/compat 参全显式） *)
        exact (real_eq_trans
          (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
          (real_eq_sym (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (p2_diff q p)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))
             (real_plus_assoc (real_kl_term p q Hp Hq) (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))))
          (real_eq_trans
             (real_plus (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q)))) (real_plus (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))) (real_plus (real_plus (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_plus (p2_diff q p) (p2_diff p q)))
             (RealSetoid.real_eq_plus_compat (real_kl_term p q Hp Hq) (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_kl_term p q Hp Hq) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                (real_eq_refl (real_kl_term p q Hp Hq))
                (real_eq_trans (real_plus (p2_diff q p) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))) (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                   (real_plus_assoc (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff p q))
                   (real_eq_trans (real_plus (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q)) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q)))
                      (RealSetoid.real_eq_plus_compat (real_plus (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (p2_diff p q) (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q)
                         (real_plus_comm (p2_diff q p) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1)) (real_eq_refl (p2_diff p q)))
                      (real_eq_sym (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))) (real_plus (real_plus (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p)) (p2_diff p q))
                         (real_plus_assoc (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (p2_diff q p) (p2_diff p q))))))
             (real_plus_assoc (real_kl_term p q Hp Hq) (real_kl_term (p2_one_minus p) (p2_one_minus q) Hp1 Hq1) (real_plus (p2_diff q p) (p2_diff p q))))).
      * exact Hsum.
Qed.

(* ---- 7. 主件（降档见证形）：0<c 且 c·TV² ≤_B KL ---- *)

(* 7a. 见证正常数：KL>0 且 TV²>0 ⟹ 0 < c := KL·inv(TV²) *)
Theorem p2_c_pos : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)),
  real_lt real_zero (p2_c p q Hp Hq Hp1 Hq1 Hkl Htv).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hkl Htv.
  unfold p2_c.
  exact (real_mult_positive (p2_kl2 p q Hp Hq Hp1 Hq1)           (real_inv_pos (p2_tvsq p q) Htv) Hkl           (real_inv_pos_pos (p2_tvsq p q) Htv)).
Qed.

(* 7b. 主件：c·TV² == KL（逆元代数链）⟹ Bishop 形 c·TV² ≤_B KL。      *)
(*   Pinsker 型下界的见证真形：常数显式闭式、真正常数（7a）、            *)
(*   下界以 real_le_b（∀eps>0）Set 面出口。                             *)
Theorem p2_pinsker_witness_b : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hkl : real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
  (Htv : real_lt real_zero (p2_tvsq p q)),
  real_le_b (real_mult (p2_c p q Hp Hq Hp1 Hq1 Hkl Htv) (p2_tvsq p q))
            (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hkl Htv.
  assert (Hmain : real_eq
                    (real_mult (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                                 (real_inv_pos (p2_tvsq p q) Htv))
                               (p2_tvsq p q))
                    (p2_kl2 p q Hp Hq Hp1 Hq1)).
  { apply (real_eq_trans
             _ (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                          (real_mult (real_inv_pos (p2_tvsq p q) Htv)
                                     (p2_tvsq p q))) _).
    - apply real_eq_sym.
      exact (real_mult_assoc (p2_kl2 p q Hp Hq Hp1 Hq1)
               (real_inv_pos (p2_tvsq p q) Htv) (p2_tvsq p q)).
    - apply (real_eq_trans
               _ (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1) real_one) _).
      + apply (RealSetoid.real_eq_mult_compat
                 (p2_kl2 p q Hp Hq Hp1 Hq1)
                 (real_mult (real_inv_pos (p2_tvsq p q) Htv)
                            (p2_tvsq p q))
                 (p2_kl2 p q Hp Hq Hp1 Hq1) real_one).  (* 续接席注：交叉腿序重排（9.1 适配税#2 同族） *)
        * apply real_eq_refl.
        * apply (real_eq_trans
                   _ (real_mult (p2_tvsq p q)
                                (real_inv_pos (p2_tvsq p q) Htv)) _).
          -- exact (real_mult_comm (real_inv_pos (p2_tvsq p q) Htv)
                      (p2_tvsq p q)).
          -- exact (real_inv_pos_correct (p2_tvsq p q) Htv).
      + exact (real_mult_one (p2_kl2 p q Hp Hq Hp1 Hq1)).  (* 续接席注：real_mult_one 实向 x·one==x，去多余 sym *) }
  apply (leb3_le_b_eq_l (p2_kl2 p q Hp Hq Hp1 Hq1)
           (real_mult (real_mult (p2_kl2 p q Hp Hq Hp1 Hq1)
                        (real_inv_pos (p2_tvsq p q) Htv))
                      (p2_tvsq p q))
           (p2_kl2 p q Hp Hq Hp1 Hq1)).
  - apply real_eq_sym. exact Hmain.
  - apply leb3_le_b_refl.
Qed.

(* ---- 8. 伴随 B 面收口：p≠q（Or 前提）⟹ 0 ≤_B KL（二点 Gibbs 收口） ---- *)
Theorem p2_kl2_nonneg_b : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hp1 : real_lt real_zero (p2_one_minus p))
  (Hq1 : real_lt real_zero (p2_one_minus q))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1).
Proof.
  intros p q Hp Hq Hp1 Hq1 Hne.
  exact (real_le_to_le_b real_zero (p2_kl2 p q Hp Hq Hp1 Hq1)
    (@inl (real_lt real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
          (real_eq real_zero (p2_kl2 p q Hp Hq Hp1 Hq1))
     (p2_kl2_pos p q Hp Hq Hp1 Hq1 Hne))).
Qed.

(* ---- 文尾假设审计 ---- *)
Print Assumptions p2_tvsq_sym.
Print Assumptions p2_gibbs_core_strict_pgtq.
Print Assumptions p2_kl2_pos.
Print Assumptions p2_c_pos.
Print Assumptions p2_pinsker_witness_b.
Print Assumptions p2_kl2_nonneg_b.
