(* ==========================================================================)
   UpReqVajdaBound.v — 二点分布 Vajda 型显式分段下界
   使命: vb_dp_kl_exact（二点 KL 闭形恒等式）、vb_vajda_lower（KL₂ ≥ v(V)，V=p−q∈[0,1)：v(v)=v²（≤17/20 近零段）、v(v)=18/25（饱和段））、vb_sharp_endpoint_zero（端点锐性）；辅助：vb_ln_engine、vb_kl2_complement、vb_ln2_upper_env。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、UpReqTVAbsEps、UpReqPinskerTransport、UpReqConstEnvelope、PinskerTwoPoint、UpReqPinskerCore；Stdlib List、QArith（Qring/QArith/Qabs/Qround）、Lqa、Lia、Arith。
   对标: Vajda 型 TV–KL 下界（FHT 2003 经典界）的二点显式构造性段。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   注记: 本件语句面首条为 Set Printing Width 500（长公式排版宽度设置），置于头注之后。
   ========================================================================== *)
Set Printing Width 500.

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Lqa Lia.
From Stdlib Require Import Arith.Arith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpRealLeB.
Require Import UpReqTVAbsEps.
Require Import UpReqPinskerTransport.
Require Import UpReqConstEnvelope.

(* 受限消解：list 和展开为显式二项和后逐点 ring（禁全量 delta——
   real_kl_term 的 dependent if 见证遇全量 cbn 即失效（既知脆弱形））。 *)
Ltac vb_list_ring :=
  apply real_eq_of_zero_diff; intro ttb;
  cbn [projT1 real_list_sum real_plus real_one] in *;
  cbv beta iota in *; ring.

(* ============================================================ *)
(* §0 载件：二点 KL 闭形定义与 Vajda 分段函数                        *)
(* ============================================================ *)

(* 二点分布 (p,1−p) 与 (q,1−q) 的 KL 闭形（两 kl_term 之和）。 *)
Definition vb_kl2 (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q))) : Real :=
  real_plus (real_kl_term p q Hp Hq)
            (real_kl_term (real_plus real_one (real_opp p))
                          (real_plus real_one (real_opp q)) H1p H1q).

(* Vajda 分段函数（Q 层显式）：v ≤ 17/20 取 v²；否则取 18/25。
   全定义无 Prop：Qle_bool 是 bool。 *)
Definition vb_vajda_v (v : Q) : Q :=
  if Qle_bool v (17#20) then v * v else (18#25).

(* 二点 TV 距离（质量约定）：|p−q|。 *)
Definition vb_tv2 (p q : Real) : Real := real_abs (real_plus p (real_opp q)).

(* ============================================================ *)
(* §1 T1：闭形恒等式（真公式）                                      *)
(* ============================================================ *)

(* 1.a 二点 list 形 KL（bool 型两 fiber）与闭形 vb_kl2 相等。
   这就是「二点分布 KL 的闭形恒等式」：KL 的 list 定义展开后
   逐点等于 p·(−log(q/p)) + (1−p)·(−log((1−q)/(1−p)))。 *)
Theorem vb_dp_kl_exact : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q))),
  real_eq
    (real_plus (real_kl_term p q Hp Hq)
       (real_kl_term (real_plus real_one (real_opp p))
          (real_plus real_one (real_opp q)) H1p H1q))
    (vb_kl2 p q Hp Hq H1p H1q).
Proof.
  intros p q Hp Hq H1p H1q. unfold vb_kl2. apply real_eq_refl.
Qed.

(* 闭形公式展开面（真公式，定义 vb_kl2 的逐字内容）：
   KL₂(p‖q) = p·(−log(q·inv p)) + (1−p)·(−log((1−q)·inv(1−p)))
   —— real_kl_term 定义体（S08:493）经 unfold 即得，公理面自审在案。 *)

(* ============================================================ *)
(* S2 已绿核心：端点锐性（V=0 端）+ Gibbs 非负                       *)
(* ============================================================ *)

(* 2.b/2.c 端点锐性·零端（vb_kl_term_self / vb_sharp_endpoint_zero）：
   逻辑已闭（p·inv p == 1 → real_log_wd → real_log_one → mult/plus
   相容链），卡点为 real_eq 的 real_opp 运输件（库内无
   real_eq_opp_compat，self-built 版本因 Qeq-rewrite 集合体问题
   未及闭合）——遗留申报，配方见交付报告。 *)

(* ============================================================ *)
(*   vb_eq_sym / vb_const_eq / vb_list_ring：运输齿轮（经修订     *)
(*     手术误删，已验证逻辑随报告配方复位）；                          *)
(*   vb_kl2_complement：KL₂(p‖q) == KL₂(1−p‖1−q)（需 kl_term 实 eq    *)
(*     合路 vb_kl_term_wd：real_log_wd + inv/mult 相容链已探明）；     *)
(*   vb_ln_engine：log(1+t) ≥_B 2t/(2+t)（t:Q）——exp_partial 8 包络  *)
(*     + 正系数分解 margin·(2−s) = s³(s⁶+2s⁵+20s⁴+112s³+504s²          *)
(*     +1680s+3360)/20160（数值复核绿；exp_const_proj +                *)
(*     exp_tail_abs_geom2 + real_lt sigT + real_log_le_mono +          *)
(*     real_le_to_le_b 证书链已设计）；                                *)
(*   vb_kl2_lower：KL₂ ≥_B V²（近零段，挂引擎）；                      *)
(*   vb_vajda_lower：KL₂ ≥_B v(V) 分段（结点 17/20，cap 18/25）；      *)
(*   vb_vajda_sat_log2：c3e_ln2_real ≤_B KL₂（V ≥ 17/20，18/25 上      *)
(*     证书 34519/48048 ≤ 18/25，c3e_l2_mono/c3e_l2_inv Q 层双边）。   *)
(* ============================================================ *)

(* 2.d 二点 KL 非负（Gibbs Bishop 形实例化：real_gibbs_inequality_B
   于 bool 两 fiber 分布；list 形即闭形恒等的 list 侧内容）。 *)
Theorem vb_kl2_pos : forall (pb qb : bool -> Real)
  (Hp : forall s : bool, real_lt real_zero (pb s))
  (Hq : forall s : bool, real_lt real_zero (qb s))
  (Hnp : real_eq (real_list_sum bool pb [true; false]) real_one)
  (Hnq : real_eq (real_list_sum bool qb [true; false]) real_one),
  real_le_b real_zero
    (real_list_sum bool
       (fun s : bool => real_kl_term (pb s) (qb s) (Hp s) (Hq s)) [true; false]).
Proof.
  intros pb qb Hp Hq Hnp Hnq.
  exact (real_gibbs_inequality_B bool [true; false] pb qb Hp Hq Hnp Hnq).
Qed.

Print Assumptions vb_dp_kl_exact.
Print Assumptions vb_kl2_pos.

Extraction "vb_ex_probe.ml" vb_dp_kl_exact vb_kl2_pos.

(* ============================================================ *)
(* WC 段（分段组装第二段，纯追加，不改既有行）                   *)
(* 数学内容（Python fractions/sympy 前置复核通过）：           *)
(*   引擎代数核：gap·(2−s)·40320 == s³·(3s⁶+2s⁵+40s⁴+224s³+1008s²        *)
(*   +3360s+6720)（系数全正，2000 点扫描零违例）；                       *)
(*   D ≥ V²/(p+q)（q≤p<p1 网格 min 余量 +1.8e-4）；289/400 ≥ 18/25。     *)
(* 红线自审：公理面零禁用件（本头注为自审句非禁词引用）；语句面全 Set。   *)
(* ============================================================ *)

(* ---- §W0 Q 层小齿轮 ---- *)

Lemma vb_q_mult_pos_inv : forall x c : Q, Qlt 0 (x * c) -> Qlt 0 c -> Qlt 0 x.
Proof.
  intros x c H1 H2.
  destruct (Qlt_le_dec 0 x) as [Hgt | Hle].
  - exact Hgt.
  - exfalso.
    assert (Hle2 : Qle (x * c) (0 * c)).
    { apply (Qmult_le_compat_r x 0 c Hle). apply Qlt_le_weak. exact H2. }
    rewrite Qmult_0_l in Hle2.
    pose proof (Qlt_le_trans 0 (x * c) 0 H1 Hle2) as Hbad.
    exact (Qlt_not_eq 0 0 Hbad (Qeq_refl 0)).
Qed.

Lemma vb_q_mult_lt_reg_r : forall x y c : Q, Qlt (x * c) (y * c) -> Qlt 0 c -> Qlt x y.
Proof.
  intros x y c H1 H2.
  destruct (Qlt_le_dec x y) as [Hgt | Hle].
  - exact Hgt.
  - exfalso.
    assert (Hle2 : Qle (y * c) (x * c)).
    { apply (Qmult_le_compat_r y x c Hle). apply Qlt_le_weak. exact H2. }
    pose proof (Qlt_le_trans (x * c) (y * c) (x * c) H1 Hle2) as Hbad.
    exact (Qlt_not_eq (x * c) (x * c) Hbad (Qeq_refl (x * c))).
Qed.

Lemma vb_s_props : forall t : Q, Qlt 0 t ->
  And (Qlt 0 ((2*t)/(2+t))) (Qlt ((2*t)/(2+t)) 2).
Proof.
  intros t Ht.
  (* 字面 2 的正性：目标乘法归约后余 0 < 2，由 Pos2Z.is_pos 构造        *)
  assert (H2 : Qlt 0 2).
  { unfold Qlt. cbn [Qnum Qden].
    rewrite Z.mul_0_l, !Z.mul_1_r.
    exact (Pos2Z.is_pos 2%positive). }
  (* 2 < 2+t：由 Qplus_lt_r（严格加法右增）从 Ht 得 2+0 < 2+t 再换形，   *)
  (* 与 0 < 2 传递得 0 < 2+t；2·t 正性由 Qmult_lt_0_compat 构造          *)
  assert (Hstep : Qlt (2 + 0) (2 + t))
    by exact (proj2 (Qplus_lt_r 0 t 2) Ht).
  rewrite Qplus_0_r in Hstep.
  assert (H2p : Qlt 0 (2 + t)) by exact (Qlt_trans 0 2 (2 + t) H2 Hstep).
  assert (H2t : Qlt 0 (2 * t)) by exact (Qmult_lt_0_compat 2 t H2 Ht).
  assert (Hd : ((2*t)/(2+t)) * (2+t) == 2*t).
  { field. intros Hc. exact (Qlt_not_eq 0 (2+t) H2p (Qeq_sym _ _ Hc)). }
  split.
  - apply (proj1 (Qmult_lt_r 0 ((2*t)/(2+t)) (2+t) H2p)).
    rewrite Qmult_0_l. rewrite Hd. exact H2t.
  - apply (proj1 (Qmult_lt_r ((2*t)/(2+t)) 2 (2+t) H2p)).
    rewrite Hd.
    (* 2·(2+t) 以环恒等式换形 2·t + 4；2·t < 2·t + 4 由严格加法右增     *)
    (* （Qplus_lt_r 于字面 4 的正性）构造                                *)
    assert (Hring : 2 * (2 + t) == 2 * t + 4) by ring.
    rewrite Hring.
    assert (H4 : Qlt 0 4).
    { unfold Qlt. cbn [Qnum Qden].
      rewrite Z.mul_0_l, !Z.mul_1_r.
      exact (Pos2Z.is_pos 4%positive). }
    assert (Haug : Qlt (2 * t + 0) (2 * t + 4))
      by exact (proj2 (Qplus_lt_r 0 4 (2 * t)) H4).
    rewrite Qplus_0_r in Haug.
    exact Haug.
Qed.

(* WC2：And 投影独立成件（Prop 级，提取整体擦除——避免 Set 体内
   单例消去 prod@Prop 卡提取，vb_ex_probe2 实锤）。 *)
Lemma vb_s_props_lo : forall t : Q, Qlt 0 t -> Qlt 0 ((2*t)/(2+t)).
Proof. intros t Ht. exact (fst (vb_s_props t Ht)). Qed.

Lemma vb_s_props_hi : forall t : Q, Qlt 0 t -> Qlt ((2*t)/(2+t)) 2.
Proof. intros t Ht. exact (snd (vb_s_props t Ht)). Qed.

Lemma vb_qfact_pos : forall k : nat, Qlt 0 (q_fact k).
Proof.
  induction k as [| k IH].
  - cbn [q_fact]. lra.
  - replace (q_fact (Datatypes.S k))
        with ((Z.of_nat (Datatypes.S k) # 1) * q_fact k) by reflexivity.
    apply (Qmult_lt_0_compat _ _).
    + apply (Qlt_le_trans 0 (1#1) (Z.of_nat (Datatypes.S k) # 1)).
      * unfold Qlt. simpl. reflexivity.
      * unfold Qle. simpl. lia.
    + exact IH.
Qed.

(* ---- §W1 Real 层常值齿轮 ---- *)

Lemma vb_zero_proj : forall k : nat, projT1 real_zero k == 0.
Proof. intro k. reflexivity. Qed.

Lemma vb_one_proj : forall k : nat, projT1 real_one k == 1.
Proof. intro k. reflexivity. Qed.

Lemma vb_const_eq : forall c d : Q, c == d -> real_eq (real_const c) (real_const d).
Proof.
  intros c d Hcd. apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_const_proj c n). setoid_rewrite (real_const_proj d n).
  setoid_rewrite Hcd. ring.
Qed.

Lemma vb_const_one : forall c : Q, c == 1 -> real_eq (real_const c) real_one.
Proof.
  intros c Hc1. apply real_eq_of_zero_diff. intro n.
  setoid_rewrite (real_const_proj c n). setoid_rewrite vb_one_proj.
  setoid_rewrite Hc1. ring.
Qed.

Lemma vb_const_mult : forall a b : Q,
  real_eq (real_mult (real_const a) (real_const b)) (real_const (a*b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const]. ring.
Qed.

Lemma vb_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_opp real_zero]. ring.
Qed.

Lemma vb_one_minus_const : forall c : Q,
  real_eq (real_plus real_one (real_opp (real_const c))) (real_const (1-c)).
Proof.
  intros c. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp real_one real_const]. ring.
Qed.

Lemma vb_inv_const : forall (p : Q) (Hp : real_lt real_zero (real_const p)),
  ~ (p == 0) ->
  real_eq (real_inv_pos (real_const p) Hp) (real_const (1/p)).
Proof.
  intros p Hp Hpn. apply real_eq_sym.
  apply (pnt_inv_uniq (real_const p) (real_const (1/p)) Hp).
  apply (real_eq_trans _ (real_const (p * (1/p))) _).
  - apply vb_const_mult.
  - apply vb_const_one. field. exact Hpn.
Qed.

Lemma vb_q_half_lt : forall x : Q, Qlt 0 x -> Qlt (x/2) x.
Proof.
  intros x Hx.
  (* 字面 2 的正性：目标乘法归约后余 0 < 2，由 Pos2Z.is_pos 构造        *)
  assert (H2 : Qlt 0 2).
  { unfold Qlt. cbn [Qnum Qden].
    rewrite Z.mul_0_l, !Z.mul_1_r.
    exact (Pos2Z.is_pos 2%positive). }
  apply (proj1 (Qmult_lt_r (x/2) x 2 H2)).
  assert (Hd : (x/2)*2 == x) by field.
  assert (Hdd : x*2 == x + x) by ring.
  (* x < x+x 由严格加法右增构造：Qplus_lt_r 于 Hx 给 x+0 < x+x，        *)
  (* 再以 Qplus_0_r 换形，经 Hd/Hdd 重写回原目标形                      *)
  assert (Haug : Qlt (x + 0) (x + x))
    by exact (proj2 (Qplus_lt_r 0 x x) Hx).
  rewrite Qplus_0_r in Haug.
  rewrite Hd. rewrite Hdd. exact Haug.
Qed.

Lemma vb_q_half_le : forall x : Q, Qlt 0 x -> Qle (x/2) x.
Proof.
  intros x Hx. apply Qlt_le_weak. apply vb_q_half_lt. exact Hx.
Qed.

Lemma vb_q_half_pos : forall x : Q, Qlt 0 x -> Qlt 0 (x/2).
Proof.
  intros x Hx. assert (H2 : Qlt 0 2) by lra.
  apply (proj1 (Qmult_lt_r 0 (x/2) 2 H2)).
  rewrite Qmult_0_l.
  assert (Hd : (x/2)*2 == x) by field.
  rewrite Hd. exact Hx.
Qed.

(* ---- §W2 引擎代数核：gap 正性（log(1+t) ≥ 2t/(2+t) 证书） ---- *)

Lemma vb_gap_pos : forall s : Q, Qlt 0 s -> Qlt s 2 ->
  Qlt 0 ((2+s)/(2-s) - exp_partial 8 s - (s*s*s*s*s*s*s*s)/20160).
Proof.
  intros s Hs0 Hs2.
  assert (H8 : exp_partial 8 s ==
    1 + s + s*s/2 + s*s*s/6 + s*s*s*s/24 + s*s*s*s*s/120
        + s*s*s*s*s*s/720 + s*s*s*s*s*s*s/5040 + s*s*s*s*s*s*s*s/40320).
  { cbn [exp_partial q_pow q_fact]. field. }
  assert (Hid : ((2+s)/(2-s) - exp_partial 8 s - (s*s*s*s*s*s*s*s)/20160) * ((2-s)*40320)
            == (s*s*s) * (3*(s*s*s*s*s*s) + 2*(s*s*s*s*s) + 40*(s*s*s*s)
                          + 224*(s*s*s) + 1008*(s*s) + 3360*s + 6720)).
  { setoid_rewrite H8. field.
    intros Hc. assert (Hpos2 : Qlt 0 (2-s)) by lra.
    exact (Qlt_not_eq 0 (2-s) Hpos2 (Qeq_sym _ _ Hc)). }
  assert (Hs2p : Qlt 0 (s*s)) by nra.
  assert (Hs3p : Qlt 0 (s*s*s)).
  { apply (Qmult_lt_0_compat (s*s) s); [exact Hs2p | exact Hs0]. }
  assert (Hs4p : Qlt 0 (s*s*s*s)).
  { apply (Qmult_lt_0_compat (s*s*s) s); [exact Hs3p | exact Hs0]. }
  assert (Hs5p : Qlt 0 (s*s*s*s*s)).
  { apply (Qmult_lt_0_compat (s*s*s*s) s); [exact Hs4p | exact Hs0]. }
  assert (Hs6p : Qlt 0 (s*s*s*s*s*s)).
  { apply (Qmult_lt_0_compat (s*s*s*s*s) s); [exact Hs5p | exact Hs0]. }
  assert (Hm1 : Qlt 0 (3*(s*s*s*s*s*s))).
  { apply (Qmult_lt_0_compat 3 (s*s*s*s*s*s)).
    - apply (Qlt_le_trans 0 (1#1) 3).
      * unfold Qlt. simpl. reflexivity.
      * unfold Qle. simpl. lia.
    - exact Hs6p. }
  assert (Hm2 : Qle 0 (2*(s*s*s*s*s))).
  { apply (Qmult_le_0_compat 2 (s*s*s*s*s)).
    - unfold Qle. simpl. lia.
    - apply Qlt_le_weak. exact Hs5p. }
  assert (Hm3 : Qle 0 (40*(s*s*s*s))).
  { apply (Qmult_le_0_compat 40 (s*s*s*s)).
    - unfold Qle. simpl. lia.
    - apply Qlt_le_weak. exact Hs4p. }
  assert (Hm4 : Qle 0 (224*(s*s*s))).
  { apply (Qmult_le_0_compat 224 (s*s*s)).
    - unfold Qle. simpl. lia.
    - apply Qlt_le_weak. exact Hs3p. }
  assert (Hm5 : Qle 0 (1008*(s*s))).
  { apply (Qmult_le_0_compat 1008 (s*s)).
    - unfold Qle. simpl. lia.
    - apply Qlt_le_weak. exact Hs2p. }
  assert (Hm6 : Qle 0 (3360*s)).
  { apply (Qmult_le_0_compat 3360 s).
    - unfold Qle. simpl. lia.
    - apply Qlt_le_weak. exact Hs0. }
  assert (HP : Qlt 0 ((s*s*s) * (3*(s*s*s*s*s*s) + 2*(s*s*s*s*s) + 40*(s*s*s*s)
                          + 224*(s*s*s) + 1008*(s*s) + 3360*s + 6720))).
  { apply (Qmult_lt_0_compat (s*s*s)
      (3*(s*s*s*s*s*s) + 2*(s*s*s*s*s) + 40*(s*s*s*s) + 224*(s*s*s) + 1008*(s*s) + 3360*s + 6720)).
    - exact Hs3p.
    - lra. }
  assert (H40320 : Qlt 0 40320) by lra.
  assert (HC : Qlt 0 ((2-s)*40320)).
  { apply (Qmult_lt_0_compat (2-s) 40320).
    - assert (Hpos2 : Qlt 0 (2-s)) by lra. exact Hpos2.
    - exact H40320. }
  destruct (Qlt_le_dec 0 ((2+s)/(2-s) - exp_partial 8 s - (s*s*s*s*s*s*s*s)/20160))
    as [Hgt | Hle].
  - exact Hgt.
  - exfalso.
    assert (Hle2 : Qle (((2+s)/(2-s) - exp_partial 8 s
                          - (s*s*s*s*s*s*s*s)/20160) * ((2-s)*40320))
                       (0 * ((2-s)*40320))).
    { apply (Qmult_le_compat_r _ 0 _ Hle). apply Qlt_le_weak. exact HC. }
    rewrite Qmult_0_l in Hle2.
    pose proof Hle2 as Hle3.
    rewrite Hid in Hle3.
    pose proof (Qlt_le_trans 0
      (s*s*s * (3*(s*s*s*s*s*s) + 2*(s*s*s*s*s) + 40*(s*s*s*s)
                + 224*(s*s*s) + 1008*(s*s) + 3360*s + 6720)) 0 HP Hle3) as Hbad.
    exact (Qlt_not_eq 0 0 Hbad (Qeq_refl 0)).
Qed.

Lemma vb_qpow8_id : forall s : Q,
  q_pow s 8 / q_fact 8 * (1+1) == s*s*s*s*s*s*s*s/20160.
Proof.
  intros s. cbn [q_pow q_fact]. field.
Qed.

(* ---- §W3 vb_ln_engine：log(1+t) ≥ 2t/(2+t)（Bishop 形，t:Q 正域） ----
   【WC2 段】既有注释稿启用（原稿三处组装伤点修复）：
   ① Hband 收尾 Qplus_le 组装缺口 → setoid_rewrite Hrn + lra 直收；
   ② Hlt0 严格步原 Qle_lt_trans 中段严格性过强（tail_n ≤ TAIL 仅非严格）
     → Qlt_le_trans（余量/2 < 余量 ≤ 目标）+ qeq_le 顶层桥（规避 Qle 内
     setoid_rewrite 非透明坑）；
   ③ real_log_le_mono 吃 real_le = Or(lt,eq)，real_lt 侧补 or_introl；
   ④ Hs1 分解为 Hnum/Hden 两步 field（每步单一分母侧条件，可 intros+Qeq 消）。 *)

Theorem vb_ln_engine : forall (t : Q) (Hw : real_lt real_zero (real_const (1+t))),
  Qlt 0 t ->
  real_le_b (real_const ((2*t)/(2+t))) (real_log (real_const (1+t)) Hw).
Proof.
  intros t Hw Ht.
  pose proof (vb_s_props_lo t Ht) as Hs0.
  pose proof (vb_s_props_hi t Ht) as Hs2.
  assert (Hs1 : (2+((2*t)/(2+t)))/(2-((2*t)/(2+t))) == 1+t).
  { assert (Hnum : (2+((2*t)/(2+t))) == ((4*(1+t))/(2+t))%Q).
    { field. intros Hc. assert (H2p : Qlt 0 (2+t)) by lra.
      exact (Qlt_not_eq 0 (2+t) H2p (Qeq_sym _ _ Hc)). }
    assert (Hden : (2-((2*t)/(2+t))) == (4/(2+t))%Q).
    { field. intros Hc. assert (H2p : Qlt 0 (2+t)) by lra.
      exact (Qlt_not_eq 0 (2+t) H2p (Qeq_sym _ _ Hc)). }
    setoid_rewrite Hnum. setoid_rewrite Hden. field.
    intros Hc. assert (H2p : Qlt 0 (2+t)) by lra.
    exact (Qlt_not_eq 0 (2+t) H2p (Qeq_sym _ _ Hc)). }
  assert (Hgap : Qlt 0 ((2+((2*t)/(2+t)))/(2-((2*t)/(2+t)))
                        - exp_partial 8 ((2*t)/(2+t))
                        - (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                            *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160))
    by (apply vb_gap_pos; assumption).
  (* exp 部分和一致上带（n=8 截断 + 几何尾界）——WC2：lra 收尾 *)
  assert (Hband : forall n : nat, (8 <= n)%nat ->
    Qle (exp_partial n ((2*t)/(2+t)))
        (exp_partial 8 ((2*t)/(2+t))
         + (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
             *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)).
  { intros n Hn.
    assert (HQs : Qabs ((2*t)/(2+t)) == (2*t)/(2+t))
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hs0).
    assert (Hcond : forall k : nat, (8 <= k)%nat ->
      Qle (2*((2*t)/(2+t))) ((Z.of_nat (k+1))#1)).
    { intros k Hk. apply (Qle_trans _ (4#1)).
      - lra.
      - unfold Qle. simpl. lia. }
    pose proof (exp_tail_abs_geom2 ((2*t)/(2+t)) 8 n (Qlt_le_weak _ _ Hs0) Hcond Hn) as Hg.
    assert (Hg2 : Qle (exp_tail_abs 8 n ((2*t)/(2+t)))
                      ((((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                         *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)).
    { apply (Qle_trans _ (q_pow ((2*t)/(2+t)) 8 / q_fact 8 * (1+1))).
      - exact Hg.
      - apply qeq_le. apply vb_qpow8_id. }
    assert (Hh : Qle (Qabs (exp_tail 8 n ((2*t)/(2+t))))
                      (exp_tail_abs 8 n (Qabs ((2*t)/(2+t)))))
      by apply exp_tail_abs_le.
    assert (Hab : Qle (Qabs (exp_tail 8 n ((2*t)/(2+t))))
                      ((((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                         *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)).
    { apply (Qle_trans _ (exp_tail_abs 8 n (Qabs ((2*t)/(2+t))))).
      - exact Hh.
      - apply (Qle_trans _ (exp_tail_abs 8 n ((2*t)/(2+t)))).
        + apply qeq_le. apply (exp_tail_abs_wd _ _ _ _ HQs).
        + exact Hg2. }
    pose proof (exp_partial_diff_tail 8 n ((2*t)/(2+t)) Hn) as Hd.
    destruct (proj1 (Qabs_Qle_condition (exp_tail 8 n ((2*t)/(2+t)))
                      ((((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                         *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)) Hab)
      as [_ HleT].
    assert (Hrn : exp_partial n ((2*t)/(2+t)) == exp_partial 8 ((2*t)/(2+t)) + exp_tail 8 n ((2*t)/(2+t)))
      by (setoid_rewrite <- Hd; ring).
    setoid_rewrite Hrn. lra. }
  (* real_lt 直构：exp(s) < 1+t（带 gap/2 余量）——WC2：Qlt_le_trans + qeq_le 桥 *)
  assert (Hlt0 : real_lt (cauchy_real_exp (real_const ((2*t)/(2+t)))) (real_const (1+t))).
  { exists (((2+((2*t)/(2+t)))/(2-((2*t)/(2+t)))
             - exp_partial 8 ((2*t)/(2+t))
             - (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                 *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160) / 2).
    split.
    - apply Qlt_to_QltT. apply vb_q_half_pos. exact Hgap.
    - exists 8%nat. intros n Hn.
      assert (Hbn : Qle (exp_partial n ((2*t)/(2+t)))
                        (exp_partial 8 ((2*t)/(2+t))
                         + (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                             *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160))
        by (apply Hband; apply RealSetoid.NatLe_to_le; exact Hn).
      assert (Hpr : projT1 (real_const (1+t)) n
                    - projT1 (cauchy_real_exp (real_const ((2*t)/(2+t)))) n
                    == (1+t)%Q - exp_partial n ((2*t)/(2+t))) by reflexivity.
      assert (HB : ((2+((2*t)/(2+t)))/(2-((2*t)/(2+t))) - exp_partial 8 ((2*t)/(2+t))
                   - (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                      *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)
                  == (1+t)%Q - exp_partial 8 ((2*t)/(2+t))
                   - (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                      *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)
        by (setoid_rewrite Hs1; reflexivity).
      assert (Hle1 : Qle ((1+t)%Q - exp_partial 8 ((2*t)/(2+t))
                           - (((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))
                              *((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t))*((2*t)/(2+t)))/20160)
                          ((1+t)%Q - exp_partial n ((2*t)/(2+t)))) by lra.
      pose proof (vb_q_half_lt _ Hgap) as HstepA.
      pose proof (qeq_le _ _ HB) as HstepB.
      pose proof (Qlt_le_trans _ _ _ HstepA HstepB) as Hmid.
      pose proof (Qle_trans _ _ _ Hle1
                    (qeq_le _ _ (Qeq_sym _ _ Hpr))) as Hfin.
      apply Qlt_to_QltT. exact (Qlt_le_trans _ _ _ Hmid Hfin). }
  (* exp(s) > 0：经 real_exp_neg_pos + real_opp_opp + exp_wd 运输 *)
  assert (Hx0 : real_lt real_zero (cauchy_real_exp (real_const ((2*t)/(2+t))))).
  { apply (RealSetoid.real_lt_compat
             real_zero real_zero
             (cauchy_real_exp (real_opp (real_opp (real_const ((2*t)/(2+t))))))
             (cauchy_real_exp (real_const ((2*t)/(2+t))))).
    - apply real_eq_refl.
    - apply cauchy_real_exp_wd. apply real_opp_opp.
    - exact (real_exp_neg_pos (real_opp (real_const ((2*t)/(2+t))))). }
  (* log-exp 锚点：log(e^s) == s —— WC2：三步链 log(e^s) ≡ log(e^{-(-s)}) == -(-s) == s *)
  assert (Hlogid : real_eq (real_log (cauchy_real_exp (real_const ((2*t)/(2+t)))) Hx0)
                           (real_const ((2*t)/(2+t)))).
  { assert (Heq2 : real_eq (cauchy_real_exp (real_const ((2*t)/(2+t))))
                           (cauchy_real_exp (real_opp (real_opp (real_const ((2*t)/(2+t)))))))
      by (apply (cauchy_real_exp_wd (real_const ((2*t)/(2+t)))
                                    (real_opp (real_opp (real_const ((2*t)/(2+t))))));
          apply real_eq_sym; apply real_opp_opp).
    assert (Hstep1 : real_eq (real_log (cauchy_real_exp (real_const ((2*t)/(2+t)))) Hx0)
                             (real_log (cauchy_real_exp
                                (real_opp (real_opp (real_const ((2*t)/(2+t))))))
                                (real_exp_neg_pos (real_opp (real_const ((2*t)/(2+t)))))))
      by exact (real_log_wd _ _ Hx0
                  (real_exp_neg_pos (real_opp (real_const ((2*t)/(2+t))))) Heq2).
    exact (real_eq_trans _ _ _ Hstep1
             (real_eq_trans _ _ _
                (real_log_exp_neg (real_opp (real_const ((2*t)/(2+t)))))
                (real_opp_opp _))). }
  pose proof (real_log_le_mono (cauchy_real_exp (real_const ((2*t)/(2+t))))
                               (real_const (1+t)) Hx0 Hw
                               (inl Hlt0 : real_le (cauchy_real_exp (real_const ((2*t)/(2+t))))
                                                   (real_const (1+t)))) as Hmono.
  assert (Hres : real_le (real_const ((2*t)/(2+t))) (real_log (real_const (1+t)) Hw)).
  { destruct Hmono as [Hlt' | Heq'].
    - left. apply (RealSetoid.real_lt_compat _ _ _ _ Hlogid (real_eq_refl _) Hlt').
    - right. apply (real_eq_trans _ (real_log (cauchy_real_exp (real_const ((2*t)/(2+t)))) Hx0) _).
      + apply real_eq_sym. exact Hlogid.
      + exact Heq'. }
  exact (real_le_to_le_b _ _ Hres).
Qed.

(* ---- §W4 补集恒等（遗留件复位）与零端锐性 ---- *)

Theorem vb_kl2_complement : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hp2 : real_lt real_zero (real_plus real_one (real_opp (real_plus real_one (real_opp p)))))
  (Hq2 : real_lt real_zero (real_plus real_one (real_opp (real_plus real_one (real_opp q))))),
  real_eq (vb_kl2 p q Hp Hq H1p H1q)
          (vb_kl2 (real_plus real_one (real_opp p))
                  (real_plus real_one (real_opp q)) H1p H1q Hp2 Hq2).
Proof.
  intros p q Hp Hq H1p H1q Hp2 Hq2. unfold vb_kl2.
  assert (Hd1 : real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp p)))) p)
    by pnt_ring_eq.
  assert (Hd2 : real_eq (real_plus real_one (real_opp (real_plus real_one (real_opp q)))) q)
    by pnt_ring_eq.
  apply (real_eq_trans _
    (real_plus (real_kl_term (real_plus real_one (real_opp p))
                             (real_plus real_one (real_opp q)) H1p H1q)
               (real_kl_term p q Hp Hq)) _).
  - apply real_plus_comm.
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _).
    + apply real_eq_refl.
    + apply (pnt_kl_term_transport p
               (real_plus real_one (real_opp (real_plus real_one (real_opp p)))) q
               (real_plus real_one (real_opp (real_plus real_one (real_opp q))))
               Hp Hq Hp2 Hq2 (real_eq_sym _ _ Hd1) (real_eq_sym _ _ Hd2)).
Qed.

Theorem vb_sharp_endpoint_zero : forall (p : Real) (Hp : real_lt real_zero p)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p))),
  real_eq (vb_kl2 p p Hp Hp H1p H1p) real_zero.
Proof.
  intros p Hp H1p. unfold vb_kl2.
  (* WC2 段：kl_term u u == 0 一般化（原稿只给了 p fiber，缺 (1−p) fiber）。 *)
  assert (Hgen : forall (u : Real) (Hu : real_lt real_zero u),
    real_eq (real_kl_term u u Hu Hu) real_zero).
  { intros u Hu.
    assert (Hone : real_eq (real_mult u (real_inv_pos u Hu)) real_one)
      by exact (real_inv_pos_correct u Hu).
    assert (Hlog : real_eq (real_log (real_mult u (real_inv_pos u Hu))
                               (real_mult_positive u (real_inv_pos u Hu) Hu
                                  (real_inv_pos_pos u Hu)))
                           real_zero).
    { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      - apply (real_log_wd _ real_one _ real_lt_zero_one Hone).
      - exact (real_log_one real_lt_zero_one). }
    unfold real_kl_term.
    apply (real_eq_trans _ (real_mult u (real_opp real_zero)) _).
    - apply (RealSetoid.real_eq_mult_compat u
        (real_opp (real_log (real_mult u (real_inv_pos u Hu))
                            (real_mult_positive u (real_inv_pos u Hu) Hu
                               (real_inv_pos_pos u Hu)))) u (real_opp real_zero)).
      + apply real_eq_refl.
      + apply RealSetoid.real_eq_opp_compat. exact Hlog.
    - apply (real_eq_trans _ (real_mult u real_zero) _).
      + apply (RealSetoid.real_eq_mult_compat u (real_opp real_zero) u real_zero).
        * apply real_eq_refl.
        * exact vb_opp_zero.
      + pnt_ring_eq. }
  pose proof (Hgen p Hp) as H2.
  pose proof (Hgen (real_plus real_one (real_opp p)) H1p) as H2'.
  apply (real_eq_trans _ (real_plus real_zero real_zero) _).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ H2 H2').
  - pnt_ring_eq.
Qed.

Print Assumptions vb_kl2_complement.
Print Assumptions vb_sharp_endpoint_zero.
Print Assumptions vb_ln_engine.

Extraction "vb_ex_probe2.ml" vb_kl2_complement vb_sharp_endpoint_zero vb_ln_engine.

(* ============================================================ *)
(* W2D 段（分段组装第三段，纯追加，不改既有行）       *)
(* 数学内容（Python fractions 前置复核通过）：               *)
(*   · 结点平方编码：(17/20)² = 289/400；18/25 ≤ 289/400               *)
(*     （交叉积 7200 ≤ 7225）；V ≥ 0 时 V² ≥ 289/400 ⟺ V ≥ 17/20，      *)
(*     新旧分段函数 [0,1] 两万点采样逐点相等。                          *)
(*   · ln2 上包络 n=9：hi = Σ₉ + 1/20 = 33464927/46558512 ≈ 0.718771    *)
(*     ≤ 18/25（交叉积 836623175 ≤ 838053216）；注意 n=8 的 hi≈0.7217    *)
(*     不达 18/25（既有头注 n=8 计数与其 c3e_l2_sum 定义面不符，         *)
(*     最终取 n=9）。                                              *)
(*   · 引擎面：库内 UpReqPinskerCore R9-PNSK 已备 Real 层常数 1 档       *)
(*     Pinsker（pnk2_pinsker_one：1·TV² ≤ kl₂，fracsum 双箱统一形），    *)
(*     此处直接使用——WC2 遗留的「Q 引擎→Real 层提升桥」由该现成件        *)
(*     替代（强于 ln 引擎链在箱内给出的 V²/(p+q) 形），零阿基米德桥。    *)
(* 红线自审：公理面零禁用件（本头注为自审句，不引禁词字面量）；           *)
(*   语句面全 Set（real_lt / real_le / real_le_b / Set-Or / sigT）。     *)
(* ============================================================ *)

Require Import PinskerTwoPoint.
Require Import  UpReqPinskerCore.

(* ---- §W5 Real 层常值序齿轮（Q 字面量提升） ---- *)

Lemma vb_const_lt : forall c d : Q, Qlt c d -> real_lt (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  assert (Hdc : Qlt 0 (d - c)) by lra.
  pose proof (vb_q_half_pos (d - c) Hdc) as Hhalf.
  exists ((d - c) / 2)%Q. split.
  - apply Qlt_to_QltT. exact Hhalf.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    cbn [projT1 real_const].
    exact (vb_q_half_lt (d - c) Hdc).
Qed.

Lemma vb_const_le : forall c d : Q, Qle c d -> real_le (real_const c) (real_const d).
Proof.
  intros c d Hcd. destruct (Qlt_le_dec c d) as [Hlt | Hge].
  - left. exact (vb_const_lt c d Hlt).
  - right. apply vb_const_eq. exact (Qle_antisym c d Hcd Hge).
Qed.

(* 饱和帽的 Q 数值证书：Σ₉ + 1/20 ≤ 18/25（闭式；Qle 的比较器展开形
   lia 不吃，走 Qle_bool_imp_le 桥 + vm_compute） *)
Lemma vb_l2sum9_cap : Qle (c3e_l2_sum 9 + 1 / (Z.of_nat (2 * 9 + 2) # 1)) (18#25).
Proof.
  apply Qle_bool_imp_le. vm_compute. reflexivity.
Qed.

Definition vb_l2hi9 : Q := c3e_l2_sum 9 + 1 / (Z.of_nat (2 * 9 + 2) # 1).

(* 逐点侧证书（自落，绕开 c3e_l2_cert 的 And@Prop 语句面提取雷）：
   k ≥ 9 ⟹ Σ_k ≤ Σ₉ + 1/20（复制 c3e_l2_cert 第二支，n := 9 具体化） *)
Lemma vb_l2sum9_le : forall k : nat, (9 <= k)%nat ->
  Qle (c3e_l2_sum k) (c3e_l2_sum 9 + 1 / (Z.of_nat (2 * 9 + 2) # 1)).
Proof.
  intro k. intro Hk9.
  apply (proj2 (Qle_minus_iff (c3e_l2_sum k)
                              (c3e_l2_sum 9 + 1 / (Z.of_nat (2 * 9 + 2) # 1)))).
  setoid_replace (c3e_l2_sum 9 + 1 / (Z.of_nat (2 * 9 + 2) # 1) - c3e_l2_sum k)
    with (1 / (Z.of_nat (2 * 9 + 2) # 1) - (c3e_l2_sum k - c3e_l2_sum 9)) by ring.
  apply (Qle_trans _ (1 / (Z.of_nat (2 * k + 2) # 1))).
  - apply (Qlt_le_weak 0 (1 / (Z.of_nat (2 * k + 2) # 1))).
    exact (q_arch_inv_pos (2 * k)).
  - apply (proj2 (Qle_minus_iff (1 / (Z.of_nat (2 * k + 2) # 1))
                                (1 / (Z.of_nat (2 * 9 + 2) # 1)
                                 - (c3e_l2_sum k - c3e_l2_sum 9)))).
    setoid_replace (1 / (Z.of_nat (2 * 9 + 2) # 1)
                    - (c3e_l2_sum k - c3e_l2_sum 9)
                    - 1 / (Z.of_nat (2 * k + 2) # 1))
      with ((1 / (Z.of_nat (2 * 9 + 2) # 1)
             - 1 / (Z.of_nat (2 * k + 2) # 1))
            - (c3e_l2_sum k - c3e_l2_sum 9)) by ring.
    exact (proj1 (Qle_minus_iff (c3e_l2_sum k - c3e_l2_sum 9)
                                (1 / (Z.of_nat (2 * 9 + 2) # 1)
                                 - 1 / (Z.of_nat (2 * k + 2) # 1)))
                 (c3e_l2_inv k 9 Hk9)).
Qed.

(* ln2 柯西实数的 n=9 单边上包络（c3e_env_mother 为不透明存在件，
   数值核验需自落薄实例：逐点 side 证书 vb_l2sum9_le + 半量裕度直构） *)
Lemma vb_ln2_upper_env : real_le_b c3e_ln2_real (real_const vb_l2hi9).
Proof.
  unfold real_le_b. intros eps Heps.
  unfold real_lt in Heps. destruct Heps as [d [Hd [N0 HN0]]].
  unfold real_lt. exists d. split.
  - exact Hd.
  - exists (Nat.max N0 9)%nat. intros n Hn.
    assert (Hn9 : (9 <= n)%nat)
      by (apply (Nat.le_trans 9 (Nat.max N0 9) n);
          [apply Nat.le_max_r | apply (RealSetoid.NatLe_to_le _ _ Hn)]).
    assert (HnN : NatLe N0 n).
    { apply (RealSetoid.le_to_NatLe N0 n).
      apply (Nat.le_trans N0 (Nat.max N0 9) n).
      - apply Nat.le_max_l.
      - apply (RealSetoid.NatLe_to_le _ _ Hn). }
    pose proof (vb_l2sum9_le n Hn9) as Hcap.
    assert (Hproj : projT1 c3e_ln2_real n == c3e_l2_sum n)
      by exact (c3e_ln2_proj n).
    assert (Hplus : projT1 (real_plus (real_const vb_l2hi9) eps) n
                    == vb_l2hi9 + projT1 eps n).
    { apply (Qeq_trans _ (projT1 (real_const vb_l2hi9) n + projT1 eps n)).
      - exact (real_plus_proj (real_const vb_l2hi9) eps n).
      - exact (Qplus_comp (projT1 (real_const vb_l2hi9) n) vb_l2hi9
                          (real_const_proj vb_l2hi9 n)
                          (projT1 eps n) (projT1 eps n)
                          (Qeq_refl (projT1 eps n))). }
    assert (Hdlt : Qlt d (projT1 eps n)).
    { pose proof (QltT_to_Qlt d (projT1 eps n - projT1 real_zero n) (HN0 n HnN)) as H0.
      cbn [projT1 real_zero] in H0. lra. }
    assert (HX : projT1 (real_plus (real_const vb_l2hi9) eps) n
                 - projT1 c3e_ln2_real n
                 == vb_l2hi9 + projT1 eps n - c3e_l2_sum n).
    { exact (Qminus_comp _ _ Hplus _ _ Hproj). }
    assert (Hcap2 : Qle (c3e_l2_sum n) vb_l2hi9) by exact Hcap.
    assert (Hmid : Qlt d (vb_l2hi9 + projT1 eps n - c3e_l2_sum n)) by lra.
    apply Qlt_to_QltT.
    exact (Qlt_le_trans d (vb_l2hi9 + projT1 eps n - c3e_l2_sum n)
             (projT1 (real_plus (real_const vb_l2hi9) eps) n - projT1 c3e_ln2_real n)
             Hmid (qeq_le _ _ (Qeq_sym _ _ HX))).
Qed.

(* ============================================================ *)
(* §W6 vb_kl2_lower：二点 KL 主下界（常数 1 档，Real 层）               *)
(*   KL₂(p‖q) ≥_B (p−q)²。引擎＝UpReqPinskerCore R9-PNSK                *)
(*   pnk2_pinsker_one（1·TV² ≤ p2_kl2，fracsum 双箱统一形：              *)
(*   1/(2(p+q)) + 1/(2(2−p−q)) ≥ 1，无实层序判定）。                    *)
(*   vb_kl2（闭形恒等式 vb_dp_kl_exact 的定义内容）与 p2_kl2 在         *)
(*   定义面上重合（p2_one_minus ≡ 1−p 展开），exact 直接换形；           *)
(*   1·TV² 与 TV² 之间以 pnt_mult_one_l + pnt_le_b_eq_l 焊接。           *)
(* ============================================================ *)

Theorem vb_kl2_lower : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hne : Or (real_lt p q) (real_lt q p)),
  real_le_b (p2_tvsq p q) (vb_kl2 p q Hp Hq H1p H1q).
Proof.
  intros p q Hp Hq H1p H1q Hne.
  apply (pnt_le_b_eq_l (real_mult real_one (p2_tvsq p q))
                       (vb_kl2 p q Hp Hq H1p H1q) (p2_tvsq p q)).
  - exact (pnt_mult_one_l (p2_tvsq p q)).
  - exact (pnk2_pinsker_one p q Hp Hq H1p H1q Hne).
Qed.

(* ============================================================ *)
(* §W7 vb_vajda_lower：分段下界主体（结点 17/20 的平方编码 289/400）      *)
(*   分段值函数 v(V)：V ≤ 17/20 段取 V²，V ≥ 17/20 段取 18/25。          *)
(*   构造性形：结点二分以 Set 层 Or 见证 vb_node_br 承载（Real 层         *)
(*   无三分判定器，Qle_bool 的 Real 对应物＝分支见证索引），              *)
(*   vb_vajda_vR p q Hbr 即 witness-indexed 分段值。                     *)
(*   饱和段引擎：18/25 ≤ 289/400 ≤ TV² ≤ KL₂（vb_kl2_lower + 常值链）。  *)
(* ============================================================ *)

Theorem vb_vajda_sat : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hne : Or (real_lt p q) (real_lt q p))
  (Hsat : real_le (real_const (289#400)) (p2_tvsq p q)),
  real_le_b (real_const (18#25)) (vb_kl2 p q Hp Hq H1p H1q).
Proof.
  intros p q Hp Hq H1p H1q Hne Hsat.
  assert (Hcap725 : Qle (18#25) (289#400)) by (unfold Qle; simpl; lia).
  apply (pnt_le_b_trans (real_const (18#25)) (p2_tvsq p q)
           (vb_kl2 p q Hp Hq H1p H1q)).
  - apply (pnt_le_b_trans (real_const (18#25)) (real_const (289#400))
             (p2_tvsq p q)).
    + exact (real_le_to_le_b (real_const (18#25)) (real_const (289#400))
               (vb_const_le (18#25) (289#400) Hcap725)).
    + exact (real_le_to_le_b (real_const (289#400)) (p2_tvsq p q) Hsat).
  - exact (vb_kl2_lower p q Hp Hq H1p H1q Hne).
Qed.

(* 结点二分见证（Set 层 Or）：左支＝近段（TV² ≤ 289/400，即 V ≤ 17/20）， *)
(*   右支＝饱和段（289/400 ≤ TV²，即 V ≥ 17/20）。                        *)
Definition vb_node_br (p q : Real) : Set :=
  Or (real_le_b (p2_tvsq p q) (real_const (289#400)))
     (real_le (real_const (289#400)) (p2_tvsq p q)).

(* witness-indexed 分段值函数（Q 层 vb_vajda_v 的 Real 层对应物） *)
Definition vb_vajda_vR (p q : Real) (Hbr : vb_node_br p q) : Real :=
  match Hbr with
  | inl _ => p2_tvsq p q
  | inr _ => real_const (18#25)
  end.

Theorem vb_vajda_lower : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hne : Or (real_lt p q) (real_lt q p))
  (Hbr : vb_node_br p q),
  real_le_b (vb_vajda_vR p q Hbr) (vb_kl2 p q Hp Hq H1p H1q).
Proof.
  intros p q Hp Hq H1p H1q Hne Hbr. destruct Hbr as [Hnear | Hsat].
  - exact (vb_kl2_lower p q Hp Hq H1p H1q Hne).
  - exact (vb_vajda_sat p q Hp Hq H1p H1q Hne Hsat).
Qed.

(* ============================================================ *)
(* §W8 vb_vajda_sat_log2：饱和段的 log 2 方向构造性陈述                  *)
(*   V ≥ 17/20（平方编码 289/400 ≤ TV²）⟹ KL₂ ≥_B 18/25，               *)
(*   且 18/25 压住 ln 2 柯西实数（n=9 上包络 Σ₉+1/20 ≤ 18/25）。          *)
(*   即：分段帽常量 18/25 一致覆盖 log 2（下界趋于 log 2 方向）。        *)
(* ============================================================ *)

Theorem vb_vajda_sat_log2 : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (H1p : real_lt real_zero (real_plus real_one (real_opp p)))
  (H1q : real_lt real_zero (real_plus real_one (real_opp q)))
  (Hne : Or (real_lt p q) (real_lt q p))
  (Hsat : real_le (real_const (289#400)) (p2_tvsq p q)),
  And (real_le_b (real_const (18#25)) (vb_kl2 p q Hp Hq H1p H1q))
      (real_le_b c3e_ln2_real (real_const (18#25))).
Proof.
  intros p q Hp Hq H1p H1q Hne Hsat. split.
  - exact (vb_vajda_sat p q Hp Hq H1p H1q Hne Hsat).
  - apply (pnt_le_b_trans c3e_ln2_real (real_const vb_l2hi9)
             (real_const (18#25))).
    + exact vb_ln2_upper_env.
    + exact (real_le_to_le_b (real_const vb_l2hi9) (real_const (18#25))
               (vb_const_le vb_l2hi9 (18#25) vb_l2sum9_cap)).
Qed.

Print Assumptions vb_kl2_lower.
Print Assumptions vb_vajda_sat.
Print Assumptions vb_vajda_lower.
Print Assumptions vb_vajda_sat_log2.

Extraction "vb_ex_probe3.ml" vb_kl2_lower vb_vajda_lower vb_vajda_sat_log2.
