(* ============================================================ *)
(* ToyR 玩具证替换件 —— T250 台账席 战役包K（tier2 头批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   tw_ZT_le_NEU（原 L1110，5 句玩具证）                                 *)
(*   tw_ZT_ge_NEL（原 L1103，5 句玩具证）                                 *)
(*   tw_lt_half_opp（原 L354，4 句玩具证）                                *)
(*   tw_Q_min_r（原 L263，3 句玩具证）                                    *)
(*   tw_Q_min_l（原 L258，3 句玩具证）                                    *)
(*   tw_le_eq_l（原 L61，2 句玩具证）                                     *)
(*   tw_le_eq_r（原 L54，2 句玩具证）                                     *)
(*   tw_eq_le（原 L48，2 句玩具证）                                       *)
(*   tw_lt_le（原 L42，2 句玩具证）                                       *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T321 恒等守恒更正注记】2026-09-22 包AW九 台账席（恒等头注更正全量第一批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 9 参数位证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 参数位＋恒等守恒 9 参数位；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321 台账。                        *)
(* 附记：T277 判级全文恒等；包K 全量第一批整批直推（T317 六·1 方案①）                           *)
(* ============================================================ *)

(* ============================================================ *)
(* UpTempWindow.v *)
(* *)
(* 目的： 温度窗口面：硬注意力极限的窗口载体重建。 *)
(* 主件： tw_wT / tv_unif 窗口核与 tw_ZT_pos、tw_states_len_pos 前提族。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 纯构造性、零公理面/承认件/弃证/经典逻辑；词表非空与温度直径正为显式前提。 *)
(* ============================================================ *)

(* ============================================================ *)

(*   高温趋近均匀分布（量词翻转的真极限定理，sigT 见证）。       *)
(*                                                              *)
(*   主定理 temp_window_T_infty：                                *)
(*     ∀eps > 0, ∃T₂ > 0, ∀T > T₂, TV(w_T, U) ≤ eps             *)
(*                                                              *)
(*   设定：list 离散状态世界（副本 AttnHardLimit）：             *)
(*     states : list S 非空；logits z : S -> Real 一致界         *)
(*     |z(s)| ≤ Δ（Δ > 0）；w_T(x) = e^{z(x)/T}/Z(T)；           *)
(*     uniform(x) = 1/N（N = |states|）；TV = Σ|w_T − 1/N|。     *)
(*                                                              *)
(*   核心不等式（Doeblin 均匀版）：                              *)
(*     e^{−2Δ/T}/N ≤ w_T(x) ≤ e^{+2Δ/T}/N                       *)
(*   ⟹ 逐点 |w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)/N                   *)
(*   ⟹ TV ≤ e^{2Δ/T} − 1。                                      *)

(*     T > T₂ ⟹ 2Δ/T ≤ cw_log(1+eps) ⟹ e^{2Δ/T} ≤ 1+eps。      *)
(*                                                              *)
(*   纪律：纯构造性、零 公理/承认件/弃证/经典逻辑；         *)
(*         语句全 Set 层（sigT/And/Or）；全部 Qed。              *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax QArith.QOrderedType.

(* ============================================================ *)
(* 0. 通用桥（Real 层，Section 外，全局可复用）                 *)
(* ============================================================ *)

(* lt ⟹ le（real_le 的 Or 编码左支） *)
Lemma tw_lt_le : forall a b : Real, real_lt a b -> real_le a b.
Proof.
  intros a b H.
  exact (inl H).
Qed.

(* eq ⟹ le（Or 编码右支） *)
Lemma tw_eq_le : forall a b : Real, real_eq a b -> real_le a b.
Proof.
  intros a b H.
  exact (inr H).
Qed.

(* a ≤ b 且 b == c ⟹ a ≤ c *)
Lemma tw_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hab Hbc.
  exact (real_le_trans a b c Hab (inr Hbc)).
Qed.

(* a ≤ b 且 a == c ⟹ c ≤ b *)
Lemma tw_le_eq_l : forall a b c : Real,
  real_le a b -> real_eq a c -> real_le c b.
Proof.
  intros a b c Hab Hac.
  exact (real_le_trans c a b (inr (real_eq_sym a c Hac)) Hab).
Qed.

(* 0 ≤ b ⟹ a ≤ a + b *)
Lemma tw_le_plus_nonneg_r : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (RealSetoid.real_le_id_l a (real_plus a real_zero) (real_plus a b)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_le_plus_compat; [apply real_le_refl | exact Hb].
Qed.

(* 0 < y ⟹ −y < 0（见证不变，逐点 0−(−y_k) == y_k） *)
Lemma tw_lt_opp_l : forall y : Real,
  real_lt real_zero y -> real_lt (real_opp y) real_zero.
Proof.
  intros y H. destruct H as [e [He [N HN]]].
  destruct y as [u Hu].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    cbn [projT1 real_opp real_zero].
    assert (Hy : Qlt e (u n - 0)) by (apply QltT_to_Qlt; exact (HN n Hn)).
    assert (Hz : u n - 0 == u n) by ring.
    rewrite Hz in Hy.
    apply Qlt_to_QltT.
    assert (Hz2 : 0 - - u n == u n) by ring.
    rewrite Hz2.
    exact Hy.
Qed.

(* ============================================================ *)
(* 1. 纯环原子恒等式族（real_eq_of_zero_diff 逐点 ring，N = 0） *)
(*   惯例：原子以 Real 变量抽象，destruct 后 simpl 全消 projT1。 *)
(* ============================================================ *)

(* 0 + x == x（zero 在左） *)
Lemma tw_ring_zero_plus : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (d+d)·e == d·e + d·e *)
Lemma tw_ring_dd_mult : forall d e : Real,
  real_eq (real_mult (real_plus d d) e)
          (real_plus (real_mult d e) (real_mult d e)).
Proof.
  intros d e. destruct d as [u Hu]. destruct e as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x+y)·z == x·z + y·z（右分配） *)
Lemma tw_ring_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z)
          (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x·y + (−y) == (x + (−1))·y *)
Lemma tw_ring_sub_mult : forall x y : Real,
  real_eq (real_plus (real_mult x y) (real_opp y))
          (real_mult (real_plus x (real_opp real_one)) y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* y + −(x·y) == (1 + −x)·y *)
Lemma tw_ring_sub_mult_l : forall x y : Real,
  real_eq (real_plus y (real_opp (real_mult x y)))
          (real_mult (real_plus real_one (real_opp x)) y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (1+e) + (−1) == e *)
Lemma tw_ring_one_eps_minus : forall e : Real,
  real_eq (real_plus (real_plus real_one e) (real_opp real_one)) e.
Proof.
  intros e. destruct e as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* T₂·L == 2Δ·(L·invL) + L，其中 T₂ = 2Δ·invL + 1（翻转链换形） *)
Lemma tw_ring_t2 : forall d l il : Real,
  real_eq (real_mult l (real_plus (real_mult (real_plus d d) il) real_one))
          (real_plus (real_mult (real_plus d d) (real_mult l il)) l).
Proof.
  intros d l il. destruct d as [u Hu]. destruct l as [v Hv]. destruct il as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (2Δ + L)·invT == 2Δ·invT + L·invT *)
Lemma tw_ring_ddl : forall d l it : Real,
  real_eq (real_mult (real_plus (real_plus d d) l) it)
          (real_plus (real_mult (real_plus d d) it) (real_mult l it)).
Proof.
  intros d l it. destruct d as [u Hu]. destruct l as [v Hv]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* u + −(2u) == −u（u = Δ/T，2u = EF） *)
Lemma tw_ring_u_plus_negEF : forall d it : Real,
  real_eq (real_plus (real_mult d it)
                     (real_opp (real_mult (real_plus d d) it)))
          (real_opp (real_mult d it)).
Proof.
  intros d it. destruct d as [u Hu]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −u + 2u == u *)
Lemma tw_ring_negu_plus_EF : forall d it : Real,
  real_eq (real_plus (real_opp (real_mult d it))
                     (real_mult (real_plus d d) it))
          (real_mult d it).
Proof.
  intros d it. destruct d as [u Hu]. destruct it as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x == (x+x) + (−x)（x+x ~ 0 时归零链用） *)
Lemma tw_ring_self_minus : forall x : Real,
  real_eq x (real_plus (real_plus x x) (real_opp x)).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x+x) 换形：x + x == 2·x 的右分配形态（配 inv_pos_correct(1+1) 用） *)
Lemma tw_ring_two_split : forall x h : Real,
  real_eq (real_plus (real_mult x h) (real_mult x h))
          (real_mult x (real_mult (real_plus real_one real_one) h)).
Proof.
  intros x h. destruct x as [u Hu]. destruct h as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x + −(−x) == x + x *)
Lemma tw_ring_xopp_x : forall x : Real,
  real_eq (real_plus x (real_opp (real_opp x))) (real_plus x x).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x·h == −(x·h) *)
Lemma tw_ring_opp_mult : forall x h : Real,
  real_eq (real_mult (real_opp x) h) (real_opp (real_mult x h)).
Proof.
  intros x h. destruct x as [u Hu]. destruct h as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x + x == 0 *)
Lemma tw_ring_opp_plus : forall x : Real,
  real_eq (real_plus (real_opp x) x) real_zero.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* ============================================================ *)
(* 2. Q 层助手：QltT 的构造/传输与 Qmin 事实                    *)
(*    QltT x y == Id (Qlt_bool x y) true（非集合体，不可 setoid）*)
(*    ⟹ 一律经 Qcompare = Lt 通道构造，再 Qeq 传输。            *)
(* ============================================================ *)

(* Qcompare = Lt ⟹ QltT（unfold 后改写 match 判别式） *)
Lemma tw_QltT_from_Qcompare : forall a b : Q, Qcompare a b = Lt -> QltT a b.
Proof.
  intros a b H. unfold QltT, Qlt_bool. rewrite H. reflexivity.
Qed.

(* QltT a b 且 b == c ⟹ QltT a c *)
Lemma tw_QltT_transport : forall a b c : Q,
  QltT a b -> b == c -> QltT a c.
Proof.
  intros a b c Hab Hbc.
  apply tw_QltT_from_Qcompare.
  assert (Hcmp : Qcompare a b = Lt).
  { apply Qlt_alt. apply QltT_to_Qlt. exact Hab. }
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b c Hbc).
  exact Hcmp.
Qed.

(* Qmin 事实（GenericMinMax 经 Qminmax.Q 实例化） *)
Lemma tw_Q_min_l : forall e1 e2 : Q, e1 <= e2 -> Qmin e1 e2 == e1.
Proof.
  intros e1 e2 H.
  apply Q.min_l.
  exact H.
Qed.

Lemma tw_Q_min_r : forall e1 e2 : Q, e2 <= e1 -> Qmin e1 e2 == e2.
Proof.
  intros e1 e2 H.
  apply Q.min_r.
  exact H.
Qed.

Lemma tw_Q_le_min_l : forall e1 e2 : Q, Qle (Qmin e1 e2) e1.
Proof.
  intros e1 e2.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qle_refl.
  - rewrite (tw_Q_min_r e1 e2 H).
    exact H.
Qed.

Lemma tw_Q_le_min_r : forall e1 e2 : Q, Qle (Qmin e1 e2) e2.
Proof.
  intros e1 e2.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qlt_le_weak. exact H.
  - rewrite (tw_Q_min_r e1 e2 H).
    apply Qle_refl.
Qed.

(* 正的 Qmin：两见证皆正 ⟹ min 正 *)
Lemma tw_Q_pos_min : forall e1 e2 : Q,
  QltT 0 e1 -> QltT 0 e2 -> QltT 0 (Qmin e1 e2).
Proof.
  intros e1 e2 He1 He2.
  apply tw_QltT_from_Qcompare.
  destruct (Qlt_le_dec e1 e2) as [H | H].
  - rewrite (tw_Q_min_l e1 e2 (Qlt_le_weak _ _ H)).
    apply Qlt_alt. apply QltT_to_Qlt. exact He1.
  - rewrite (tw_Q_min_r e1 e2 H).
    apply Qlt_alt. apply QltT_to_Qlt. exact He2.
Qed.

(* 折半：0 < e < 2y 形态 ⟹ e/2 < y（Q 层，经 field + Qlt_irrefl） *)
Lemma tw_Q_half_lt : forall e y : Q, QltT e (y + y) -> QltT (e / 2) y.
Proof.
  intros e y H.
  assert (Hcmp : Qcompare (e / 2) y = Lt).
  { destruct (Qlt_le_dec (e / 2) y) as [Hyes | Hno].
    - apply Qlt_alt. exact Hyes.
    - exfalso.
      assert (H2 : y + y <= e / 2 + e / 2)
        by (apply Qplus_le_compat; exact Hno).
      assert (H3 : e / 2 + e / 2 == e) by field.
      rewrite H3 in H2.
      assert (H4 : Qlt e e) by (apply (Qlt_le_trans e (y + y) e);
                               [apply QltT_to_Qlt; exact H | exact H2]).
      exact (Qlt_irrefl e H4). }
  apply tw_QltT_from_Qcompare. exact Hcmp.
Qed.

(* ============================================================ *)
(* 3. Real 层见证折半与 exp 恒等式                              *)
(* 0 < y + y ⟹ 0 < y *)
Lemma tw_lt_half : forall y : Real,
  real_lt real_zero (real_plus y y) -> real_lt real_zero y.
Proof.
  intros y H. destruct H as [e [He [N HN]]].
  destruct y as [u Hu].
  exists (e / 2)%Q. split.
  - (* 0 < e/2：反证 e/2 ≤ 0 ⟹ e ≤ 0 与 He 矛盾 *)
    destruct (Qlt_le_dec 0 (e / 2)) as [Hyes | Hno].
    + apply Qlt_to_QltT. exact Hyes.
    + exfalso.
      assert (H2 : e / 2 + e / 2 <= 0 + 0)
        by (apply Qplus_le_compat; exact Hno).
      assert (H3 : e / 2 + e / 2 == e) by field.
      assert (H4 : Qle e 0).
      { apply (Qle_trans e (e / 2 + e / 2) 0).
        - apply qeq_le. apply Qeq_sym. exact H3.
        - apply (Qle_trans (e / 2 + e / 2) (0 + 0) 0).
          + exact H2.
          + apply qeq_le. ring. }
      exact (Qlt_irrefl 0 (Qlt_le_trans 0 e 0 (QltT_to_Qlt 0 e He) H4)).
  - exists N. intros n Hn.
    cbn [projT1 real_plus real_zero].
    cbn [projT1 real_plus real_zero] in HN.
    apply tw_QltT_transport with (b := u n).
    + apply tw_Q_half_lt.
      apply (tw_QltT_transport e (u n + u n - 0) (u n + u n)).
      * exact (HN n Hn).
      * ring.
    + ring.
Qed.

(* 0 < y + y ⟹ −y < 0 *)
Lemma tw_lt_half_opp : forall y : Real,
  real_lt real_zero (real_plus y y) -> real_lt (real_opp y) real_zero.
Proof.
  intros y H.
  apply tw_lt_opp_l.
  apply tw_lt_half.
  exact H.
Qed.

(* exp 单调的 le 版（real_le 的 Or 编码分解到 mono/wd） *)
Lemma tw_exp_mono_le : forall a b : Real,
  real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | Heq].
  - exact (inl (cauchy_real_exp_mono a b Hlt)).
  - exact (inr (cauchy_real_exp_wd a b Heq)).
Qed.

(* e^{−E}·e^{E} == 1（exp_plus + wd + exp_zero 链） *)
Lemma tw_exp_opp_prod : forall E : Real,
  real_eq (real_mult (cauchy_real_exp (real_opp E)) (cauchy_real_exp E))
          real_one.
Proof.
  intros E.
  apply (real_eq_trans _
           (cauchy_real_exp (real_plus (real_opp E) E)) _).
  - apply real_eq_sym. apply (cauchy_real_exp_plus (real_opp E) E).
  - apply (real_eq_trans _ (cauchy_real_exp real_zero) _).
    + apply cauchy_real_exp_wd. apply tw_ring_opp_plus.
    + apply cauchy_real_exp_zero.
Qed.

(* 0 + o1 == o1 *)
Lemma tw_ring_zero_plus_one : forall o1 : Real,
  real_eq (real_plus real_zero o1) o1.
Proof.
  intros o1. destruct o1 as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (x + −1) + 1 == x *)
Lemma tw_ring_add_one_back : forall x : Real,
  real_eq (real_plus (real_plus x (real_opp real_one)) real_one) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 1·x == x *)
Lemma tw_ring_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* −x == −(1·x) *)
Lemma tw_eq_opp_mult_one : forall x : Real,
  real_eq (real_opp x) (real_opp (real_mult real_one x)).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* x·(−1) == −x *)
Lemma tw_ring_mult_opp_one : forall x : Real,
  real_eq (real_mult x (real_opp real_one)) (real_opp x).
Proof.
  intros x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < E ⟹ 1 ≤ e^{E}（经 cauchy_real_exp_minus_one_pos） *)
Lemma tw_le_expE_one : forall E : Real,
  real_lt real_zero E -> real_le real_one (cauchy_real_exp E).
Proof.
  intros E HE.
  assert (Hm : real_lt real_zero
                 (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by (apply (cauchy_real_exp_minus_one_pos E); exact HE).
  assert (Hle0 : real_le real_zero
                   (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by (exact (inl Hm)).
  apply (tw_le_eq_l (real_plus real_zero real_one)
           (cauchy_real_exp E) real_one).
  - apply (tw_le_eq_r
             (real_plus real_zero real_one)
             (real_plus (real_plus (cauchy_real_exp E) (real_opp real_one))
                        real_one)
             (cauchy_real_exp E)).
    + apply real_le_plus_compat; [exact Hle0 | apply real_le_refl].
    + apply (tw_ring_add_one_back (cauchy_real_exp E)).
  - apply tw_ring_zero_plus_one.
Qed.

(* 0 < E ⟹ e^{−E} ≤ 1（右乘 e^{−E} > 0 保序 + 乘积恒等） *)
Lemma tw_le_exp_oppE_one : forall E : Real,
  real_lt real_zero E ->
  real_le (cauchy_real_exp (real_opp E)) real_one.
Proof.
  intros E HE.
  assert (Hc : real_lt real_zero (cauchy_real_exp (real_opp E)))
    by apply cauchy_real_exp_pos.
  assert (H1 : real_le real_one (cauchy_real_exp E))
    by (apply tw_le_expE_one; exact HE).
  assert (H2 : real_le (real_mult real_one (cauchy_real_exp (real_opp E)))
                       (real_mult (cauchy_real_exp E)
                                   (cauchy_real_exp (real_opp E))))
    by (apply (real_le_mult_compat real_one (cauchy_real_exp E) (cauchy_real_exp (real_opp E)) Hc H1)).
  apply (tw_le_eq_r (cauchy_real_exp (real_opp E))
           (real_mult (cauchy_real_exp E) (cauchy_real_exp (real_opp E)))
           real_one).
  - apply (tw_le_eq_l (real_mult real_one (cauchy_real_exp (real_opp E)))
             (real_mult (cauchy_real_exp E) (cauchy_real_exp (real_opp E)))
             (cauchy_real_exp (real_opp E))).
    + exact H2.
    + apply tw_ring_mult_one_l.
  - apply (real_eq_trans _
             (real_mult (cauchy_real_exp (real_opp E)) (cauchy_real_exp E)) _).
    + apply real_mult_comm.
    + apply tw_exp_opp_prod.
Qed.

(* 0 < E ⟹ 1 + −e^{−E} ≤ e^{E} + −1 *)
Lemma tw_one_minus_exp_le : forall E : Real,
  real_lt real_zero E ->
  real_le (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
          (real_plus (cauchy_real_exp E) (real_opp real_one)).
Proof.
  intros E HE.
  assert (Hprod : real_eq (real_mult (cauchy_real_exp (real_opp E))
                                     (cauchy_real_exp E))
                          real_one) by exact (tw_exp_opp_prod E).
  assert (Halt : real_lt real_zero
                   (real_plus (cauchy_real_exp E) (real_opp real_one)))
    by exact (cauchy_real_exp_minus_one_pos E HE).
  (* a := e^{−E} < 1（tw_lt_opp_l + exp 单调 + exp_zero + eq 传输） *)
  assert (Ha1 : real_lt (cauchy_real_exp (real_opp E)) real_one).
  { apply (real_lt_eq_lt (cauchy_real_exp (real_opp E))
             (cauchy_real_exp real_zero) real_one).
    - apply (cauchy_real_exp_mono (real_opp E) real_zero).
      apply tw_lt_opp_l. exact HE.
    - apply cauchy_real_exp_zero. }
  assert (Hc1 : real_lt real_zero
                  (real_plus real_one (real_opp (cauchy_real_exp (real_opp E)))))
    by exact (real_lt_opp_plus (cauchy_real_exp (real_opp E)) real_one Ha1).
  assert (Hage : real_le real_one (cauchy_real_exp E))
    by exact (tw_le_expE_one E HE).
  assert (H2 : real_le (real_mult real_one
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E)))))
                       (real_mult (cauchy_real_exp E)
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E))))))
    by exact (real_le_mult_compat real_one (cauchy_real_exp E)
                (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
                Hc1 Hage).
  (* b·(1−a) == b + −1：分配右 + 1·b ~ b + −(a·b) ~ b + −1 *)
  assert (E2 : real_eq (real_mult (cauchy_real_exp E)
                                  (real_plus real_one
                                             (real_opp (cauchy_real_exp (real_opp E)))))
                       (real_plus (cauchy_real_exp E) (real_opp real_one))).
  { apply (real_eq_trans _
             (real_plus (real_mult real_one (cauchy_real_exp E))
                        (real_mult (real_opp (cauchy_real_exp (real_opp E)))
                                   (cauchy_real_exp E))) _).
    - apply (real_eq_trans _
               (real_mult (real_plus real_one
                                     (real_opp (cauchy_real_exp (real_opp E))))
                          (cauchy_real_exp E)) _).
      + exact (real_mult_comm (cauchy_real_exp E)
                  (real_plus real_one
                             (real_opp (cauchy_real_exp (real_opp E))))).
      + exact (tw_ring_distrib_r real_one
                  (real_opp (cauchy_real_exp (real_opp E)))
                  (cauchy_real_exp E)).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult real_one (cauchy_real_exp E))
               (real_mult (real_opp (cauchy_real_exp (real_opp E)))
                          (cauchy_real_exp E))
               (cauchy_real_exp E) (real_opp real_one)).
      + exact (tw_ring_mult_one_l (cauchy_real_exp E)).
      + apply (real_eq_trans _
                 (real_opp (real_mult (cauchy_real_exp (real_opp E))
                                      (cauchy_real_exp E))) _).
        * exact (tw_ring_opp_mult (cauchy_real_exp (real_opp E))
                    (cauchy_real_exp E)).
        * apply (RealSetoid.real_eq_opp_compat
                   (real_mult (cauchy_real_exp (real_opp E))
                              (cauchy_real_exp E)) real_one).
          exact Hprod. }
  apply (tw_le_eq_r (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))
           (real_mult (cauchy_real_exp E)
                      (real_plus real_one
                                 (real_opp (cauchy_real_exp (real_opp E)))))
           (real_plus (cauchy_real_exp E) (real_opp real_one))).
  - apply (tw_le_eq_l (real_mult real_one
                              (real_plus real_one
                                         (real_opp (cauchy_real_exp (real_opp E)))))
             (real_mult (cauchy_real_exp E)
                        (real_plus real_one
                                   (real_opp (cauchy_real_exp (real_opp E)))))
             (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))).
    + exact H2.
    + exact (tw_ring_mult_one_l
               (real_plus real_one (real_opp (cauchy_real_exp (real_opp E))))).
  - exact E2.
Qed.
(* ============================================================ *)
(* 4. 双侧绝对值引理：|x| ≤ c ⟸ x ≤ c ∧ −x ≤ c                  *)
(*   四情形（lt/lt；eq/eq；lt/eq；eq/lt），eq 混合支用            *)
(*   real_abs_neg_req / real_abs_nonneg_req 符号归零。           *)
(* ============================================================ *)

Lemma tw_abs_le : forall x c : Real,
  real_le x c -> real_le (real_opp x) c -> real_le (real_abs x) c.
Proof.
  intros x c H1 H2.
  destruct H1 as [Hlt1 | Heq1]; destruct H2 as [Hlt2 | Heq2].
  - (* 双严格：见证 Qmin e1 e2；逐点按 u n 符号取分支 *)
    left.
    destruct Hlt1 as [e1 [He1 [N1 HN1]]].
    destruct Hlt2 as [e2 [He2 [N2 HN2]]].
    exists (Qmin e1 e2). split.
    + apply tw_Q_pos_min; assumption.
    + exists (Nat.max N1 N2). intros n Hn.
      destruct x as [u Hu]. destruct c as [v Hv].
      cbn [projT1 real_opp real_zero real_abs].
      assert (Hn1 : NatLe N1 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (Hn2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      assert (Ha : Qlt e1 (v n - u n)) by (apply QltT_to_Qlt; exact (HN1 n Hn1)).
      assert (Hb : Qlt e2 (v n - - u n)) by (apply QltT_to_Qlt; exact (HN2 n Hn2)).
      destruct (Qlt_le_dec (u n) 0) as [Hneg | Hpos].
      * assert (Habs : Qabs (u n) == - u n)
          by (apply Qabs_neg; apply Qlt_le_weak; exact Hneg).
        apply Qlt_to_QltT.
        apply (Qle_lt_trans (Qmin e1 e2) e2 (v n - Qabs (u n))).
        -- apply tw_Q_le_min_r.
        -- assert (Hq : v n - Qabs (u n) == v n - - u n).
           { rewrite Habs. reflexivity. }
           rewrite Hq. exact Hb.
      * assert (Habs : Qabs (u n) == u n) by (apply Qabs_pos; exact Hpos).
        apply Qlt_to_QltT.
        apply (Qle_lt_trans (Qmin e1 e2) e1 (v n - Qabs (u n))).
        -- apply tw_Q_le_min_l.
        -- assert (Hq : v n - Qabs (u n) == v n - u n).
           { rewrite Habs. reflexivity. }
           rewrite Hq. exact Ha.
  - (* x < c ∧ −x == c ⟹ x < −x ⟹ x < 0 ⟹ |x| == −x == c *)
    assert (Hxox : real_lt x (real_opp x)).
    { exact (real_lt_eq_lt x c (real_opp x) Hlt1
               (real_eq_sym (real_opp x) c Heq2)). }
    assert (Hx0 : real_lt x real_zero).
    { apply (real_eq_lt_lt x (real_opp (real_opp x)) real_zero).
      + apply real_eq_sym. apply real_opp_opp.
      + apply tw_lt_half_opp. exact (real_lt_opp_plus x (real_opp x) Hxox). }
    exact (inr (real_eq_trans (real_abs x) (real_opp x) c
                  (real_abs_neg_req x Hx0) Heq2)).
  - (* x == c ∧ −x < c ⟹ −x < x ⟹ 0 < x ⟹ |x| == x == c *)
    assert (Hox : real_lt (real_opp x) x).
    { exact (real_lt_eq_lt (real_opp x) c x Hlt2 (real_eq_sym x c Heq1)). }
    assert (Hx0 : real_lt real_zero x).
    { apply tw_lt_half.
      apply (real_lt_eq_lt real_zero
               (real_plus x (real_opp (real_opp x))) (real_plus x x)).
      + exact (real_lt_opp_plus (real_opp x) x Hox).
      + apply tw_ring_xopp_x. }
    exact (inr (real_eq_trans (real_abs x) x c (real_abs_pos_req x Hx0) Heq1)).
  - (* x == c ∧ −x == c ⟹ x == −x ⟹ x == 0 ⟹ |x| == 0 == c *)
    assert (Hxx : real_eq x (real_opp x)).
    { exact (real_eq_trans x c (real_opp x) Heq1 (real_eq_sym (real_opp x) c Heq2)). }
    pose (h2 := real_inv_pos (real_plus real_one real_one) real_two_pos).
    assert (Hinv : real_eq (real_mult (real_plus real_one real_one) h2) real_one).
    { unfold h2. apply real_inv_pos_correct. }
    assert (Hstep1 : real_eq x
                       (real_plus (real_mult x h2) (real_mult x h2))).
    { apply (real_eq_trans x
               (real_mult x (real_mult (real_plus real_one real_one) h2))
               (real_plus (real_mult x h2) (real_mult x h2))).
      - apply (real_eq_sym
                 (real_mult x (real_mult (real_plus real_one real_one) h2)) x).
        + apply (real_eq_trans
                   (real_mult x (real_mult (real_plus real_one real_one) h2))
                   (real_mult x real_one) x).
          * apply (RealSetoid.real_eq_mult_compat x
                     (real_mult (real_plus real_one real_one) h2)
                     x real_one).
            -- apply real_eq_refl.
            -- exact Hinv.
          * apply real_mult_one.
      - exact (real_eq_sym _ _ (tw_ring_two_split x h2)). }
    assert (Hstep2 : real_eq (real_mult x h2) (real_opp (real_mult x h2))).
    { apply (real_eq_trans (real_mult x h2)
               (real_mult (real_opp x) h2) _).
      - apply (RealSetoid.real_eq_mult_compat x h2 (real_opp x) h2 Hxx
                 (real_eq_refl h2)).
      - apply tw_ring_opp_mult. }
    assert (Hx0 : real_eq x real_zero).
    { exact (real_eq_trans x
               (real_plus (real_mult x h2) (real_mult x h2))
               real_zero
               Hstep1
               (real_eq_trans _
                  (real_plus (real_mult x h2) (real_opp (real_mult x h2)))
                  real_zero
                  (RealSetoid.real_eq_plus_compat (real_mult x h2)
                    (real_mult x h2) (real_mult x h2)
                    (real_opp (real_mult x h2)) (real_eq_refl _) Hstep2)
                  (real_plus_opp _))). }
    exact (inr (real_eq_trans (real_abs x) real_zero c
                  (real_eq_trans (real_abs x) (real_abs real_zero) real_zero
                     (real_abs_eq_compat x real_zero Hx0)
                     real_abs_zero_req)
                  (real_eq_sym c real_zero
                     (real_eq_trans c x real_zero (real_eq_sym x c Heq1) Hx0)))).
Qed.
(* ============================================================ *)

(* ============================================================ *)

(* (a·b)·(c·d) == (a·c)·(b·d)（四因子重排） *)
Lemma tw_ring_abcd : forall a b c d : Real,
  real_eq (real_mult (real_mult a b) (real_mult c d))
          (real_mult (real_mult a c) (real_mult b d)).
Proof.
  intros a b c d.
  destruct a as [u1 Hu1]. destruct b as [u2 Hu2].
  destruct c as [v1 Hv1]. destruct d as [v2 Hv2].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (a·b)·c == (a·c)·b（中因子换位） *)
Lemma tw_ring_abc_acb : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult (real_mult a c) b).
Proof.
  intros a b c. destruct a as [u Hu]. destruct b as [v Hv]. destruct c as [w Hw].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* (−x) + (x + −y) == −y *)
Lemma tw_ring_opp_xplus : forall x y : Real,
  real_eq (real_plus (real_opp x) (real_plus x (real_opp y))) (real_opp y).
Proof.
  intros x y. destruct x as [u Hu]. destruct y as [v Hv].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* 0 < c ⟹ x < x + c（见证 e、N 直传，逐点 ring） *)
Lemma tw_lt_plus_r_zero : forall x c : Real,
  real_lt real_zero c -> real_lt x (real_plus x c).
Proof.
  intros x c H. destruct H as [e [He [N HN]]].
  destruct x as [u Hu]. destruct c as [v Hv].
  exists e. split.
  - exact He.
  - exists N. intros n Hn.
    cbn [projT1 real_plus].
    apply Qlt_to_QltT.
    assert (Hq : Qlt e (v n - 0)) by (apply QltT_to_Qlt; exact (HN n Hn)).
    assert (Hz : u n + v n - u n == v n - 0) by ring.
    rewrite Hz. exact Hq.
Qed.

(* a ≤ b ⟹ −b ≤ −a（lt 支经差正性 + x < x + c；eq 支 opp 传输） *)
Lemma tw_le_opp_compat : forall a b : Real,
  real_le a b -> real_le (real_opp b) (real_opp a).
Proof.
  intros a b H. destruct H as [Hlt | Heq].
  - apply tw_lt_le.
    apply (real_lt_eq_lt (real_opp b)
             (real_plus (real_opp b) (real_plus b (real_opp a)))
             (real_opp a)).
    + apply tw_lt_plus_r_zero.
      exact (real_lt_opp_plus a b Hlt).
    + apply tw_ring_opp_xplus.
  - apply tw_eq_le.
    exact (real_eq_sym (real_opp a) (real_opp b)
             (RealSetoid.real_eq_opp_compat a b Heq)).
Qed.

(* 左乘保序：0 < c、a ≤ b ⟹ c·a ≤ c·b（副本 real_le_mult_compat） *)
Lemma tw_le_mult_compat_l : forall a b c : Real,
  real_lt real_zero c -> real_le a b -> real_le (real_mult c a) (real_mult c b).
Proof.
  intros a b c Hc Hab.
  apply (RealSetoid.real_le_id_l (real_mult c a) (real_mult a c) (real_mult c b)).
  - apply real_mult_comm.
  - apply (RealSetoid.real_le_id_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + apply real_mult_comm.
    + apply (real_le_mult_compat a b c Hc Hab).
Qed.

(* 倒数唯一性：x > 0、x·y == 1 ⟹ inv x == y
   链：inv x == inv x·1 == inv x·(x·y) == (inv x·x)·y
       == (x·inv x)·y == 1·y == y *)
Lemma tw_inv_unique : forall (x y : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult x y) real_one -> real_eq (real_inv_pos x Hx) y.
Proof.
  intros x y Hx Hxy.
  apply (real_eq_trans (real_inv_pos x Hx)
           (real_mult (real_inv_pos x Hx) (real_mult x y)) y).
  - apply (real_eq_trans (real_inv_pos x Hx)
             (real_mult (real_inv_pos x Hx) real_one)
             (real_mult (real_inv_pos x Hx) (real_mult x y))).
    + apply real_eq_sym. apply real_mult_one.
    + apply (RealSetoid.real_eq_mult_compat (real_inv_pos x Hx) real_one
               (real_inv_pos x Hx) (real_mult x y)
               (real_eq_refl (real_inv_pos x Hx)) (real_eq_sym _ _ Hxy)).
  - apply (real_eq_trans (real_mult (real_inv_pos x Hx) (real_mult x y))
             (real_mult (real_mult (real_inv_pos x Hx) x) y) _).
    + apply real_mult_assoc.
    + apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) x) y)
               (real_mult real_one y) y).
      * apply (real_eq_trans (real_mult (real_mult (real_inv_pos x Hx) x) y)
                 (real_mult (real_mult x (real_inv_pos x Hx)) y)
                 (real_mult real_one y)).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_mult (real_inv_pos x Hx) x) y
                     (real_mult x (real_inv_pos x Hx)) y
                     (real_mult_comm (real_inv_pos x Hx) x) (real_eq_refl y)).
        -- apply (RealSetoid.real_eq_mult_compat
                     (real_mult x (real_inv_pos x Hx)) y real_one y
                     (real_inv_pos_correct x Hx) (real_eq_refl y)).
      * apply tw_ring_mult_one_l.
Qed.

(* ============================================================ *)
(* 6. list 求和序机器（泛型，Section 外）                        *)
(* ============================================================ *)

(* of_nat 非负 *)
Lemma tw_of_nat_nonneg : forall k : nat, real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_r real_zero
             (real_plus real_one (real_of_nat k))
             (real_of_nat (Datatypes.S k))).
    + apply real_eq_refl.
    + apply (RealSetoid.real_le_id_l real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat k))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_le_plus_compat.
        -- apply tw_lt_le. apply real_lt_zero_one.
        -- exact IH.
Qed.

(* 非空表势正性 *)
Lemma tw_list_len_pos : forall (X : Set) (l : list X),
  Not (Id l nil) -> real_lt real_zero (real_of_nat (length l)).
Proof.
  intros X l. destruct l as [| w rest].
  - intro H. exact (match H (@id_refl (list X) nil) with end).
  - cbn [length]. intro Hn.
    apply (real_lt_eq_lt real_zero
             (real_plus real_one (real_of_nat (length rest))) _).
    + apply (real_eq_lt_lt real_zero
               (real_plus real_zero real_zero)
               (real_plus real_one (real_of_nat (length rest)))).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_lt_plus_compat_lt_le.
        -- apply real_lt_zero_one.
        -- apply tw_of_nat_nonneg.
    + apply real_eq_refl.
Qed.

(* 逐点正 ⟹ 非空和正 *)
Lemma tw_sum_pos_nonempty : forall (X : Set) (f : X -> Real) (l : list X),
  (forall y : X, real_lt real_zero (f y)) -> Not (Id l nil) ->
  real_lt real_zero (real_list_sum X f l).
Proof.
  intros X f l. induction l as [| y rest IH]; intros Hf Hl.
  - exact (match Hl (@id_refl (list X) nil) with end).
  - destruct rest as [| y2 rest2].
    + cbn [real_list_sum].
      apply (real_lt_eq_lt real_zero (f y) (real_plus (f y) real_zero)).
      * apply Hf.
      * apply real_eq_sym. apply real_plus_zero.
    + cbn [real_list_sum].
      assert (Hpos : real_lt real_zero
                       (real_plus (f y)
                          (real_plus (f y2)
                             (real_list_sum X f rest2)))).
      { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) _).
        - apply real_eq_sym. apply real_plus_zero.
        - apply real_lt_plus_compat.
          + apply Hf.
          + apply (IH Hf).
            intro Hc. inversion Hc. }
      apply (real_lt_eq_lt real_zero
               (real_plus (f y) (real_plus (f y2) (real_list_sum X f rest2))) _).
      * exact Hpos.
      * apply real_eq_refl.
Qed.

(* 逐点 ≤ c ⟹ Σ f ≤ N·c（副本 sum_nonneg_le_const_aux） *)
Lemma tw_sum_le_const : forall (X : Set) (f : X -> Real) (c : Real) (l : list X),
  (forall z : X, InT z l -> real_le (f z) c) ->
  real_le (real_list_sum X f l) (real_mult (real_of_nat (length l)) c).
Proof.
  intros X f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le real_zero
             (real_mult (real_of_nat (length (@nil X))) c)
             (real_eq_sym (real_mult real_zero c) real_zero
                (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                   real_zero (real_mult_comm real_zero c)
                   (real_mult_zero c)))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_r
             (real_plus (f x) (real_list_sum X f rest))
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)).
    + apply (real_eq_trans
               (real_plus c (real_mult (real_of_nat (length rest)) c))
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (real_of_nat (length rest)) c)
                 (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans c (real_mult c real_one)
                     (real_mult real_one c)
                     (real_eq_sym (real_mult c real_one) c (real_mult_one c))
                     (real_mult_comm c real_one)).
        -- apply real_eq_refl.
      * apply real_distrib_r.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros z Hz. apply Hb. exact (InT_next z x rest Hz).
Qed.

(* 逐点 c ≤ f ⟹ N·c ≤ Σ f（下常数界，tw_sum_le_const 副本） *)
Lemma tw_const_le_sum : forall (X : Set) (f : X -> Real) (c : Real) (l : list X),
  (forall z : X, InT z l -> real_le c (f z)) ->
  real_le (real_mult (real_of_nat (length l)) c) (real_list_sum X f l).
Proof.
  intros X f c l. induction l as [| x rest IH]; intro Hb.
  - exact (RealSetoid.real_eq_le
             (real_mult (real_of_nat (length (@nil X))) c)
             (real_list_sum X f (@nil X))
             (real_eq_trans (real_mult real_zero c) (real_mult c real_zero)
                (real_list_sum X f (@nil X))
                (real_mult_comm real_zero c) (real_mult_zero c))).
  - cbn [real_list_sum length].
    apply (RealSetoid.real_le_id_l
             (real_mult (real_of_nat (Datatypes.S (length rest))) c)
             (real_plus c (real_mult (real_of_nat (length rest)) c))
             (real_plus (f x) (real_list_sum X f rest))).
    + apply (real_eq_trans
               (real_mult (real_of_nat (Datatypes.S (length rest))) c)
               (real_plus (real_mult real_one c)
                  (real_mult (real_of_nat (length rest)) c)) _).
      * apply real_eq_sym. apply real_distrib_r.
      * apply (RealSetoid.real_eq_plus_compat (real_mult real_one c)
                 (real_mult (real_of_nat (length rest)) c)
                 c (real_mult (real_of_nat (length rest)) c)).
        -- apply (real_eq_trans (real_mult real_one c) (real_mult c real_one) c
                     (real_mult_comm real_one c) (real_mult_one c)).
        -- apply real_eq_refl.
    + apply real_le_plus_compat.
      * apply Hb. apply InT_here.
      * apply IH. intros z Hz. apply Hb. exact (InT_next z x rest Hz).
Qed.

(* ============================================================ *)
(* 7. Section TempWindow：list 世界 + T→∞ 均匀极限主定理          *)
(* ============================================================ *)

Section TempWindow.

(* 世界：list 离散状态非空 + logits 双界（诚实接口，副本 AttnHardLimit） *)
Variable Tok : Set.
Variable states : list Tok.
Variable states_nonempty : Not (Id states nil).
Variable zz : Tok -> Real.
Variable Delta : Real.
Variable Delta_pos : real_lt real_zero Delta.
Variable Hzz_lo : forall x : Tok, real_le (real_opp Delta) (zz x).
Variable Hzz_hi : forall x : Tok, real_le (zz x) Delta.

(* ---------- 7.1 温度化 softmax 分布与均匀分布 ---------- *)

(* 因子 e^{z(x)/T}（副本 factor_T 形态） *)
Definition tw_factor (T : Real) (Ht : real_lt real_zero T) (x : Tok) : Real :=
  cauchy_real_exp (real_mult (real_inv_pos T Ht) (zz x)).

(* 配分函数 Z(T) = Σ states e^{z(x)/T} *)
Definition tw_ZT (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Tok (tw_factor T Ht) states.

Definition tw_ZT_pos (T : Real) (Ht : real_lt real_zero T) :
  real_lt real_zero (tw_ZT T Ht).
Proof.
  unfold tw_ZT. apply tw_sum_pos_nonempty.
  - intro x. apply cauchy_real_exp_pos.
  - exact states_nonempty.
Defined.

(* N = |states| > 0（透明件：进 real_inv_pos 计算位） *)
Definition tw_states_len_pos : real_lt real_zero (real_of_nat (length states)) :=
  tw_list_len_pos Tok states states_nonempty.

(* uniform(x) = 1/N *)
Definition tw_unif_dist : Real :=
  real_inv_pos (real_of_nat (length states)) tw_states_len_pos.

(* w_T(x) = e^{z(x)/T}/Z(T) *)
Definition tw_wT (T : Real) (Ht : real_lt real_zero T) (x : Tok) : Real :=
  real_mult (tw_factor T Ht x) (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)).

(* TV(w_T, U) = Σ_x |w_T(x) − 1/N| *)
Definition tv_unif (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_list_sum Tok
    (fun x => real_abs (real_minus_r (tw_wT T Ht x) tw_unif_dist)) states.

(* 规范指数：u = Δ/T、u2 = 2Δ/T 与四个 exp 值 *)
Definition tw_u (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult (real_inv_pos T Ht) Delta.
Definition tw_u2 (T : Real) (Ht : real_lt real_zero T) : Real :=
  real_mult (real_plus Delta Delta) (real_inv_pos T Ht).
Definition tw_EU (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (tw_u T Ht).
Definition tw_EL (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (tw_u T Ht)).
Definition tw_E2 (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (tw_u2 T Ht).
Definition tw_E2L (T : Real) (Ht : real_lt real_zero T) : Real :=
  cauchy_real_exp (real_opp (tw_u2 T Ht)).

(* ---------- 7.2 正性与指数恒等式 ---------- *)

Lemma tw_u2_pos : forall T Ht, real_lt real_zero (tw_u2 T Ht).
Proof.
  intros T Ht.
  assert (H2D : real_lt real_zero (real_plus Delta Delta)).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
             (real_plus Delta Delta)).
    - apply real_eq_sym. apply real_plus_zero.
    - exact (real_lt_plus_compat real_zero Delta real_zero Delta
               Delta_pos Delta_pos). }
  unfold tw_u2.
  apply (real_mult_pos_compat (real_plus Delta Delta) (real_inv_pos T Ht)).
  - exact H2D.
  - apply real_inv_pos_pos.
Qed.

(* u + u == u2：invT·Δ + invT·Δ == (Δ+Δ)·invT *)
Lemma tw_uu_eq_u2 : forall T Ht,
  real_eq (real_plus (tw_u T Ht) (tw_u T Ht)) (tw_u2 T Ht).
Proof.
  intros T Ht. unfold tw_u, tw_u2.
  apply (real_eq_trans
           (real_plus (real_mult (real_inv_pos T Ht) Delta)
                      (real_mult (real_inv_pos T Ht) Delta))
           (real_plus (real_mult Delta (real_inv_pos T Ht))
                      (real_mult Delta (real_inv_pos T Ht)))
           (real_mult (real_plus Delta Delta) (real_inv_pos T Ht))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (real_inv_pos T Ht) Delta)
             (real_mult (real_inv_pos T Ht) Delta)
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult_comm (real_inv_pos T Ht) Delta)
             (real_mult_comm (real_inv_pos T Ht) Delta)).
  - apply real_eq_sym. apply tw_ring_dd_mult.
Qed.

(* e^u·e^u == e^{u2} *)
Lemma tw_EU_EU_eq_E2 : forall T Ht,
  real_eq (real_mult (tw_EU T Ht) (tw_EU T Ht)) (tw_E2 T Ht).
Proof.
  intros T Ht.
  apply (real_eq_trans (real_mult (tw_EU T Ht) (tw_EU T Ht))
           (cauchy_real_exp (real_plus (tw_u T Ht) (tw_u T Ht))) (tw_E2 T Ht)).
  - apply real_eq_sym. apply (cauchy_real_exp_plus (tw_u T Ht) (tw_u T Ht)).
  - apply cauchy_real_exp_wd. exact (tw_uu_eq_u2 T Ht).
Qed.

(* e^{−u}·e^{−u} == e^{−u2} *)
Lemma tw_EL_EL_eq_E2L : forall T Ht,
  real_eq (real_mult (tw_EL T Ht) (tw_EL T Ht)) (tw_E2L T Ht).
Proof.
  intros T Ht.
  apply (real_eq_trans (real_mult (tw_EL T Ht) (tw_EL T Ht))
           (cauchy_real_exp
              (real_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht))))
           (tw_E2L T Ht)).
  - apply real_eq_sym.
    apply (cauchy_real_exp_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht))).
  - apply cauchy_real_exp_wd.
    apply (real_eq_trans
             (real_plus (real_opp (tw_u T Ht)) (real_opp (tw_u T Ht)))
             (real_opp (real_plus (tw_u T Ht) (tw_u T Ht)))
             (real_opp (tw_u2 T Ht))).
    + apply real_eq_sym. apply real_opp_plus.
    + apply (RealSetoid.real_eq_opp_compat (real_plus (tw_u T Ht) (tw_u T Ht))
               (tw_u2 T Ht)).
      exact (tw_uu_eq_u2 T Ht).
Qed.

(* ---------- 7.3 逐点 exp 夹逼 ---------- *)

Lemma tw_EL_le_factor : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_EL T Ht) (tw_factor T Ht x).
Proof.
  intros T Ht x. unfold tw_EL, tw_factor, tw_u.
  apply tw_exp_mono_le.
  apply (RealSetoid.real_le_id_l (real_opp (real_mult (real_inv_pos T Ht) Delta))
           (real_mult (real_opp Delta) (real_inv_pos T Ht))
           (real_mult (real_inv_pos T Ht) (zz x))).
  - apply (real_eq_trans (real_opp (real_mult (real_inv_pos T Ht) Delta))
             (real_opp (real_mult Delta (real_inv_pos T Ht)))
             (real_mult (real_opp Delta) (real_inv_pos T Ht))).
    + apply (RealSetoid.real_eq_opp_compat (real_mult (real_inv_pos T Ht) Delta)
               (real_mult Delta (real_inv_pos T Ht))).
      apply real_mult_comm.
    + apply real_eq_sym. apply tw_ring_opp_mult.
  - apply (real_le_trans (real_mult (real_opp Delta) (real_inv_pos T Ht))
             (real_mult (zz x) (real_inv_pos T Ht))
             (real_mult (real_inv_pos T Ht) (zz x))).
    + apply (real_le_mult_compat (real_opp Delta) (zz x)
               (real_inv_pos T Ht) (real_inv_pos_pos T Ht) (Hzz_lo x)).
    + apply (RealSetoid.real_eq_le _ _
               (real_mult_comm (zz x) (real_inv_pos T Ht))).
Qed.

Lemma tw_factor_le_EU : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_factor T Ht x) (tw_EU T Ht).
Proof.
  intros T Ht x. unfold tw_EU, tw_factor, tw_u.
  apply tw_exp_mono_le.
  apply (real_le_trans (real_mult (real_inv_pos T Ht) (zz x))
           (real_mult (zz x) (real_inv_pos T Ht))
           (real_mult (real_inv_pos T Ht) Delta)).
  - apply (RealSetoid.real_eq_le _ _
             (real_mult_comm (real_inv_pos T Ht) (zz x))).
  - apply (real_le_trans (real_mult (zz x) (real_inv_pos T Ht))
             (real_mult Delta (real_inv_pos T Ht))
             (real_mult (real_inv_pos T Ht) Delta)).
    + apply (real_le_mult_compat (zz x) Delta
               (real_inv_pos T Ht) (real_inv_pos_pos T Ht) (Hzz_hi x)).
    + apply (RealSetoid.real_eq_le _ _
               (real_mult_comm Delta (real_inv_pos T Ht))).
Qed.

(* ---------- 7.4 配分函数双侧界与 inv 三明治 ---------- *)

Lemma tw_ZT_ge_NEL : forall T Ht,
  real_le (real_mult (real_of_nat (length states)) (tw_EL T Ht)) (tw_ZT T Ht).
Proof.
  intros T Ht.
  unfold tw_ZT.
  apply tw_const_le_sum.
  intros x _.
  apply tw_EL_le_factor.
Qed.

Lemma tw_ZT_le_NEU : forall T Ht,
  real_le (tw_ZT T Ht)
          (real_mult (real_of_nat (length states)) (tw_EU T Ht)).
Proof.
  intros T Ht.
  unfold tw_ZT.
  apply tw_sum_le_const.
  intros x _.
  apply tw_factor_le_EU.
Qed.

(* inv Z ≤ invN·e^{Δ/T}：Z ≥ N·e^{−Δ/T} 反单调 + inv 唯一性 *)
Lemma tw_invZ_le_EUinvN : forall T Ht,
  real_le (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
          (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EU T Ht)).
Proof.
  intros T Ht.
  assert (HZge : real_le (real_mult (real_of_nat (length states))
                            (tw_EL T Ht)) (tw_ZT T Ht))
    by exact (tw_ZT_ge_NEL T Ht).
  assert (Hple : real_lt real_zero
                   (real_mult (real_of_nat (length states)) (tw_EL T Ht)))
    by (apply (real_mult_pos_compat (real_of_nat (length states))
                 (tw_EL T Ht));
        [exact tw_states_len_pos | apply cauchy_real_exp_pos]).
  assert (Hinv : real_le (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                   (real_inv_pos (real_mult (real_of_nat (length states))
                                       (tw_EL T Ht)) Hple))
    by exact (real_inv_pos_le_compat (real_mult (real_of_nat (length states))
                          (tw_EL T Ht)) (tw_ZT T Ht) Hple
                 (tw_ZT_pos T Ht) HZge).
  assert (Hid : real_eq (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EL T Ht)) Hple)
                  (real_mult (real_inv_pos (real_of_nat (length states))
                              tw_states_len_pos) (tw_EU T Ht))).
  { apply (tw_inv_unique (real_mult (real_of_nat (length states))
                            (tw_EL T Ht))
             (real_mult (real_inv_pos (real_of_nat (length states))
                         tw_states_len_pos) (tw_EU T Ht)) Hple).
    apply (real_eq_trans
             (real_mult (real_mult (real_of_nat (length states))
                          (tw_EL T Ht))
                       (real_mult (real_inv_pos (real_of_nat (length states))
                                   tw_states_len_pos) (tw_EU T Ht)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos))
                (real_mult (tw_EL T Ht) (tw_EU T Ht)))
             real_one).
    - apply tw_ring_abcd.
    - apply (real_eq_trans _ (real_mult real_one real_one) real_one).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (tw_EL T Ht) (tw_EU T Ht))
                 real_one real_one
                 (real_inv_pos_correct (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_exp_opp_prod (tw_u T Ht))).
      + apply real_mult_one. }
  exact (tw_le_eq_r
           (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
           (real_inv_pos (real_mult (real_of_nat (length states))
                              (tw_EL T Ht)) Hple)
           (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EU T Ht))
           Hinv Hid).
Qed.

(* invN·e^{−Δ/T} ≤ inv Z：Z ≤ N·e^{Δ/T} 反单调 + inv 唯一性 *)
Lemma tw_ELinvN_le_invZ : forall T Ht,
  real_le (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EL T Ht))
          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)).
Proof.
  intros T Ht.
  assert (HZle : real_le (tw_ZT T Ht)
                   (real_mult (real_of_nat (length states)) (tw_EU T Ht)))
    by exact (tw_ZT_le_NEU T Ht).
  assert (Hpue : real_lt real_zero
                   (real_mult (real_of_nat (length states)) (tw_EU T Ht)))
    by (apply (real_mult_pos_compat (real_of_nat (length states))
                 (tw_EU T Ht));
        [exact tw_states_len_pos | apply cauchy_real_exp_pos]).
  assert (Hinv : real_le (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EU T Ht)) Hpue)
                   (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by exact (real_inv_pos_le_compat (tw_ZT T Ht)
                (real_mult (real_of_nat (length states)) (tw_EU T Ht))
                (tw_ZT_pos T Ht) Hpue HZle).
  assert (Hid : real_eq (real_inv_pos (real_mult (real_of_nat (length states))
                                     (tw_EU T Ht)) Hpue)
                  (real_mult (real_inv_pos (real_of_nat (length states))
                              tw_states_len_pos) (tw_EL T Ht))).
  { apply (tw_inv_unique (real_mult (real_of_nat (length states))
                            (tw_EU T Ht))
             (real_mult (real_inv_pos (real_of_nat (length states))
                         tw_states_len_pos) (tw_EL T Ht)) Hpue).
    apply (real_eq_trans
             (real_mult (real_mult (real_of_nat (length states))
                          (tw_EU T Ht))
                       (real_mult (real_inv_pos (real_of_nat (length states))
                                   tw_states_len_pos) (tw_EL T Ht)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos))
                (real_mult (tw_EU T Ht) (tw_EL T Ht)))
             real_one).
    - apply tw_ring_abcd.
    - apply (real_eq_trans _ (real_mult real_one real_one) real_one).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (tw_EU T Ht) (tw_EL T Ht))
                 real_one real_one
                 (real_inv_pos_correct (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_eq_trans (real_mult (tw_EU T Ht) (tw_EL T Ht))
                    (real_mult (tw_EL T Ht) (tw_EU T Ht)) real_one
                    (real_mult_comm (tw_EU T Ht) (tw_EL T Ht))
                    (tw_exp_opp_prod (tw_u T Ht)))).
      + apply real_mult_one. }
  exact (tw_le_eq_l
           (real_inv_pos (real_mult (real_of_nat (length states))
                              (tw_EU T Ht)) Hpue)
           (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
           (real_mult (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos) (tw_EL T Ht))
           Hinv Hid).
Qed.

(* ---------- 7.5 逐点 w 界与逐点绝对值界 ---------- *)

(* w_T(x) ≤ e^{2Δ/T}·(1/N) *)
Lemma tw_wT_le_E2invN : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (tw_wT T Ht x)
          (real_mult (tw_E2 T Ht)
             (real_inv_pos (real_of_nat (length states)) tw_states_len_pos)).
Proof.
  intros T Ht x.
  assert (HinvZ : real_lt real_zero
                    (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by apply real_inv_pos_pos.
  assert (HEU : real_lt real_zero (tw_EU T Ht)) by apply cauchy_real_exp_pos.
  assert (H1 : real_le (real_mult (tw_factor T Ht x)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_EU T Ht)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (real_le_mult_compat (tw_factor T Ht x) (tw_EU T Ht)
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)) HinvZ
                (tw_factor_le_EU T Ht x)).
  assert (H2 : real_le (real_mult (tw_EU T Ht)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_EU T Ht)
                          (real_mult (real_inv_pos (real_of_nat (length states))
                                      tw_states_len_pos) (tw_EU T Ht))))
    by exact (tw_le_mult_compat_l
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EU T Ht))
                (tw_EU T Ht) HEU (tw_invZ_le_EUinvN T Ht)).
  assert (Hid : real_eq (real_mult (tw_EU T Ht)
                          (real_mult (real_inv_pos (real_of_nat (length states))
                                      tw_states_len_pos) (tw_EU T Ht)))
                  (real_mult (tw_E2 T Ht)
                     (real_inv_pos (real_of_nat (length states))
                        tw_states_len_pos))).
  { apply (real_eq_trans
             (real_mult (tw_EU T Ht)
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EU T Ht)))
             (real_mult (real_mult (tw_EU T Ht)
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos)) (tw_EU T Ht))
             (real_mult (tw_E2 T Ht)
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))).
    - apply real_mult_assoc.
    - apply (real_eq_trans
               (real_mult (real_mult (tw_EU T Ht)
                            (real_inv_pos (real_of_nat (length states))
                               tw_states_len_pos)) (tw_EU T Ht))
               (real_mult (real_mult (tw_EU T Ht) (tw_EU T Ht))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos)) _).
      + apply tw_ring_abc_acb.
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (tw_EU T Ht) (tw_EU T Ht))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_E2 T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (tw_EU_EU_eq_E2 T Ht) (real_eq_refl _)). }
  apply (real_le_trans (real_mult (tw_factor T Ht x)
                            (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
           (real_mult (tw_EU T Ht)
              (real_mult (real_inv_pos (real_of_nat (length states))
                          tw_states_len_pos) (tw_EU T Ht)))
           (real_mult (tw_E2 T Ht)
              (real_inv_pos (real_of_nat (length states))
                 tw_states_len_pos))).
  - exact (real_le_trans _ _ _ H1 H2).
  - exact (RealSetoid.real_eq_le _ _ Hid).
Qed.

(* e^{−2Δ/T}·(1/N) ≤ w_T(x) *)
Lemma tw_E2LinvN_le_wT : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (real_mult (tw_E2L T Ht)
             (real_inv_pos (real_of_nat (length states)) tw_states_len_pos))
          (tw_wT T Ht x).
Proof.
  intros T Ht x.
  assert (HinvZ : real_lt real_zero
                    (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
    by apply real_inv_pos_pos.
  assert (HEL : real_lt real_zero (tw_EL T Ht)) by apply cauchy_real_exp_pos.
  assert (Hid : real_eq (real_mult (tw_E2L T Ht)
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos))
                  (real_mult (tw_EL T Ht)
                     (real_mult (real_inv_pos (real_of_nat (length states))
                                 tw_states_len_pos) (tw_EL T Ht)))).
  { apply (real_eq_trans
             (real_mult (tw_E2L T Ht)
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))
             (real_mult (tw_EL T Ht)
                (real_mult (tw_EL T Ht)
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos)))
             (real_mult (tw_EL T Ht)
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EL T Ht)))).
    - apply (real_eq_trans
               (real_mult (tw_E2L T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult (real_mult (tw_EL T Ht) (tw_EL T Ht))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult (tw_EL T Ht)
                  (real_mult (tw_EL T Ht)
                     (real_inv_pos (real_of_nat (length states))
                        tw_states_len_pos)))).
      + apply (RealSetoid.real_eq_mult_compat
                 (tw_E2L T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult (tw_EL T Ht) (tw_EL T Ht))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_eq_sym _ _ (tw_EL_EL_eq_E2L T Ht)) (real_eq_refl _)).
      + apply real_eq_sym.
        exact (real_mult_assoc (tw_EL T Ht) (tw_EL T Ht)
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)).
    - apply (RealSetoid.real_eq_mult_compat
               (tw_EL T Ht)
               (real_mult (tw_EL T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (tw_EL T Ht)
               (real_mult (real_inv_pos (real_of_nat (length states))
                           tw_states_len_pos) (tw_EL T Ht))
               (real_eq_refl (tw_EL T Ht))
               (real_mult_comm (tw_EL T Ht)
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))). }
  assert (H2 : real_le (real_mult (tw_EL T Ht)
                         (real_mult (real_inv_pos (real_of_nat (length states))
                                     tw_states_len_pos) (tw_EL T Ht)))
                       (real_mult (tw_EL T Ht)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (tw_le_mult_compat_l
                (real_mult (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos) (tw_EL T Ht))
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))
                (tw_EL T Ht) HEL (tw_ELinvN_le_invZ T Ht)).
  assert (H3 : real_le (real_mult (tw_EL T Ht)
                         (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
                       (real_mult (tw_factor T Ht x)
                          (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht))))
    by exact (real_le_mult_compat (tw_EL T Ht) (tw_factor T Ht x)
                (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)) HinvZ
                (tw_EL_le_factor T Ht x)).
  apply (real_le_trans
           (real_mult (tw_E2L T Ht)
              (real_inv_pos (real_of_nat (length states))
                 tw_states_len_pos))
           (real_mult (tw_EL T Ht)
              (real_inv_pos (tw_ZT T Ht) (tw_ZT_pos T Ht)))
           (tw_wT T Ht x)).
  - exact (RealSetoid.real_le_id_l _ _ _ Hid H2).
  - exact H3.
Qed.

(* 逐点绝对值界：|w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)/N
   tw_abs_le 完成：上支 w−1/N ≤ (E2−1)/N（tw_ring_sub_mult 换形）；
   下支 1/N−w ≤ (1−e^{−2Δ/T})/N ≤ (E2−1)/N
   （tw_ring_sub_mult_l + tw_one_minus_exp_le） *)
Lemma tw_h_le : forall (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le (real_abs (real_minus_r (tw_wT T Ht x) tw_unif_dist))
          (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
             tw_unif_dist).
Proof.
  intros T Ht x.
  assert (HinvN : real_lt real_zero tw_unif_dist)
    by (unfold tw_unif_dist; apply real_inv_pos_pos).
  apply tw_abs_le.
  - apply (tw_le_eq_r (real_minus_r (tw_wT T Ht x) tw_unif_dist)
             (real_plus (real_mult (tw_E2 T Ht) tw_unif_dist)
                (real_opp tw_unif_dist))
             (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                tw_unif_dist)).
    + apply real_le_plus_compat;
        [exact (tw_wT_le_E2invN T Ht x) | apply real_le_refl].
    + exact (tw_ring_sub_mult (tw_E2 T Ht) tw_unif_dist).
  - apply (tw_le_eq_l (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))
             (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                tw_unif_dist)
             (real_opp (real_minus_r (tw_wT T Ht x) tw_unif_dist))).
    + apply (real_le_trans (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))
               (real_plus tw_unif_dist
                  (real_opp (real_mult (tw_E2L T Ht) tw_unif_dist)))
               (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                  tw_unif_dist)).
      * apply real_le_plus_compat.
        -- apply real_le_refl.
        -- apply tw_le_opp_compat.
           exact (tw_E2LinvN_le_wT T Ht x).
      * apply (real_le_trans
                 (real_plus tw_unif_dist
                    (real_opp (real_mult (tw_E2L T Ht) tw_unif_dist)))
                 (real_mult (real_plus real_one (real_opp (tw_E2L T Ht)))
                    tw_unif_dist)
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    tw_unif_dist)).
        -- exact (RealSetoid.real_eq_le _ _
                     (tw_ring_sub_mult_l (tw_E2L T Ht) tw_unif_dist)).
        -- exact (real_le_mult_compat
                    (real_plus real_one (real_opp (tw_E2L T Ht)))
                    (real_plus (tw_E2 T Ht) (real_opp real_one))
                    tw_unif_dist HinvN
                    (tw_one_minus_exp_le (tw_u2 T Ht) (tw_u2_pos T Ht))).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_opp (real_minus_r (tw_wT T Ht x) tw_unif_dist))
               (real_plus (real_opp (tw_wT T Ht x))
                  (real_opp (real_opp tw_unif_dist)))
               (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))).
      * apply real_opp_plus.
      * apply (real_eq_trans
                 (real_plus (real_opp (tw_wT T Ht x))
                    (real_opp (real_opp tw_unif_dist)))
                 (real_plus (real_opp (tw_wT T Ht x)) tw_unif_dist)
                 (real_plus tw_unif_dist (real_opp (tw_wT T Ht x)))).
        -- apply (RealSetoid.real_eq_plus_compat
                     (real_opp (tw_wT T Ht x))
                     (real_opp (real_opp tw_unif_dist))
                     (real_opp (tw_wT T Ht x)) tw_unif_dist
                     (real_eq_refl _) (real_opp_opp tw_unif_dist)).
        -- apply real_plus_comm.
Qed.

(* ---------- 7.6 求和完成：tv_unif ≤ e^{2Δ/T} − 1 ---------- *)

Lemma tv_unif_le : forall T Ht,
  real_le (tv_unif T Ht) (real_plus (tw_E2 T Ht) (real_opp real_one)).
Proof.
  intros T Ht.
  assert (Hmid : real_le
                   (real_mult (real_of_nat (length states))
                      (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                         (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos)))
                   (real_plus (tw_E2 T Ht) (real_opp real_one))).
  { apply (RealSetoid.real_eq_le).
    apply (real_eq_trans
             (real_mult (real_of_nat (length states))
                (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                   (real_inv_pos (real_of_nat (length states))
                      tw_states_len_pos)))
             (real_mult
                (real_mult (real_of_nat (length states))
                   (real_plus (tw_E2 T Ht) (real_opp real_one)))
                (real_inv_pos (real_of_nat (length states))
                   tw_states_len_pos))
             (real_plus (tw_E2 T Ht) (real_opp real_one))).
    - apply real_mult_assoc.
    - apply (real_eq_trans
               (real_mult
                  (real_mult (real_of_nat (length states))
                     (real_plus (tw_E2 T Ht) (real_opp real_one)))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_mult
                  (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                     (real_of_nat (length states)))
                  (real_inv_pos (real_of_nat (length states))
                     tw_states_len_pos))
               (real_plus (tw_E2 T Ht) (real_opp real_one))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_mult (real_of_nat (length states))
                    (real_plus (tw_E2 T Ht) (real_opp real_one)))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    (real_of_nat (length states)))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)
                 (real_mult_comm (real_of_nat (length states))
                    (real_plus (tw_E2 T Ht) (real_opp real_one)))
                 (real_eq_refl _)).
      + apply (real_eq_trans
                 (real_mult
                    (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                       (real_of_nat (length states)))
                    (real_inv_pos (real_of_nat (length states))
                       tw_states_len_pos))
                 (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                    (real_mult (real_of_nat (length states))
                       (real_inv_pos (real_of_nat (length states))
                          tw_states_len_pos)))
                 (real_plus (tw_E2 T Ht) (real_opp real_one))).
        * apply real_eq_sym. apply real_mult_assoc.
        * apply (real_eq_trans
                   (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                      (real_mult (real_of_nat (length states))
                         (real_inv_pos (real_of_nat (length states))
                            tw_states_len_pos)))
                   (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                      real_one)
                   (real_plus (tw_E2 T Ht) (real_opp real_one))).
          -- apply (RealSetoid.real_eq_mult_compat
                       (real_plus (tw_E2 T Ht) (real_opp real_one))
                       (real_mult (real_of_nat (length states))
                          (real_inv_pos (real_of_nat (length states))
                             tw_states_len_pos))
                       (real_plus (tw_E2 T Ht) (real_opp real_one)) real_one
                       (real_eq_refl _)
                       (real_inv_pos_correct (real_of_nat (length states))
                          tw_states_len_pos)).
          -- apply real_mult_one. }
  apply (real_le_trans (tv_unif T Ht)
           (real_mult (real_of_nat (length states))
              (real_mult (real_plus (tw_E2 T Ht) (real_opp real_one))
                 (real_inv_pos (real_of_nat (length states))
                    tw_states_len_pos)))
           (real_plus (tw_E2 T Ht) (real_opp real_one))).
  - unfold tv_unif. apply tw_sum_le_const.
    intros x _. apply tw_h_le.
  - exact Hmid.
Qed.

(* ---------- 7.7 主定理：量词翻转 ---------- *)

(*   T₂ := 2Δ·inv(cw_log(1+eps)) + 1 > 0；
     ⟹ tv_unif ≤ e^{2Δ/T} − 1 ≤ (1+eps) − 1 = eps。 *)
Theorem temp_window_T_infty :
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun T2 => And (real_lt real_zero T2)
         (forall (T : Real) (Ht : real_lt real_zero T), real_lt T2 T ->
          real_le (tv_unif T Ht) eps)).
Proof.
  intros eps Heps.
  pose (U := real_plus real_one eps).
  
  assert (HU1 : real_lt real_one U).
  { apply (real_eq_lt_lt real_one (real_plus real_zero real_one) U).
    - apply (real_eq_trans real_one (real_plus real_one real_zero)
               (real_plus real_zero real_one)).
      + apply real_eq_sym. apply real_plus_zero.
      + apply real_plus_comm.
    - apply (real_lt_eq_lt (real_plus real_zero real_one)
               (real_plus eps real_one) U).
      + exact (real_lt_plus_compat_lt_le real_zero eps real_one real_one
                 Heps (real_le_refl real_one)).
      + apply real_plus_comm. }
  assert (HUpos : real_lt real_zero U)
    by exact (real_lt_trans real_zero real_one U real_lt_zero_one HU1).
  assert (HL0 : real_lt real_zero (cw_log U HUpos)).
  { apply (real_eq_lt_lt real_zero (cw_log real_one real_lt_zero_one)
             (cw_log U HUpos)).
    - apply real_eq_sym. apply log_inv_one_thm.
    - exact (real_log_lt_mono real_one U real_lt_zero_one HUpos HU1). }
  pose (L := cw_log U HUpos).
  pose (invL := real_inv_pos L HL0).
  pose (twoD := real_plus Delta Delta).
  assert (H2D : real_lt real_zero twoD)
    by (apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero) twoD);
        [apply real_eq_sym; apply real_plus_zero |
         exact (real_lt_plus_compat real_zero Delta real_zero Delta
                   Delta_pos Delta_pos)]).
  assert (HinvL : real_lt real_zero invL) by apply real_inv_pos_pos.
  assert (H2DinvL : real_lt real_zero (real_mult twoD invL))
    by (apply (real_mult_pos_compat twoD invL); [exact H2D | exact HinvL]).
  exists (real_plus (real_mult twoD invL) real_one).
  split.
  - (* T₂ = 2Δ·invL + 1 > 0：0 < 1 ≤ T₂ *)
    apply (real_lt_le_trans real_zero real_one
             (real_plus (real_mult twoD invL) real_one) real_lt_zero_one).
    apply (tw_le_eq_l (real_plus real_zero real_one)
             (real_plus (real_mult twoD invL) real_one) real_one).
    + apply real_le_plus_compat.
      * apply tw_lt_le. exact H2DinvL.
      * apply real_le_refl.
    + apply (real_eq_trans real_one (real_plus real_one real_zero)
               (real_plus real_zero real_one)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply real_plus_comm.
  - intros T Ht HT2T.
    (* T·L 与 (2Δ+L) 的竞争：T₂·L == 2Δ + L *)
    assert (Ha : real_lt (real_mult (real_plus (real_mult twoD invL) real_one) L)
                   (real_mult T L))
      by exact (real_mult_lt_compat
                  (real_plus (real_mult twoD invL) real_one) T L HT2T HL0).
    assert (Hb : real_eq (real_mult (real_plus (real_mult twoD invL) real_one) L)
                           (real_plus twoD L)).
    { apply (real_eq_trans
               (real_mult (real_plus (real_mult twoD invL) real_one) L)
               (real_plus (real_mult twoD (real_mult L invL)) L)
               (real_plus twoD L)).
      - apply (real_eq_trans
                 (real_mult (real_plus (real_mult twoD invL) real_one) L)
                 (real_mult L (real_plus (real_mult twoD invL) real_one))
                 (real_plus (real_mult twoD (real_mult L invL)) L)).
        + apply real_mult_comm.
        + exact (tw_ring_t2 Delta L invL).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_mult twoD (real_mult L invL)) L twoD L).
        + apply (real_eq_trans (real_mult twoD (real_mult L invL))
                   (real_mult twoD real_one) twoD).
          * apply (RealSetoid.real_eq_mult_compat twoD (real_mult L invL)
                     twoD real_one (real_eq_refl twoD)
                     (real_inv_pos_correct L HL0)).
          * apply real_mult_one.
        + apply real_eq_refl. }
    assert (Hc : real_lt (real_plus twoD L) (real_mult T L))
      by exact (real_eq_lt_lt (real_plus twoD L)
                  (real_mult (real_plus (real_mult twoD invL) real_one) L)
                  (real_mult T L) (real_eq_sym _ _ Hb) Ha).
    assert (HinvT : real_lt real_zero (real_inv_pos T Ht))
      by apply real_inv_pos_pos.
    assert (Hd : real_lt (real_mult (real_plus twoD L) (real_inv_pos T Ht))
                           (real_mult (real_mult T L) (real_inv_pos T Ht)))
      by exact (real_mult_lt_compat (real_plus twoD L) (real_mult T L)
                  (real_inv_pos T Ht) Hc HinvT).
    assert (He : real_eq (real_mult (real_mult T L) (real_inv_pos T Ht)) L).
    { apply (real_eq_trans
               (real_mult (real_mult T L) (real_inv_pos T Ht))
               (real_mult (real_mult T (real_inv_pos T Ht)) L) L).
      - apply tw_ring_abc_acb.
      - apply (real_eq_trans
                 (real_mult (real_mult T (real_inv_pos T Ht)) L)
                 (real_mult real_one L) L).
        + apply (RealSetoid.real_eq_mult_compat
                   (real_mult T (real_inv_pos T Ht)) L real_one L
                   (real_inv_pos_correct T Ht) (real_eq_refl L)).
        + apply tw_ring_mult_one_l. }
    assert (Hf : real_lt (real_mult (real_plus twoD L) (real_inv_pos T Ht)) L)
      by exact (real_lt_eq_lt (real_mult (real_plus twoD L)
                                   (real_inv_pos T Ht))
                  (real_mult (real_mult T L) (real_inv_pos T Ht)) L Hd He).
    (* (2Δ+L)·invT == 2Δ/T + L/T，且 L/T > 0 ⟹ 2Δ/T < L *)
    assert (HddT : real_eq (real_mult (real_plus twoD L) (real_inv_pos T Ht))
                             (real_plus (tw_u2 T Ht)
                                (real_mult L (real_inv_pos T Ht))))
      by exact (tw_ring_ddl Delta L (real_inv_pos T Ht)).
    assert (HLiT : real_lt real_zero (real_mult L (real_inv_pos T Ht)))
      by (apply (real_mult_pos_compat L (real_inv_pos T Ht));
          [exact HL0 | exact HinvT]).
    assert (Hh : real_lt (real_plus (tw_u2 T Ht)
                              (real_mult L (real_inv_pos T Ht))) L)
      by exact (real_eq_lt_lt (real_plus (tw_u2 T Ht)
                                (real_mult L (real_inv_pos T Ht)))
                  (real_mult (real_plus twoD L) (real_inv_pos T Ht)) L
                  (real_eq_sym _ _ HddT) Hf).
    assert (Hi : real_lt (tw_u2 T Ht) L).
    { apply (real_lt_trans (tw_u2 T Ht)
               (real_plus (tw_u2 T Ht) (real_mult L (real_inv_pos T Ht))) L).
      - apply tw_lt_plus_r_zero. exact HLiT.
      - exact Hh. }
    (* e^{2Δ/T} < e^L == 1 + eps *)
    assert (Hj : real_lt (tw_E2 T Ht) U)
      by exact (real_lt_eq_lt (tw_E2 T Ht) (cauchy_real_exp L) U
                  (cauchy_real_exp_mono (tw_u2 T Ht) L Hi)
                  (cw_log_exp_right U HUpos)).
    (* 完成：tv ≤ E2 − 1 ≤ U − 1 == eps *)
    apply (real_le_trans (tv_unif T Ht)
             (real_plus (tw_E2 T Ht) (real_opp real_one)) eps).
    + exact (tv_unif_le T Ht).
    + apply (tw_le_eq_r (real_plus (tw_E2 T Ht) (real_opp real_one))
               (real_plus U (real_opp real_one)) eps).
      * apply real_le_plus_compat; [exact (inl Hj) | apply real_le_refl].
      * exact (tw_ring_one_eps_minus eps).
Qed.

End TempWindow.
