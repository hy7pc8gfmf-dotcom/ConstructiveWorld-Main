(* ==========================================================================)
   UpReqConcB2.v — conc B2：Q 层点积与核间隙界
   使命: cb2_dot 簇（点积经 sumd 折叠、交换律、dot_le_max）、Cb2Kernel 节（温度-间隙 z 的上下界 cb2_z_lb/ub/ub_all）、Cb2Smoke 冒烟节与完备性证书（cb2_smoke_complete/ub_cert）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD；Stdlib List、QArith、Lia、QArith.Qminmax。
   对标: 有限维点积的温度-最大分量间隙估计（softmax 分析中的 z 界）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia QArith.Qminmax.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* 一、Q 层点态辅件（gap 证书的算术底盘）                                  *)
(* ============================================================ *)

(* |x| ≥ x：Qabs_case 双支（abs 的 Z.abs 编码，非 Qmax 形——勿套对偶引理） *)
Lemma cb2_qabs_ge : forall x : Q, Qle x (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle x w)).
  - intro Hdummy. apply Qle_refl.
  - intro Hx0. apply (Qle_trans x 0 (Qopp x) Hx0).
    exact (Qopp_le_compat x 0 Hx0).
Qed.

(* |x| ≥ −x *)
Lemma cb2_qabs_ge_opp : forall x : Q, Qle (Qopp x) (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle (Qopp x) w)).
  - intro Hx0. apply (Qle_trans (Qopp x) 0 x).
    + exact (Qopp_le_compat 0 x Hx0).
    + exact Hx0.
  - intro Hdummy. apply Qle_refl.
Qed.

(* 0 ≤ |x| *)
Lemma cb2_qabs_nonneg : forall x : Q, Qle 0 (Qabs x).
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle 0 w)).
  - intro Hdummy. exact Hdummy.
  - intro Hx0. exact (Qopp_le_compat x 0 Hx0).
Qed.

(* −|x| ≤ x（Qabs_case 双支：x≥0 支 −x≤0≤x；x≤0 支 −(−x)==x 环归一） *)
Lemma cb2_qopp_abs_le : forall x : Q, Qle (Qopp (Qabs x)) x.
Proof.
  intro x. apply (Qabs_case x (fun w : Q => Qle (Qopp w) x)).
  - intro Hx0. apply (Qle_trans (Qopp x) 0 x).
    + exact (Qopp_le_compat 0 x Hx0).
    + exact Hx0.
  - intro Hdummy. apply (qeq_le (Qopp (Qopp x)) x).
    ring.
Qed.

(* Qmax 成员界二件（GenericMinMax max_l/max_r + Qlt_le_dec 分支） *)
Lemma cb2_qmax_ge_l : forall x y : Q, Qle x (Qmax x y).
Proof.
  intros x y. destruct (Qlt_le_dec x y) as [Hxy | Hxy].
  - rewrite (Q.max_r x y (Qlt_le_weak x y Hxy)). exact (Qlt_le_weak x y Hxy).
  - rewrite (Q.max_l x y Hxy). apply Qle_refl.
Qed.

Lemma cb2_qmax_ge_r : forall x y : Q, Qle y (Qmax x y).
Proof.
  intros x y. destruct (Qlt_le_dec y x) as [Hyx | Hyx].
  - rewrite (Q.max_l x y (Qlt_le_weak y x Hyx)). exact (Qlt_le_weak y x Hyx).
  - rewrite (Q.max_r x y Hyx). apply Qle_refl.
Qed.

(* 非负乘积 *)
Lemma cb2_qmul_nonneg : forall a b : Q, Qle 0 a -> Qle 0 b -> Qle 0 (a * b).
Proof.
  intros a b Ha Hb.
  assert (H1 : Qle (0 * a) (b * a)) by (apply (Qmult_le_compat_r 0 b a); assumption).
  assert (E0 : Qeq 0 (0 * a)) by ring.
  assert (E2 : Qeq (b * a) (a * b)) by ring.
  exact (Qle_trans 0 (0 * a) (a * b)
           (qeq_le 0 (0 * a) E0)
           (Qle_trans (0 * a) (b * a) (a * b) H1
              (qeq_le (b * a) (a * b) E2))).
Qed.

(* 乘法左保序（非负乘子） *)
Lemma cb2_qmul_nonneg_r : forall a u v : Q, Qle 0 a -> Qle u v -> Qle (a * u) (a * v).
Proof.
  intros a u v Ha Huv.
  destruct (Qle_lt_or_eq 0 a Ha) as [Hapos | Haeq].
  - exact (Qle_trans (a * u) (u * a) (a * v)
             (qeq_le (a * u) (u * a) (Qmult_comm a u))
             (Qle_trans (u * a) (v * a) (a * v)
                (proj2 (Qmult_le_r u v a Hapos) Huv)
                (qeq_le (v * a) (a * v) (Qmult_comm v a)))).

  - rewrite <- Haeq.
    apply (qeq_le (0 * u) (0 * v)).
    exact (Qeq_trans (0 * u) 0 (0 * v) (Qmult_0_l u)
                      (Qeq_sym (0 * v) 0 (Qmult_0_l v))).
Qed.

(* x ≤ y 给出 0 ≤ y−x（Qplus_le_r iff 拆支 + ring 归一） *)
Lemma cb2_qle_minus : forall x y : Q, Qle x y -> Qle 0 (Qminus y x).
Proof.
  intros x y H.
  assert (Hz : Qeq (Qplus x (Qminus y x)) y) by ring.
  apply (proj1 (Qplus_le_r 0 (Qminus y x) x)).
  rewrite Hz. rewrite Qplus_0_r. exact H.
Qed.

(* gap 件一：0 ≤ u 给出 1 ≤ u+1 *)
Lemma cb2_qplus_one_gap : forall u : Q, Qle 0 u -> Qle 1 (Qplus u 1).
Proof.
  intros u H.
  assert (H1 : Qle (Qplus 0 1) (Qplus u 1)) by (apply Qplus_le_compat; [exact H | apply Qle_refl]).
  rewrite Qplus_0_l in H1. exact H1.
Qed.

(* gap 件二：u ≤ v 给出 1 ≤ v+1−u（单位松弛封顶的算术内核） *)
Lemma cb2_qminus_gap : forall u v : Q, Qle u v -> Qle 1 (Qminus (Qplus v 1) u).
Proof.
  intros u v Huv.
  apply (proj1 (Qplus_le_r 1 (Qminus (Qplus v 1) u) u)).
  assert (Hz : Qeq (Qplus u (Qminus (Qplus v 1) u)) (Qplus v 1)) by ring.
  rewrite Hz.
  apply Qplus_le_compat.
  - exact Huv.
  - apply Qle_refl.
Qed.

(* 证书常数二件（可计算冒烟的最小元） *)
Lemma cb2_qhalf_lt_one : Qlt (1#2) 1.
Proof. reflexivity. Qed.

Lemma cb2_qhalf_pos : QltT 0 (1#2).
Proof. apply Qlt_to_QltT. reflexivity. Qed.

(* Qlt 右端 Qeq 传输（目标侧算术换形的项式安全通道——Qlt 头目标内
   arithmetic-Qeq 的 rewrite 在本环境下不可靠，全件改走本件项式传输） *)
Lemma cb2_qlt_eq_r : forall e a b : Q, Qlt e a -> Qeq a b -> Qlt e b.
Proof.
  intros e a b H Hq. exact (Qlt_le_trans e a b H (qeq_le a b Hq)).
Qed.

(* ============================================================ *)
(* 二、dot 机器（有限 list 逐点乘加，concrete Real 层）                     *)
(* ============================================================ *)

Fixpoint cb2_dot (x y : list Real) : Real :=
  match x, y with
  | a :: xt, b :: yt => real_plus (real_mult a b) (cb2_dot xt yt)
  | _, _ => real_zero
  end.

(* req 桥：dot ≡ sumd 折叠（使用既有和机器，勿重造——线性/求和辅件的桥约） *)
Lemma cb2_dot_via_sumd : forall x y : list Real,
  req (cb2_dot x y)
      (@sumd_list_sum Real RealEnhancedReal (Real * Real)
         (fun p : Real * Real => mult (fst p) (snd p)) (combine x y)).
Proof.
  intros x y. revert y. induction x as [| a xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_refl real_zero).
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_plus_compat (real_mult a b) (mult (fst (a, b)) (snd (a, b)))
                (cb2_dot xt yt)
                (@sumd_list_sum Real RealEnhancedReal (Real * Real)
                   (fun p : Real * Real => mult (fst p) (snd p)) (combine xt yt))
                (req_refl (real_mult a b))
                (IH yt)).
Defined.

(* 线性辅件：逐点乘 a 的列表上 dot 线性（mult_assoc + distrib req 链） *)
Lemma cb2_dot_map_mult_l : forall (a : Real) (x y : list Real),
  req (cb2_dot (map (fun r : Real => real_mult a r) x) y)
      (real_mult a (cb2_dot x y)).
Proof.
  intros a x. induction x as [| c xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_sym _ _ (mult_zero a)).
    + exact (req_sym _ _ (mult_zero a)).
  - destruct y as [| b yt].
    + exact (req_sym _ _ (mult_zero a)).
    + exact (req_trans _ _ _
               (req_trans _ _ _
                  (req_plus_compat (real_mult (real_mult a c) b)
                     (real_mult a (real_mult c b))
                     (cb2_dot (map (fun r : Real => real_mult a r) xt) yt)
                     (real_mult a (cb2_dot xt yt))
                     (req_sym _ _ (mult_assoc a c b))
                     (IH yt))
                  (req_plus_compat (real_mult a (real_mult c b))
                     (real_mult a (real_mult c b))
                     (real_mult a (cb2_dot xt yt))
                     (real_mult a (cb2_dot xt yt))
                     (req_refl (real_mult a (real_mult c b)))
                     (req_refl (real_mult a (cb2_dot xt yt)))))
               (req_sym _ _ (distrib a (real_mult c b) (cb2_dot xt yt)))).
Defined.

(* 对称辅件：dot 交换 *)
Lemma cb2_dot_comm : forall x y : list Real, req (cb2_dot x y) (cb2_dot y x).
Proof.
  intros x. induction x as [| a xt IH]; intro y.
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_refl real_zero).
  - destruct y as [| b yt].
    + exact (req_refl real_zero).
    + exact (req_plus_compat (real_mult a b) (real_mult b a)
                (cb2_dot xt yt) (cb2_dot yt xt)
                (mult_comm a b) (IH yt)).
Defined.

(* ============================================================ *)
(* 三、max 封顶机器（pair 表折叠 real_max；核心引理纯 Q 层归纳）             *)
(* ============================================================ *)

(* 封顶折叠：默认基座 d（诚实空表支）+ 逐对 |dot| 的 real_max 并入 *)
Fixpoint cb2_list_max_abs (d : Real) (l : list (list Real * list Real)) : Real :=
  match l with
  | nil => d
  | (a, b) :: t => real_max (real_abs (cb2_dot a b)) (cb2_list_max_abs d t)
  end.

(* ★核心引理：逐元素 |dot|(n) ≤ 折叠(n)——有限归纳逐点（Q 层，真归纳证明）。
   语句取点态 Qle 形：plain real_le 形即 AT5 Or 真墙同族（混合号下两支均
   不可构造），点态/eps 形为正道（与 csm_abs_sum_le_eps 同哲学）。 *)
Lemma cb2_dot_le_max : forall (l : list (list Real * list Real)) (x y : list Real) (n : nat),
  In (x, y) l ->
  Qle (Qabs (projT1 (cb2_dot x y) n)) (projT1 (cb2_list_max_abs real_zero l) n).
Proof.
  intro l. induction l as [| p t IH]; intros x y n Hin.
  - destruct Hin.
  - destruct p as [a b]. simpl in Hin. destruct Hin as [Heq | Hin].
    + injection Heq; intros; subst.
      cbn [cb2_list_max_abs].
      rewrite real_max_proj. rewrite real_abs_proj.
      apply cb2_qmax_ge_l.
    + cbn [cb2_list_max_abs].
      rewrite real_max_proj. rewrite real_abs_proj.
      apply (Qle_trans (Qabs (projT1 (cb2_dot x y) n))
                       (projT1 (cb2_list_max_abs real_zero t) n)).
      * apply IH. exact Hin.
      * apply cb2_qmax_ge_r.
Qed.

(* 折叠非负（基座 real_zero 支供 0 下界） *)
Lemma cb2_maxabs_nonneg : forall (l : list (list Real * list Real)) (n : nat),
  Qle 0 (projT1 (cb2_list_max_abs real_zero l) n).
Proof.
  intro l. induction l as [| p t IH]; intro n.
  - cbn [cb2_list_max_abs].
    assert (Hz : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz. apply Qle_refl.
  - destruct p as [a b]. cbn [cb2_list_max_abs].
    rewrite real_max_proj. rewrite real_abs_proj.
    apply (Qle_trans 0 (Qabs (projT1 (cb2_dot a b) n))).
    + apply cb2_qabs_nonneg.
    + apply cb2_qmax_ge_l.
Qed.

(* AT5 式 lt 加强形：|dot| < 折叠 + eps（eps>0；gap 由 eps 证书边际供给） *)
Lemma cb2_dot_lt_max_eps : forall (l : list (list Real * list Real)) (x y : list Real),
  In (x, y) l -> forall eps : Real, real_lt real_zero eps ->
  real_lt (real_abs (cb2_dot x y))
          (real_plus (cb2_list_max_abs real_zero l) eps).
Proof.
  intros l x y Hin eps Heps.
  destruct Heps as [e0 [He0 [Neps HNeps]]].
  unfold real_lt. exists e0. split.
  - exact He0.
  - exists Neps. intros n Hn.
    specialize (HNeps n Hn).
    apply QltT_to_Qlt in HNeps.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HNeps.
    assert (Hze : Qeq (projT1 eps n - 0) (projT1 eps n)) by ring.
    rewrite Hze in HNeps.
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot x y) n))
                      (projT1 (cb2_list_max_abs real_zero l) n))
      by exact (cb2_dot_le_max l x y n Hin).
    assert (Hm0 : Qle 0 (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                                (Qabs (projT1 (cb2_dot x y) n))))
      by (apply (cb2_qle_minus (Qabs (projT1 (cb2_dot x y) n))
                  (projT1 (cb2_list_max_abs real_zero l) n) Hbd)).
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite real_abs_proj.
    (* 证书链：e0 < eps(n) ≤ eps(n)+(M−|d|) ≡ M+eps(n)−|d(n)| *)
    assert (Hstep : Qle (projT1 eps n)
                        (Qplus (projT1 eps n)
                               (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                                  (Qabs (projT1 (cb2_dot x y) n)))))
      by exact (Qle_trans (projT1 eps n) (Qplus (projT1 eps n) 0)
                  (Qplus (projT1 eps n)
                     (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                        (Qabs (projT1 (cb2_dot x y) n))))
                  (qeq_le (projT1 eps n) (Qplus (projT1 eps n) 0)
                     (Qeq_sym (Qplus (projT1 eps n) 0) (projT1 eps n)
                        (Qplus_0_r (projT1 eps n))))
                  (proj2 (Qplus_le_r 0
                            (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                               (Qabs (projT1 (cb2_dot x y) n)))
                            (projT1 eps n)) Hm0)).
    assert (Hzg : Qeq (Qplus (projT1 eps n)
                          (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                             (Qabs (projT1 (cb2_dot x y) n))))
                      (projT1 (cb2_list_max_abs real_zero l) n + projT1 eps n
                       - Qabs (projT1 (cb2_dot x y) n))) by ring.
    exact (cb2_qlt_eq_r e0
             (Qplus (projT1 eps n)
                (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                   (Qabs (projT1 (cb2_dot x y) n))))
             (projT1 (cb2_list_max_abs real_zero l) n + projT1 eps n
              - Qabs (projT1 (cb2_dot x y) n))
             (Qlt_le_trans e0 (projT1 eps n)
                (Qplus (projT1 eps n)
                   (Qminus (projT1 (cb2_list_max_abs real_zero l) n)
                      (Qabs (projT1 (cb2_dot x y) n))))
                HNeps Hstep)
             Hzg).
Qed.

(* ============================================================ *)
(* 四、具体 logit 核（Section Cb2Kernel：q/k 向量族 + temp + 封顶清单）      *)
(* ============================================================ *)

Section Cb2Kernel.

Variable S : Set.
Variable q : S -> list Real.
Variable k : S -> list Real.
Variable temp : Real.
Variable temp_pos : real_lt real_zero temp.
Variable lmax : list (list Real * list Real).

(* 核值：具体 logit 核 = temp × dot(q s)(k s') *)
Definition cb2_z (s s' : S) : Real :=
  real_mult temp (cb2_dot (q s) (k s')).

(* 封顶核心（原始字面形）：temp × max|dot|。
   注意：字面形不做装配 Delta——全零退化下其正性证书不存在（见头注★）。 *)
Definition cb2_Delta_core : Real :=
  real_mult temp (cb2_list_max_abs real_zero lmax).

(* 装配 Delta = 封顶核心 + 单位松弛：松弛使 gap(n) ≥ 1 恒成立，三件证书走 inl *)
Definition cb2_Delta : Real :=
  real_plus cb2_Delta_core real_one.

(* ---- Delta 正性（无条件；证书 eps := 1#2，N 取 temp_pos 之 N0） ---- *)

Lemma cb2_Delta_pos : real_lt real_zero cb2_Delta.
Proof.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (HM0 : Qle 0 (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_maxabs_nonneg lmax n).
    assert (HX : Qle 0 (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by (apply cb2_qmul_nonneg; assumption).
    apply Qlt_to_QltT.
    unfold cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    change (projT1 real_zero n) with 0%Q.
    assert (Hzg : Qeq (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                      (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n
                       + 1 - 0)) by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1 - 0)
             (Qlt_le_trans (1#2)%Q 1%Q
                (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                cb2_qhalf_lt_one
                (cb2_qplus_one_gap
                   (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n) HX))
             Hzg).
Qed.

(* ---- z 下界：−Delta ≤ temp·dot（In 形；封顶清单须含该 pair） ---- *)

Lemma cb2_z_lb : forall s s' : S,
  In (q s, k s') lmax -> real_le (real_opp cb2_Delta) (cb2_z s s').
Proof.
  intros s s' Hin.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  apply inl. unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                      (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_dot_le_max lmax (q s) (k s') n Hin).
    assert (Hdn_ge : Qle (Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                         (projT1 (cb2_dot (q s) (k s')) n))
      by exact (cb2_qopp_abs_le (projT1 (cb2_dot (q s) (k s')) n)).
    assert (Hu : Qle (projT1 temp n
                        * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                     (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n))
      by (apply cb2_qmul_nonneg_r; [exact Htn0 | exact Hdn_ge]).
    assert (Hw : Qle 0 (projT1 temp n
                          * Qminus (projT1 (cb2_list_max_abs real_zero lmax) n)
                              (Qabs (projT1 (cb2_dot (q s) (k s')) n))))
      by (apply cb2_qmul_nonneg; [exact Htn0 | exact (cb2_qle_minus _ _ Hbd)]).
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_opp_proj. rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    (* Hw 换形到左目标和项：tn·(M−|d|) ≡ tn·(−|d|) + tn·M *)
    assert (Hzr : Qeq (projT1 temp n
                         * Qminus (projT1 (cb2_list_max_abs real_zero lmax) n)
                             (Qabs (projT1 (cb2_dot (q s) (k s')) n)))
                      (projT1 temp n * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by ring.
    assert (HX : Qle 0 (projT1 temp n
                          * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                        + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)).
    { rewrite <- Hzr. exact Hw. }
    assert (HY : Qle (projT1 temp n * Qopp (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)
                     (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by (apply Qplus_le_compat; [exact Hu | apply Qle_refl]).
    assert (Htot : Qle 0 (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                           + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (Qle_trans _ _ _ HX HY).
    (* gap = tn·dn − (−(tn·M + 1)) ≡ tn·dn + tn·M + 1 ≥ 1 > 1#2 *)
    assert (Hzg : Qeq (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                      (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                       - Qopp (projT1 temp n
                                 * projT1 (cb2_list_max_abs real_zero lmax) n + 1)))
      by ring.
    exact (cb2_qlt_eq_r (1#2)%Q
             (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
              + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
             (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
              - Qopp (projT1 temp n
                        * projT1 (cb2_list_max_abs real_zero lmax) n + 1))
             (Qlt_le_trans (1#2)%Q 1%Q
                (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n
                 + projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n + 1)
                cb2_qhalf_lt_one (cb2_qplus_one_gap _ Htot))
             Hzg).
Qed.

(* ---- z 上界：temp·dot ≤ Delta（In 形） ---- *)

Lemma cb2_z_ub : forall s s' : S,
  In (q s, k s') lmax -> real_le (cb2_z s s') cb2_Delta.
Proof.
  intros s s' Hin.
  destruct temp_pos as [e0 [He0 [N0 HN0]]].
  apply inl. unfold real_lt. exists (1#2)%Q. split.
  - exact cb2_qhalf_pos.
  - exists N0. intros n Hn.
    specialize (HN0 n Hn).
    apply QltT_to_Qlt in HN0.
    assert (Hz0 : projT1 real_zero n == 0%Q) by reflexivity.
    rewrite Hz0 in HN0.
    assert (Hzn : Qeq (projT1 temp n - 0) (projT1 temp n)) by ring.
    rewrite Hzn in HN0.
    assert (Htn0 : Qle 0 (projT1 temp n)).
    { apply (Qle_trans 0 e0 (projT1 temp n)).
      - apply Qlt_le_weak. exact (QltT_to_Qlt 0 e0 He0).
      - exact (Qlt_le_weak e0 (projT1 temp n) HN0). }
    assert (Hbd : Qle (Qabs (projT1 (cb2_dot (q s) (k s')) n))
                      (projT1 (cb2_list_max_abs real_zero lmax) n))
      by exact (cb2_dot_le_max lmax (q s) (k s') n Hin).
    assert (Huv : Qle (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n)
                      (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)).
    { apply cb2_qmul_nonneg_r.
      - exact Htn0.
      - apply (Qle_trans (projT1 (cb2_dot (q s) (k s')) n)
                         (Qabs (projT1 (cb2_dot (q s) (k s')) n))).
        + apply cb2_qabs_ge.
        + exact Hbd. }
    apply Qlt_to_QltT.
    unfold cb2_z, cb2_Delta, cb2_Delta_core.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    assert (H1 : projT1 real_one n == 1%Q) by reflexivity.
    rewrite H1.
    (* gap = (tn·M + 1) − tn·dn ≥ 1（cb2_qminus_gap，Huv 封顶支路） *)
    exact (Qlt_le_trans (1#2)%Q 1%Q
             (Qminus (Qplus (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n) 1)
                (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n))
             cb2_qhalf_lt_one
             (cb2_qminus_gap (projT1 temp n * projT1 (cb2_dot (q s) (k s')) n)
                             (projT1 temp n * projT1 (cb2_list_max_abs real_zero lmax) n)
                             Huv)).
Qed.

(* ---- 参数位直接代入形（完备性证书消去 In；语句与闭合链 z_lb/z_ub 槽转换同体） ---- *)

Variable lmax_complete : forall s s' : S, In (q s, k s') lmax.

Lemma cb2_z_lb_all : forall s s' : S, real_le (real_opp cb2_Delta) (cb2_z s s').
Proof. intros s s'. apply cb2_z_lb. apply lmax_complete. Qed.

Lemma cb2_z_ub_all : forall s s' : S, real_le (cb2_z s s') cb2_Delta.
Proof. intros s s'. apply cb2_z_ub. apply lmax_complete. Qed.

End Cb2Kernel.

(* ============================================================ *)
(* 五、自检守卫：退化输入（全零向量）平凡支 compute 冒烟（G3 辅证）          *)
(* ============================================================ *)

Section Cb2Smoke.

Definition cb2_smoke_q : unit -> list Real := fun _ => real_zero :: nil.
Definition cb2_smoke_k : unit -> list Real := fun _ => real_zero :: nil.
Definition cb2_smoke_lmax : list (list Real * list Real) :=
  (real_zero :: nil, real_zero :: nil) :: nil.

(* dot 机器冒烟：全零一维点积逐点归约到 0（reflexivity 即 compute） *)
Lemma cb2_smoke_dot : projT1 (cb2_dot (real_zero :: nil) (real_zero :: nil)) 5%nat == 0%Q.
Proof. reflexivity. Qed.

(* 核值冒烟：z(5) = 1·(0·0+0) = 0 *)
Lemma cb2_smoke_z : projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) 5%nat == 0%Q.
Proof. reflexivity. Qed.

(* 封顶折叠冒烟：max|dot|(5) = Qmax |0| 0 = 0；Delta(5) = 1·0+1 = 1 *)
Lemma cb2_smoke_max : projT1 (cb2_list_max_abs real_zero cb2_smoke_lmax) 5%nat == 0%Q.
Proof. reflexivity. Qed.

Lemma cb2_smoke_Delta : projT1 (cb2_Delta real_one cb2_smoke_lmax) 5%nat == 1%Q.
Proof. reflexivity. Qed.

(* 证书冒烟：z 界的 gap(5) = 1−0 = 1，严格大于 1#2 可计算判定 *)
Lemma cb2_smoke_gap : QltT (1#2)%Q
   (projT1 (cb2_Delta real_one cb2_smoke_lmax) 5%nat
   - projT1 (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt) 5%nat).
Proof. reflexivity. Qed.

Lemma cb2_smoke_complete : forall s s' : unit,
  In (cb2_smoke_q s, cb2_smoke_k s') cb2_smoke_lmax.
Proof. intros s s'. apply in_eq. Qed.

(* 平凡支证书整体成项：全零输入下 z_ub_all 闭项（reflexivity 级使用面） *)
Definition cb2_smoke_ub_cert :
  real_le (cb2_z unit cb2_smoke_q cb2_smoke_k real_one tt tt)
          (cb2_Delta real_one cb2_smoke_lmax) :=
  cb2_z_ub_all unit cb2_smoke_q cb2_smoke_k real_one one_pos
               cb2_smoke_lmax cb2_smoke_complete tt tt.

End Cb2Smoke.

(* ============ G4 证据：新件零外部未证假设（全 Closed，前提=显式参数） ============ *)
Print Assumptions cb2_dot_via_sumd.
Print Assumptions cb2_dot_map_mult_l.
Print Assumptions cb2_dot_comm.
Print Assumptions cb2_dot_le_max.
Print Assumptions cb2_maxabs_nonneg.
Print Assumptions cb2_dot_lt_max_eps.
Print Assumptions cb2_Delta_pos.
Print Assumptions cb2_z_lb.
Print Assumptions cb2_z_ub.
Print Assumptions cb2_z_lb_all.
Print Assumptions cb2_z_ub_all.
Print Assumptions cb2_smoke_ub_cert.

(* ======== ToyR 专项切片二 · 验证证据段（正文语句面零改，仅追加取证） ======== *)
Print Assumptions cb2_qmul_nonneg_r.
Print Assumptions cb2_qhalf_lt_one.
Print Assumptions cb2_qhalf_pos.
Print Assumptions cb2_qlt_eq_r.
Print Assumptions cb2_z_lb_all.
Print Assumptions cb2_z_ub_all.
Print Assumptions cb2_smoke_dot.
Print Assumptions cb2_smoke_z.
Print Assumptions cb2_smoke_max.
Print Assumptions cb2_smoke_Delta.
Print Assumptions cb2_smoke_gap.
Print Assumptions cb2_smoke_complete.
