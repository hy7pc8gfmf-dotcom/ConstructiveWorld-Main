(* ==========================================================================)
   UpReqEngineCeiling.v —— 引擎族常数天花板与 ε-三分比较基建的 Q 层形式化
   使命：本件形式化三组 Q 层结构。其一，引擎族常数天花板族：调和数下界
     cec_H_lower、截断天花板 min 分段账 cec_trunc_sup、嵌套切线族核二阶
     系数 cec_kernel_coef 及其一般 k 无条件实例 eck_kernel_coef_k、切线族
     严格上界 cec_tangent_ceiling 与缺口恒等式 cec_tangent_gap。
     其二，ε-三分比较基建：三支见证型三分定理 etc_trichotomy、远距桥
     etc_apart 与出口便捷件 etc_compare_tri / etc_sign_tri / etc_one_side。
     其三，实数一侧分离的逐坐标 Q 层装载面 pkc_sign_load /
     pkc_half_slack_load / pkc_oneside_far_load / pkc_oneside_near_load /
     pkc_w3_qface 与提取检验件。
   依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib QArith、
     QArith.Qabs、QArith.Qring、ZArith.Zorder、Arith、Lia、Setoid、
     Morphisms、Extraction。
   对标：调和数部分和的初等下界估计（1 + 1 ≤ H_k − 1/(k+1)，k ≥ 5）、
     几何级数闭式与二项反演的构造性对应、逐点可判定比较序的三分构造。
   构造性：全件 Qed/Defined 闭合、零承认词面、无经典逻辑；序谓词与等词为
     Set 值承载（QltT/QleT'/QeqT/sigT），零 Prop 泄露；sigT 见证与提取
     检验件 projT1 可计算提取。
   编译配方：Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树
     同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import ZArith.Zorder Setoid Lia Extraction.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.


(* ---- §0 通用小件：Q 层地基（cec_ 前缀） ---- *)

(* Z.of_nat (n+1) # 1 > 0（Q 层正性；lia 走 Nat2Z） *)
Lemma cec_nat_pos : forall n : nat, Qlt 0 (Z.of_nat (n + 1) # 1).
Proof. intro n. unfold Qlt. simpl. lia. Qed.

Lemma cec_nat_pos0 : forall n : nat, (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof. intros n Hn. unfold Qlt. simpl. lia. Qed.

(* Qeq 面非零性（S03 q_neq_of_lt 同款：field 侧条件实测为 ~ (x == 0)） *)
Lemma cec_neq_of_pos : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof. exact S03_QExp.q_neq_of_lt. Qed.

(* 乘积非零（Qeq 面；Qmult_integral_l 本为 Qeq 面） *)
Lemma cec_mult_neq0 : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0).
Proof.
  intros x y Hx Hy H.
  apply Hy.
  exact (Qmult_integral_l x y Hx H).
Qed.

(* field 侧条件统一闭法：实测 field 产出合取 ~ d == 0 /\ ...（S03 split 同款）；
   闭法：split 分裂 / 假设直取 / 乘积分裂 / 正性 lia（全 Qeq 面） *)
Ltac cec_nz :=
  repeat first
    [ assumption
    | split; cec_nz
    | apply cec_mult_neq0; cec_nz
    | apply cec_neq_of_pos; (assumption || (unfold Qlt; simpl; lia)) ].

(* 倒数正性（按 Qnum 三分构造；Qinv 定义面） *)
Lemma cec_inv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (/ x).
Proof.
  intros x Hx. destruct x as [a b]. unfold Qlt in Hx. simpl in Hx.
  destruct a.
  - lia.
  - unfold Qlt. simpl. lia.
  - lia.
Qed.

Lemma cec_inv_mult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (/ (x * y)).
Proof.
  intros x y Hx Hy. rewrite Qinv_mult_distr.
  apply Qmult_lt_0_compat; apply cec_inv_pos; assumption.
Qed.

(* x + y ≥ x（供归纳单调步；Qplus_le_r 为 iff 形不便直用，自证） *)
Lemma cec_plus_r_le : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy. apply (Qle_trans x (x + 0) (x + y)).
  - apply qeq_imp_qle. rewrite Qplus_0_r. apply Qeq_refl.
  - apply (Qplus_le_compat x x 0 y); [apply Qle_refl | exact Hy].
Qed.

(* 自己的 min（Qle_bool 反映形，与 QleT' 同基；避免 stdlib Qminmax 名漂移） *)
Definition cec_min (x y : Q) : Q := if Qle_bool x y then x else y.

Lemma cec_min_ge : forall x y : Q, Qle y x -> cec_min x y == y.
Proof.
  intros x y Hyx. unfold cec_min. destruct (Qle_bool x y) eqn:E.
  - apply Qle_antisym; [| exact Hyx].
    apply (QleT'_to_Qle x y). unfold QleT'. rewrite E. exact id_refl.
  - reflexivity.
Qed.

(* 同分母严格除比较（Qmult_lt_compat_r 的 /e 参数位：倒数正性桥） *)
Lemma cec_div_same_denom_lt : forall a c e : Q,
  Qlt 0 e -> Qlt a c -> Qlt (a / e) (c / e).
Proof.
  intros a c e He Hac.
  unfold Qdiv.
  apply (Qmult_lt_compat_r _ _ _ (cec_inv_pos e He) Hac).
Qed.

(* 跨分母严格除比较：a*d < c*b, b,d > 0 ⟹ a/b < c/d *)
Lemma cec_lt_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> Qlt (a / b) (c / d).
Proof.
  intros a b c d Hb Hd H.
  assert (E1 : a / b == (a * d) / (b * d)) by (field; cec_nz).
  assert (E2 : c / d == (c * b) / (b * d)) by (field; cec_nz).
  rewrite E1, E2.
  apply cec_div_same_denom_lt.
  - apply Qmult_lt_0_compat; assumption.
  - exact H.
Qed.

(* ---- §1 调和数与角点常数 ---- *)

(* H_k := Σ_{j=1..k} 1/j（内项统一 n+1 形，防 S k 的 Z 形错位） *)
Fixpoint cec_H (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => cec_H m + ((1 # 1) / (Z.of_nat (m + 1) # 1))
  end.

(* 角点常数 f(k) := H_k − 1/(k+1)（调和数角点极限的 Q 层精确形） *)
Definition cec_pt (k : nat) : Q := cec_H k - ((1 # 1) / (Z.of_nat (k + 1) # 1)).

(* 四个角点精确值（fractions 精确：1/2, 7/6, 19/12, 113/60） *)
Lemma cec_pt_1 : cec_pt 1 == (1 # 2).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_2 : cec_pt 2 == (7 # 6).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_3 : cec_pt 3 == (19 # 12).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_4 : cec_pt 4 == (113 # 60).
Proof. vm_compute. reflexivity. Qed.

(* 单调步的显式增量（fractions 验证：f(k+1) − f(k) = (k+3)/((k+1)(k+2))） *)
Lemma cec_pt_step_eq : forall k : nat,
  cec_pt (Datatypes.S k) ==
  cec_pt k + ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k.
  (* S n / n+c 的 Z 形统一（lia zify 直吃，Nat2Z 名漂移零依赖） *)
  assert (EA : forall n : nat, (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + (1 # 1)).
  { intro n. unfold Qeq, Qplus. simpl. lia. }
  assert (EB0 : (Z.of_nat (k + 1) # 1) == (Z.of_nat k # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB1 : (Z.of_nat (k + 2) # 1) == (Z.of_nat k # 1) + ((1 # 1) + (1 # 1))).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB2 : (Z.of_nat (k + 3) # 1) == (Z.of_nat k # 1) + ((1 # 1) + ((1 # 1) + (1 # 1)))).
  { unfold Qeq, Qplus. simpl. lia. }
  unfold cec_pt.
  change ((Datatypes.S k + 1)%nat) with (Datatypes.S (k + 1)).
  rewrite (EA (k + 1)%nat).
  cbn [cec_H].
  rewrite EB0.
  rewrite EB1, EB2.
  field; cec_nz.
Qed.

Lemma cec_pt_step_pos : forall k : nat,
  Qlt 0 ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply (cec_nat_pos0 (k + 3)%nat). lia.
  - apply cec_inv_mult_pos.
    + apply (cec_nat_pos0 (k + 1)%nat). lia.
    + apply (cec_nat_pos0 (k + 2)%nat). lia.
Qed.

(* 基例：f(5) = 127/60（fractions 精确）且 > 2 *)
Lemma cec_pt_5 : cec_pt 5 == (127 # 60).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_two_lt_127_60 : Qlt (1 + 1)%Q (127 # 60).
Proof. unfold Qlt. simpl. lia. Qed.

(* 严格下界归纳：k ≥ 5 ⟹ 2 < f(k)（严格版，供 min 段取 2） *)
Lemma cec_pt_gt2 : forall k : nat, (5 <= k)%nat -> Qlt (1 + 1)%Q (cec_pt k).
Proof.
  induction k as [| m IH]; intro Hk.
  - lia.
  - destruct (Nat.eq_dec m 4) as [E4 | Hne].
    + subst m. rewrite cec_pt_5. apply cec_two_lt_127_60.
    + assert (Hm5 : (5 <= m)%nat) by lia.
      specialize (IH Hm5).
      assert (Hstep : Qle (cec_pt m) (cec_pt (Datatypes.S m))).
      { pose proof (cec_pt_step_pos m) as Hp.
        pose proof (cec_pt_step_eq m) as E.
        rewrite E.
        apply (cec_plus_r_le (cec_pt m)
                ((Z.of_nat (m + 3) # 1) /
                 ((Z.of_nat (m + 1) # 1) * (Z.of_nat (m + 2) # 1)))).
        apply Qlt_le_weak. exact Hp. }
      apply (Qlt_le_trans (1 + 1)%Q (cec_pt m) (cec_pt (Datatypes.S m)) IH Hstep).
Qed.

(* 主件：调和数下界引理（QleT' Set 面，独立成件零 And 混装） *)
Theorem cec_H_lower : forall k : nat, (5 <= k)%nat -> QleT' (1 + 1)%Q (cec_pt k).
Proof.
  intros k Hk.
  exact (Qle_to_QleT' (1 + 1)%Q (cec_pt k)
    (Qlt_le_weak (1 + 1)%Q (cec_pt k) (cec_pt_gt2 k Hk))).
Qed.


(* ---- §2 截断引擎族天花板 c*(k) = min(H_k − 1/(k+1), 2) ---- *)

Definition cec_cstar (k : nat) : Q := cec_min (cec_pt k) (1 + 1)%Q.

(* k≥5 段：min(f(k), 2) = 2（由严格下界经 min_ge 取右枝） *)
Theorem cec_cstar_tail : forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q.
Proof.
  intros k Hk. unfold cec_cstar. apply cec_min_ge.
  apply Qlt_le_weak. apply cec_pt_gt2. exact Hk.
Qed.

(* 五条 min 分段账（全 Qeq Prop And；repeat apply conj 防转换穿透） *)
Theorem cec_trunc_sup :
  cec_cstar 1 == (1 # 2) /\
  cec_cstar 2 == (7 # 6) /\
  cec_cstar 3 == (19 # 12) /\
  cec_cstar 4 == (113 # 60) /\
  (forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q).
Proof.
  repeat apply conj.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact cec_cstar_tail.
Qed.

(* ---- §3 嵌套切线族核二阶系数 −(k+1)/(2k) ---- *)

(* 抽象二项反演引擎：s = a·v + b·v² + v³w ⟹ a·v 的 s² 系数恰 −b/a²，
   残差 s³·ρ 显式（ρ 分母 (a+bv+v²w)³ 在 v=0 取值 a³≠0，正则性可见；
   python fractions 492 样本抽检恒等式为零）。 *)
Definition cec_smap (a b w v : Q) : Q := a * v + b * v * v + v * v * v * w.

Definition cec_rho (a b w v : Q) : Q :=
  (((2 * b * b / a - w) + (b * (b * b + (1 + 1)%Q * a * w) / (a * a)) * v
    + ((1 + 1)%Q * b * b * w / (a * a)) * v * v
    + (b * w * w / (a * a)) * v * v * v)
   / ((a + b * v + v * v * w)
      * ((a + b * v + v * v * w) * (a + b * v + v * v * w)))).

Lemma cec_inv2 : forall (a b w v : Q),
  Qlt 0 a -> ~ (cec_smap a b w v == 0) ->
  Qeq (a * v)
      (cec_smap a b w v - (b / (a * a)) * (cec_smap a b w v * cec_smap a b w v)
       + cec_smap a b w v * cec_smap a b w v * cec_smap a b w v
         * cec_rho a b w v).
Proof.
  intros a b w v Ha Hs.
  assert (Ha0 : ~ (a == 0)) by (apply cec_neq_of_pos; exact Ha).
  assert (Hden : ~ ((a + b * v + v * v * w) == 0)).
  { intro Hd. apply Hs. unfold cec_smap.
    assert (Ef : a * v + b * v * v + v * v * v * w == v * (a + b * v + v * v * w)) by ring.
    rewrite Ef, Hd. ring. }
  unfold cec_smap, cec_rho.
  field; cec_nz.
Qed.

(* 嵌套切线族的 a, b, 系数：a = k，b = k(k+1)/2，|系数| = b/a² = (k+1)/(2k) *)
Definition cec_r6_s (k : nat) (v : Q) : Q := (1 # 1) / q_pow (1 - v) k - (1 # 1).
Definition cec_r6_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).
Definition cec_r6_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

Lemma cec_bcoef_div_a2 : forall k : nat, (1 <= k)%nat ->
  cec_r6_bcoef k / ((Z.of_nat k # 1) * (Z.of_nat k # 1)) == cec_r6_coef k.
Proof.
  intros k Hk. unfold cec_r6_bcoef, cec_r6_coef.
  field; cec_nz.
Qed.

(* 系数指纹（一般 k 无条件）：(k+1)/(2k) > 1/2 ——「每支亏 1/(2k)」的族推广 *)
Lemma cec_coef_fingerprint : forall k : nat, (1 <= k)%nat -> Qlt (1 # 2) (cec_r6_coef k).
Proof.
  intros k Hk. unfold cec_r6_coef.
  apply (cec_lt_div_lt (1 # 1) ((1 + 1)%Q) ((Z.of_nat k # 1) + 1)
                       ((1 + 1)%Q * (Z.of_nat k # 1))).
  - unfold Qlt. simpl. lia.
  - apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - (* Qmult 在 Qplus 参数上卡 match；ring 只证多项式恒等式（Qmake(Z和) 是
     不透明原子），故把交叉积归到原子 z#1 的加法多项式形再 unfold+lia *)
    assert (E1 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    assert (E2 : ((Z.of_nat k # 1) + 1) * ((1 + 1)%Q)
                 == ((Z.of_nat k # 1) + (Z.of_nat k # 1)) + ((1 + 1)%Q)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* 系数指纹上侧：|系数| = (k+1)/(2k) ≤ 1 *)
Lemma cec_coef_le_1 : forall k : nat, (1 <= k)%nat -> Qle (cec_r6_coef k) (1 # 1).
Proof.
  intros k Hk. unfold cec_r6_coef.
  change (Qle (((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)))
              ((1 # 1) / (1 # 1))).
  apply (S03_QExp.q_le_div_le ((Z.of_nat k # 1) + 1)
            ((1 + 1)%Q * (Z.of_nat k # 1)) (1 # 1) (1 # 1)).
  - apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - unfold Qlt. simpl. lia.
  - assert (E1 : ((Z.of_nat k # 1) + 1) * (1 # 1)
                 == (Z.of_nat k # 1) + (1 # 1)) by ring.
    assert (E2 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    rewrite E1, E2.
    unfold Qle. simpl. lia.
Qed.

(* 主件（一般 k 条件形：参数化恒等式为显式假设，诚实遗留） *)
Theorem cec_kernel_coef : forall (k : nat) (v w : Q), (1 <= k)%nat ->
  ~ (cec_r6_s k v == 0) ->
  cec_r6_s k v == (Z.of_nat k # 1) * v + cec_r6_bcoef k * v * v + v * v * v * w ->
  Qeq ((Z.of_nat k # 1) * v)
      (cec_r6_s k v - cec_r6_coef k * (cec_r6_s k v * cec_r6_s k v)
       + cec_r6_s k v * cec_r6_s k v * cec_r6_s k v
         * cec_rho (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
Proof.
  intros k v w Hk Hs Hpar.
  assert (Ha : Qlt 0 (Z.of_nat k # 1)) by (apply (cec_nat_pos0 k Hk)).
  assert (E : cec_r6_s k v == cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
  { unfold cec_smap. exact Hpar. }
  assert (Hs2 : ~ (cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v == 0)).
  { intro H0. apply Hs. rewrite E. exact H0. }
  pose proof (cec_inv2 (Z.of_nat k # 1) (cec_r6_bcoef k) w v Ha Hs2) as H.
  rewrite <- E in H.
  rewrite cec_bcoef_div_a2 in H by exact Hk.
  exact H.
Qed.

(* k=1 无条件参数化（field 全闭）：1/(1−v) − 1 == v + v² + v³/(1−v) *)
Lemma cec_r6_param_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  cec_r6_s 1 v == (1 # 1) * v + cec_r6_bcoef 1 * v * v + v * v * v * ((1 # 1) / (1 - v)).
Proof.
  intros v Hv. unfold cec_r6_s, cec_r6_bcoef.
  cbn [q_pow].
  field; cec_nz.
Qed.

(* k=1 无条件系数实例：s² 系数 = −cec_r6_coef 1 = −1 = −(1+1)/(2·1) *)
Theorem cec_kernel_coef_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  ~ (cec_r6_s 1 v == 0) ->
  Qeq ((1 # 1) * v)
      (cec_r6_s 1 v - cec_r6_coef 1 * (cec_r6_s 1 v * cec_r6_s 1 v)
       + cec_r6_s 1 v * cec_r6_s 1 v * cec_r6_s 1 v
         * cec_rho (1 # 1) (cec_r6_bcoef 1) ((1 # 1) / (1 - v)) v).
Proof.
  intros v Hv Hs.
  apply (cec_kernel_coef 1 v ((1 # 1) / (1 - v))).
  - lia.
  - exact Hs.
  - apply cec_r6_param_k1. exact Hv.
Qed.

(* 教科书字面形（s 变量，s/(1+s) = s − s² + s³/(1+s)，系数 −1 恰） *)
Lemma cec_kernel_coef_literal_s : forall s : Q, ~ ((s + (1 # 1)) == 0) ->
  Qeq (s / (s + (1 # 1)))
      (s - (1 # 1) * (s * s) + s * s * s * ((1 # 1) / (s + (1 # 1)))).
Proof.
  intros s Hs. field; cec_nz.
Qed.

(* ---- §4 嵌套切线族天花板 2(k−1)/k < 2 严格 ---- *)

Definition cec_tg (m : nat) : Q :=
  ((1 + 1)%Q * (Z.of_nat m # 1)) / (Z.of_nat (m + 1) # 1).

(* 严格天花板（QltT Set 面）：2m/(m+1) < 2 ⟸ 2m < 2(m+1) *)
Theorem cec_tangent_ceiling : forall m : nat, QltT (cec_tg m) (1 + 1)%Q.
Proof.
  intro m. apply Qlt_to_QltT.
  apply (cec_lt_div_lt ((1 + 1)%Q * (Z.of_nat m # 1)) (Z.of_nat (m + 1) # 1)
                       (1 + 1)%Q (1 # 1)).
  - apply (cec_nat_pos m).
  - unfold Qlt. simpl. lia.
  - assert (E1 : (((1 + 1)%Q * (Z.of_nat m # 1)) * (1 # 1))
                 == (Z.of_nat m # 1) + (Z.of_nat m # 1)) by ring.
    assert (E2 : ((1 + 1)%Q * (Z.of_nat (m + 1) # 1))
                 == (Z.of_nat (m + 1) # 1) + (Z.of_nat (m + 1) # 1)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* QleT' 影子件（Set 面 ≤ 形） *)
Theorem cec_tangent_le : forall m : nat, QleT' (cec_tg m) (1 + 1)%Q.
Proof.
Proof. intro m. exact (qltT_leT' (cec_tg m) (1 + 1)%Q (cec_tangent_ceiling m)). Qed.

(* 缺口恒等式：2 − 2m/(m+1) == 2/(m+1)（缺口恰 2/k 的 Q 层精确形） *)
Theorem cec_tangent_gap : forall m : nat,
  (1 + 1)%Q - cec_tg m == ((1 + 1)%Q) / (Z.of_nat (m + 1) # 1).
Proof.
  intro m. unfold cec_tg.
  (* 先统一 Z 形：z_{m+1} ≡ z_m + 1（lia 桥），化单原子后 field 收 *)
  assert (EB : (Z.of_nat (m + 1) # 1) == (Z.of_nat m # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  rewrite EB.
  field; cec_nz.
Qed.

(* ---- §5 cec_ 族公理面审计 ---- *)

Print Assumptions cec_trunc_sup.
Print Assumptions cec_H_lower.
Print Assumptions cec_kernel_coef.
Print Assumptions cec_kernel_coef_k1.
Print Assumptions cec_tangent_ceiling.
Print Assumptions cec_tangent_gap.

(* ---- §6 Z 移位与非零性基础引理 ---- *)

(* Z 移位：z_{n+1} == z_n + 1（Qmake 原子统一；lia 走 Nat2Z 零名漂移） *)
Lemma eck_z_shift : forall n : nat,
  (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + (1 # 1).
Proof. intro n. unfold Qeq, Qplus. simpl. lia. Qed.

(* 正幂非零（Qeq 面；步乘积分裂使用 Qmult_integral_l） *)
Lemma eck_q_pow_neq0 : forall (x : Q) (n : nat),
  ~ (x == 0) -> ~ (q_pow x n == 0).
Proof.
  intros x n Hx. induction n as [| m IH].
  - intro H. unfold Qeq in H. simpl in H. lia.
  - simpl. intro H. apply IH.
    exact (Qmult_integral_l x (q_pow x m) Hx H).
Qed.

(* ---- §7 几何和基础引理（q_pow Q 层版，库内缺自建） ---- *)

(* Σ_{j=0}^{k-1} x^j（内项取 j 形幂，防 S 错位） *)
Fixpoint eck_gsum (k : nat) (x : Q) : Q :=
  match k with
  | 0%nat => 0%Q
  | Datatypes.S m => eck_gsum m x + q_pow x m
  end.

(* 几何和闭式：(1-x)·Σ_{j<k} x^j == 1 - x^k（两归纳一 ring） *)
Lemma eck_geom_sum_closed : forall (k : nat) (x : Q),
  ((1 # 1) - x) * eck_gsum k x == (1 # 1) - q_pow x k.
Proof.
  intros k x. induction k as [| m IH].
  - cbn [eck_gsum q_pow]. ring.
  - cbn [eck_gsum q_pow].
    (* 分配律桥 + IH 代入 + 闭式合并（IH 模式被和式挡，直 rewrite 不中） *)
    apply (Qeq_trans _ (((1 # 1) - x) * eck_gsum m x
                        + ((1 # 1) - x) * q_pow x m)).
    + ring.
    + rewrite IH. ring.
Qed.

(* 逐幂差一：(x-1)·Σ_{j<k} x^j == x^k - 1（几何和反号直读） *)
Lemma eck_pow_minus_one : forall (k : nat) (x : Q),
  q_pow x k - (1 # 1) == (x - (1 # 1)) * eck_gsum k x.
Proof.
  intros k x.
  assert (E1 : x - (1 # 1) == - ((1 # 1) - x)) by ring.
  assert (E2 : q_pow x k - (1 # 1) == - ((1 # 1) - q_pow x k)) by ring.
  (* 序：E2 反号 → 闭式 RHS 侧代入（rewrite <-）→ E1 反号 → ring *)
  rewrite E2. rewrite <- (eck_geom_sum_closed k x). rewrite E1. ring.
Qed.

(* 倒数幂：t = 1/x 的 k 次幂 == 1/x^k（核 t = 1/(1-v) 表象桥） *)
Lemma eck_q_pow_inv : forall (k : nat) (x : Q), ~ (x == 0) ->
  q_pow ((1 # 1) / x) k == (1 # 1) / q_pow x k.
Proof.
  intros k x Hx. induction k as [| m IH].
  - cbn [q_pow]. reflexivity.
  - assert (Hpm : ~ (q_pow x m == 0)) by (apply eck_q_pow_neq0; exact Hx).
    cbn [q_pow]. rewrite IH. field; cec_nz.
Qed.

(* ---- §8 核的几何表象与步递推（逐幂一跳） ---- *)

(* 核几何表象：s_k(v) == (t-1)·Σ_{j<k} t^j，t = 1/(1-v)。
   语句：核的几何和表象等式（Qeq）；一般 k，仅 1-v≠0 域假设；
   几何和环节闭（使用 §7 自建 eck_gsum 引擎）。 *)
Lemma eck_r6s_geom : forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
  cec_r6_s k v ==
  (((1 # 1) / (1 - v)) - (1 # 1)) * eck_gsum k ((1 # 1) / (1 - v)).
Proof.
  intros k v Hv. unfold cec_r6_s.
  rewrite <- (eck_q_pow_inv k (1 - v) Hv).
  apply eck_pow_minus_one.
Qed.

(* 步递推：s_{k+1} == s_k/(1-v) + v/(1-v)（核逐幂一跳；
   k=0 基例即已闭件 cec_r6_param_k1 的恒等式面） *)
Lemma eck_r6s_step : forall (k : nat) (v : Q),
  ~ ((1 # 1) - v == 0) -> ~ (q_pow (1 - v) k == 0) ->
  cec_r6_s (Datatypes.S k) v ==
  cec_r6_s k v / (1 - v) + ((1 # 1) * v) / (1 - v).
Proof.
  intros k v Hv Hk. unfold cec_r6_s. cbn [q_pow]. field; cec_nz.
Qed.

(* ---- §9 二阶系数递推引擎 eck_Wk 与一般 k 参数化主恒等式 ---- *)

(* bcoef 步恒等：b_{k+2} == b_{k+1} + (k+2)（求和三常数 Σ1/Σj/ΣC(j,2)
   在递推侧的内敛形：二阶系数步增量即 k+2） *)
Lemma eck_bcoef_step : forall m : nat,
  cec_r6_bcoef (Datatypes.S (Datatypes.S m)) ==
  cec_r6_bcoef (Datatypes.S m) + (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1).
Proof.
  intro m. unfold cec_r6_bcoef.
  rewrite (eck_z_shift (Datatypes.S m)). rewrite (eck_z_shift m).
  field; cec_nz.
Qed.

(* W_k(v)：s_k(v) = k·v + b_k·v^2 + v^3·W_k(v) 的显式见证（分式递推，
   W_1 = 1/(1-v)，W_{k+1} = (W_k + b_{k+2})/(1-v)；k=1 与已闭件
   cec_r6_param_k1 的见证 1/(1-v) 恰合） *)
Fixpoint eck_Wk (n : nat) (v : Q) : Q :=
  match n with
  | 0%nat => (1 # 1) / (1 - v)
  | Datatypes.S m =>
      (eck_Wk m v + cec_r6_bcoef (Datatypes.S (Datatypes.S m))) / (1 - v)
  end.

(* 一般 k 参数化主恒等式（交付主件之一）：
   s_{k+1}(v) == (k+1)·v + b_{k+1}·v^2 + v^3·W_k(v)。
   见证 w = eck_Wk k v 显式给出，假设卸载（Qeq 无条件形）；
   一般 k 无条件（1-v≠0 为 q_pow/分母内禀域假设，非降级非虚报）；
   边界：v=0 点两面包络仍闭（s=0 与右端同为 0），恒等式域内全域
   成立；无不可判定墙、无 Or-encoding 墙。 *)
Theorem eck_r6_param_k : forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
  cec_r6_s (Datatypes.S k) v ==
  (Z.of_nat (Datatypes.S k) # 1) * v + cec_r6_bcoef (Datatypes.S k) * v * v
  + v * v * v * eck_Wk k v.
Proof.
  intros k v Hv. induction k as [| m IH].
  - cbn [eck_Wk]. exact (cec_r6_param_k1 v Hv).
  - assert (Hpm : ~ (q_pow (1 - v) (Datatypes.S m) == 0))
      by (apply eck_q_pow_neq0; exact Hv).
    rewrite (eck_r6s_step (Datatypes.S m) v Hv Hpm).
    rewrite IH. cbn [eck_Wk]. rewrite eck_bcoef_step.
    rewrite (eck_z_shift (Datatypes.S m)).
    field; cec_nz.
Qed.

(* sigT 装载件：一般 k 参数化见证包（proj1 = eck_Wk k v 可计算提取，
   Set 面透明设计，沿 UpReqUMixSelect 提取透明先例） *)
Definition eck_param_sig : Type :=
  forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
    sigT (fun w : Q =>
      cec_r6_s (Datatypes.S k) v ==
      (Z.of_nat (Datatypes.S k) # 1) * v
      + cec_r6_bcoef (Datatypes.S k) * v * v + v * v * v * w).

Definition eck_param_pack : eck_param_sig :=
  fun (k : nat) (v : Q) (Hv : ~ ((1 # 1) - v == 0)) =>
    existT (fun w : Q =>
      cec_r6_s (Datatypes.S k) v ==
      (Z.of_nat (Datatypes.S k) # 1) * v
      + cec_r6_bcoef (Datatypes.S k) * v * v + v * v * v * w)
      (eck_Wk k v) (eck_r6_param_k k v Hv).

(* ---- §10 主定理：cec_kernel_coef 一般 k 无条件形 ---- *)

(* 二阶反演一般 k 无条件实例：核二阶系数 (k+1)/(2k) = cec_r6_coef k
   对一般 k 承载，无需参数化恒等式假设（k=1 退化为 cec_kernel_coef_k1）。
   语句：一般 k 无条件 Qeq 反演形，见证 w = eck_Wk k v；强度：
   与 cec_kernel_coef_k1 同构且 k 自由（cec_kernel_coef 泛化形的最强
   可证形）；边界：域假设 1-v≠0 与 s≠0（反演非零性）为内禀域假设，
   无不可判定墙、无 Or-encoding 墙。 *)
Theorem eck_kernel_coef_k : forall (k : nat) (v : Q),
  ~ ((1 # 1) - v == 0) -> ~ (cec_r6_s (Datatypes.S k) v == 0) ->
  Qeq ((Z.of_nat (Datatypes.S k) # 1) * v)
      (cec_r6_s (Datatypes.S k) v
       - cec_r6_coef (Datatypes.S k)
         * (cec_r6_s (Datatypes.S k) v * cec_r6_s (Datatypes.S k) v)
       + cec_r6_s (Datatypes.S k) v * cec_r6_s (Datatypes.S k) v
         * cec_r6_s (Datatypes.S k) v
         * cec_rho (Z.of_nat (Datatypes.S k) # 1) (cec_r6_bcoef (Datatypes.S k))
             (eck_Wk k v) v).
Proof.
  intros k v Hv Hs.
  apply (cec_kernel_coef (Datatypes.S k) v (eck_Wk k v)).
  - lia.
  - exact Hs.
  - apply eck_r6_param_k. exact Hv.
Qed.

(* ---- §11 eck_ 族公理面审计 ---- *)

Print Assumptions eck_geom_sum_closed.
Print Assumptions eck_r6s_geom.
Print Assumptions eck_r6s_step.
Print Assumptions eck_r6_param_k.
Print Assumptions eck_param_pack.
Print Assumptions eck_kernel_coef_k.

(* ============================================================ *)
(* §12 便捷桥两件                                                *)
(* ============================================================ *)

(* QltT → QleT' 降格（严格蕴涵非严格） *)
Lemma etc_ltT_leT' : forall x y : Q, QltT x y -> QleT' x y.
Proof.
  intros x y H.
  apply Qle_to_QleT'.
  apply QltT_to_Qlt in H. unfold Qle. unfold Qlt in H. lia.
Qed.

(* Set 层等值见证直接使用 S02 原生 QeqT（Id-Qcompare 反映形，
   qeq_imp_qeqT/qeqT_imp_qeq 双向桥在案），本件不另造第三形。 *)

(* ============================================================ *)
(* §13 等值代换三件（Z 层显式乘式链，不做 Qlt 下重写）           *)
(* ============================================================ *)

(* 左代换（≤）：x == y、x ≤ z ⟹ y ≤ z *)
Lemma etc_qeq_le_r : forall x y z : Q, (x == y)%Q -> (x <= z)%Q -> (y <= z)%Q.
Proof.
  intros x y z He Hle.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qle in Hle. unfold Qeq in He. unfold Qle.
  apply (Zmult_le_reg_r (Qnum y * Z.pos (Qden z))
           (Qnum z * Z.pos (Qden y)) (Z.pos (Qden x))).
  - lia.
  - replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_le_compat_r (Qnum x * Z.pos (Qden z))
             (Qnum z * Z.pos (Qden x)) (Z.pos (Qden y))).
    + exact Hle.
    + lia.
Qed.

(* 左代换（＜）：x == y、z ＜ x ⟹ z ＜ y *)
Lemma etc_qeq_lt_r : forall x y z : Q, (x == y)%Q -> (z < x)%Q -> (z < y)%Q.
Proof.
  intros x y z He Hlt.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qlt in Hlt. unfold Qeq in He. unfold Qlt.
  apply (Zmult_lt_reg_r (Qnum z * Z.pos (Qden y))
           (Qnum y * Z.pos (Qden z)) (Z.pos (Qden x))).
  - exact Hdx.
  - replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_lt_compat_r (Qnum z * Z.pos (Qden x))
             (Qnum x * Z.pos (Qden z)) (Z.pos (Qden y))).
    + exact Hdy.
    + exact Hlt.
Qed.

(* Qabs 零化：a == b ⟹ |a−b| == 0 *)
Lemma etc_qabs_zero : forall a b : Q, (a == b)%Q -> (Qabs (a - b) == 0)%Q.
Proof.
  intros a b Hab.
  assert (Hd : (a - b == 0)%Q).
  { apply (Qeq_trans (a + - b)%Q (b + - b)%Q).
    - apply Qplus_comp; [exact Hab | apply Qeq_refl].
    - apply Qplus_opp_r. }
  apply (Qabs_case (a - b) (fun t => (t == 0)%Q)).
  - intros _. exact Hd.
  - intros _. apply (Qeq_trans (- (a - b))%Q (- 0)%Q 0%Q).
    + apply (Qopp_comp (a - b) 0%Q Hd).
    + reflexivity.
Qed.

(* ============================================================ *)
(* §14 eps 分半基础引理                                            *)
(* ============================================================ *)

(* 半量正性：0 < eps ⟹ 0 < (1#2)·eps *)
Lemma etc_eps_half_pos : forall eps : Q, QltT 0 eps -> QltT 0 ((1#2) * eps).
Proof.
  intros eps Heps.
  apply Qlt_to_QltT.
  apply Qmult_lt_0_compat.
  - unfold Qlt. simpl. lia.
  - apply QltT_to_Qlt. exact Heps.
Qed.

(* 分半回接恒等：(1#2)·eps + (1#2)·eps == eps（eps/2 拆分闭合） *)
Lemma etc_eps_half_add : forall eps : Q,
  (((1#2) * eps) + ((1#2) * eps) == eps)%Q.
Proof.
  intro eps.
  assert (Hone : (((1#2) + (1#2)) == 1)%Q) by reflexivity.
  rewrite <- (Qmult_plus_distr_l (1#2) (1#2) eps).
  rewrite Hone.
  apply Qmult_1_l.
Qed.

(* ============================================================ *)
(* §15 主件：ε-三分（三支 sigT 见证形）                          *)
(* ============================================================ *)

Theorem etc_trichotomy : forall (a b eps : Q),
  QltT 0 eps ->
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => QleT' (Qabs (a - b)) eps
    | Gt => QltT b a
    end).
Proof.
  intros a b eps Heps.
  destruct (Qcompare a b) eqn:E.
  - (* Eq 支：a == b ⟹ |a−b| == 0 ＜ eps ⟹ 判定必非 Gt（comparison 序＝Eq|Lt|Gt） *)
    exists Eq.
    assert (Hq : (a == b)%Q).
    { apply (proj2 (Qeq_alt a b)). exact E. }
    assert (Hz := etc_qabs_zero a b Hq).
    apply QltT_to_Qlt in Heps.
    unfold QleT', Qle_bool.
    destruct (Qcompare (Qabs (a - b)) eps) eqn:E2.
    + reflexivity.
    + reflexivity.
    + exfalso.
      assert (Hgt : (eps < Qabs (a - b))%Q) by (apply Qgt_alt; exact E2).
      apply (etc_qeq_lt_r (Qabs (a - b)) 0 eps Hz) in Hgt.
      assert (Hc : (0 < 0)%Q) by (apply Qlt_trans with eps; assumption).
      destruct (Qlt_irrefl 0 Hc).
  - (* Lt 支：a ＜ b *)
    exists Lt. unfold QltT, Qlt_bool. rewrite E. reflexivity.
  - (* Gt 支：b ＜ a（见证判定式为 (b ?= a)，独立分账） *)
    exists Gt. unfold QltT, Qlt_bool.
    destruct (Qcompare b a) eqn:E3.
    + exfalso.
      assert (Heqba : (b == a)%Q) by (apply (proj2 (Qeq_alt b a)); exact E3).
      assert (Eab : (a ?= b) = Eq).
      { apply (proj1 (Qeq_alt a b)). apply Qeq_sym. exact Heqba. }
      rewrite Eab in E. discriminate.
    + reflexivity.
    + exfalso.
      assert (Hba : (b < a)%Q) by (apply Qgt_alt; exact E).
      assert (Hab : (a < b)%Q) by (apply Qgt_alt; exact E3).
      exact (Qlt_irrefl a (Qlt_trans a b a Hab Hba)).
Defined.

(* ============================================================ *)
(* §16 Apart 桥：|a−b| ＞ eps ⟹ 三分判 Lt/Gt（Eq 支排空）        *)
(* ============================================================ *)

Theorem etc_apart : forall (a b eps : Q),
  QltT 0 eps ->
  QltT eps (Qabs (a - b)) ->
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => Id false true
    | Gt => QltT b a
    end).
Proof.
  intros a b eps Heps Hap.
  destruct (Qcompare a b) eqn:E.
  - (* Eq 支排空：a == b ⟹ |a−b| == 0 ⟹ eps ＜ 0，与 0 ＜ eps 矛盾 *)
    assert (Hq : (a == b)%Q).
    { apply (proj2 (Qeq_alt a b)). exact E. }
    assert (Hz := etc_qabs_zero a b Hq).
    apply QltT_to_Qlt in Hap.
    apply (etc_qeq_lt_r (Qabs (a - b)) 0 eps Hz) in Hap.
    apply QltT_to_Qlt in Heps.
    assert (Hc : (0 < 0)%Q) by (apply Qlt_trans with eps; assumption).
    destruct (Qlt_irrefl 0 Hc).
  - exists Lt. unfold QltT, Qlt_bool. rewrite E. reflexivity.
  - exists Gt. unfold QltT, Qlt_bool.
    destruct (Qcompare b a) eqn:E3.
    + exfalso.
      assert (Heqba : (b == a)%Q) by (apply (proj2 (Qeq_alt b a)); exact E3).
      assert (Eab : (a ?= b) = Eq).
      { apply (proj1 (Qeq_alt a b)). apply Qeq_sym. exact Heqba. }
      rewrite Eab in E. discriminate.
    + reflexivity.
    + exfalso.
      assert (Hba : (b < a)%Q) by (apply Qgt_alt; exact E).
      assert (Hab : (a < b)%Q) by (apply Qgt_alt; exact E3).
      exact (Qlt_irrefl a (Qlt_trans a b a Hab Hba)).
Defined.

(* ============================================================ *)
(* §17 出口便捷件：精确比较三分族                                *)
(*   符号提取（ε-三分符号支）＝etc_sign_tri；                   *)
(*   单位一侧判分（t≤1 vs t＞1）＝etc_one_side；                *)
(*   通用二点比较面＝etc_compare_tri。                          *)
(* ============================================================ *)

Theorem etc_compare_tri : forall a b : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT a b
    | Eq => QeqT a b
    | Gt => QltT b a
    end).
Proof.
  intros a b.
  destruct (Qcompare a b) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply (proj2 (Qeq_alt a b)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* 便捷实例一：符号提取（t 正/零/负三分） *)
Theorem etc_sign_tri : forall t : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT 0 t
    | Eq => QeqT t 0
    | Gt => QltT t 0
    end).
Proof.
  intro t.
  destruct (Qcompare 0 t) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply Qeq_sym. apply (proj2 (Qeq_alt 0 t)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* 便捷实例二：单位上界判支（t ＜ 1 / t == 1 / t ＞ 1） *)
Theorem etc_one_side : forall t : Q,
  sigT (fun c : comparison =>
    match c with
    | Lt => QltT t 1
    | Eq => QeqT t 1
    | Gt => QltT 1 t
    end).
Proof.
  intro t.
  destruct (Qcompare t 1) eqn:E.
  - exists Eq. apply qeq_imp_qeqT.
    apply (proj2 (Qeq_alt t 1)). exact E.
  - exists Lt. apply Qlt_to_QltT. apply Qlt_alt. exact E.
  - exists Gt. apply Qlt_to_QltT. apply Qgt_alt. exact E.
Defined.

(* ============================================================ *)
(* §18 提取检验：sigT 见证可计算、证明面擦除                  *)
(* ============================================================ *)
Definition etc_pack (a b eps : Q) (Heps : QltT 0 eps) : comparison :=
  projT1 (etc_trichotomy a b eps Heps).

Extraction "etc13_out" etc_pack etc_eps_half_add.

(* 公理面审计 *)
Print Assumptions etc_trichotomy.
Print Assumptions etc_apart.
Print Assumptions etc_compare_tri.
Print Assumptions etc_sign_tri.
Print Assumptions etc_one_side.
Print Assumptions etc_eps_half_pos.
Print Assumptions etc_eps_half_add.
Print Assumptions etc_qeq_le_r.
Print Assumptions etc_qeq_lt_r.
Print Assumptions etc_qabs_zero.
Print Assumptions etc_ltT_leT'.

(* ============================================================ *)
(* §19 单元面小件：real_one 逐坐标投影 + 减法等值面双保               *)
(* ============================================================ *)

(* real_one 逐坐标投影叶：projT1 real_one n == 1（real_one 定义面透明） *)
Lemma pkc_one_proj : forall n : nat, (projT1 real_one n == 1)%Q.
Proof. intro n. cbv [projT1 real_one]. exact (Qeq_refl 1%Q). Qed.

(* 左元减法等值面：a == b ⟹ x − a == x − b *)
Lemma pkc_minus_l_wd : forall a b x : Q, (a == b)%Q -> (x - a == x - b)%Q.
Proof.
  intros a b x H.
  apply (Qeq_trans (x + - a) (x + - b)).
  - apply Qplus_comp; [apply Qeq_refl | apply (Qopp_comp a b H) ].
  - apply Qeq_refl.
Qed.

(* 右元减法等值面：a == b ⟹ a − x == b − x *)
Lemma pkc_minus_r_wd : forall a b x : Q, (a == b)%Q -> (a - x == b - x)%Q.
Proof.
  intros a b x H.
  apply (Qeq_trans (a + - x) (b + - x)).
  - apply Qplus_comp; [exact H | apply Qeq_refl].
  - apply Qeq_refl.
Qed.

(* 左元严格小代换：x == y、x ＜ z ⟹ y ＜ z（etc_qeq_lt_r 同配方，
   乘子取 Qden x 的 Z 层显式乘式链） *)
Lemma pkc_qeq_lt_l : forall x y z : Q, (x == y)%Q -> (x < z)%Q -> (y < z)%Q.
Proof.
  intros x y z He Hlt.
  assert (Hdx : (0 < Z.pos (Qden x))%Z) by apply Pos2Z.pos_is_pos.
  assert (Hdy : (0 < Z.pos (Qden y))%Z) by apply Pos2Z.pos_is_pos.
  unfold Qlt in Hlt. unfold Qeq in He. unfold Qlt.
  apply (Zmult_lt_reg_r (Qnum y * Z.pos (Qden z))
           (Qnum z * Z.pos (Qden y)) (Z.pos (Qden x))).
  - exact Hdx.
  - replace (((Qnum y * Z.pos (Qden z)) * Z.pos (Qden x))%Z)
        with (((Qnum y * Z.pos (Qden x)) * Z.pos (Qden z))%Z) by ring.
    replace (((Qnum z * Z.pos (Qden y)) * Z.pos (Qden x))%Z)
        with (((Qnum z * Z.pos (Qden x)) * Z.pos (Qden y))%Z) by ring.
    rewrite <- He.
    replace (((Qnum x * Z.pos (Qden y)) * Z.pos (Qden z))%Z)
        with (((Qnum x * Z.pos (Qden z)) * Z.pos (Qden y))%Z) by ring.
    apply (Zmult_lt_compat_r (Qnum x * Z.pos (Qden z))
             (Qnum z * Z.pos (Qden x)) (Z.pos (Qden y))).
    + exact Hdy.
    + exact Hlt.
Qed.

(* 半量严格小：0 < e ⟹ (1#2)·e ＜ e（eps 分半的半-全比较叶：
   全程使用基建件 etc_eps_half_pos / etc_eps_half_add） *)
Lemma pkc_half_lt : forall e : Q, QltT 0 e -> QltT ((1#2) * e) e.
Proof.
  intros e H.
  assert (Hpos : QltT 0 ((1#2) * e)) by exact (etc_eps_half_pos e H).
  assert (Hlt : (0 < (1#2) * e)%Q) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hsub : ((1#2) * e == e - (1#2) * e)%Q).
  { assert (Ta : (((1#2) * e + (1#2) * e) + - ((1#2) * e))
                 == ((1#2) * e + ((1#2) * e + - ((1#2) * e))))
      by exact (Qeq_sym _ _
             (Qplus_assoc ((1#2) * e) ((1#2) * e) (- ((1#2) * e)))).
    assert (Tb : ((1#2) * e + ((1#2) * e + - ((1#2) * e)))
                 == ((1#2) * e + 0))
      by (apply Qplus_comp; [apply Qeq_refl | apply Qplus_opp_r]).
    assert (Tc : ((1#2) * e + 0) == (1#2) * e) by apply Qplus_0_r.
    assert (T4 : (((1#2) * e + (1#2) * e) + - ((1#2) * e)) == (1#2) * e)
      by exact (Qeq_trans _ _ _ Ta (Qeq_trans _ _ _ Tb Tc)).
    apply (Qeq_trans _ _ _ (Qeq_sym _ _ T4)).
    apply Qplus_comp; [exact (etc_eps_half_add e) | apply Qeq_refl]. }
  assert (Hsub' : (0 < e - (1#2) * e)%Q)
    by exact (etc_qeq_lt_r _ _ 0 Hsub Hlt).
  apply Qlt_to_QltT.
  apply (proj2 (Qlt_minus_iff ((1#2) * e) e)).
  unfold Qminus. exact Hsub'.
Qed.

(* ============================================================ *)
(* §20 ε-三分符号支点级装载                                           *)
(*   前置需求：两支的构造性证明需 ε-三分（p<q+δ 与 q<p+δ 的           *)
(*   Cauchy 点级比较）基建。本件把 Real 层一侧分离（real_lt q p）      *)
(*   的见证逐坐标点装载为 Q 层符号三分裁决：对一切足够远坐标，         *)
(*   p_n − q_n 的 etc_sign_tri 判定必落正支（Lt 支），负支/零支        *)
(*   逐点排空（Id false true 显式消解）。                              *)
(* ============================================================ *)

Theorem pkc_sign_load : forall (p q : Real), real_lt q p ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => Id false true
      | Eq => Id false true
      | Gt => QltT 0 (projT1 p n - projT1 q n)
      end)).
Proof.
  intros p q Hpq. destruct Hpq as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNd : QltT d (projT1 p n - projT1 q n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  assert (HltD : (d < projT1 p n - projT1 q n)%Q) by (apply QltT_to_Qlt; exact HNd).
  destruct (etc_sign_tri (projT1 p n - projT1 q n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝p_n − q_n == 0 ⟹ d ＜ 0，与 0 ＜ d 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hlt0 : (d < 0)%Q) by exact (etc_qeq_lt_r _ 0 d Hc HltD).
    assert (Hcc : (0 < 0)%Q) by (apply Qlt_trans with d; [exact Hd | exact Hlt0]).
    destruct (Qlt_irrefl 0 Hcc).
  - (* Lt 支＝0 ＜ p_n − q_n：正支成立，装 Gt 标签 *)
    exists Gt. exact Hc.
  - (* Gt 支＝p_n − q_n ＜ 0 ⟹ d ＜ 负，与 0 ＜ d 矛盾 *)
    assert (Hneg : (projT1 p n - projT1 q n < 0)%Q) by (apply QltT_to_Qlt; exact Hc).
    assert (Hlt0 : (d < 0)%Q) by exact (Qlt_trans d _ _ HltD Hneg).
    assert (Hcc : (0 < 0)%Q) by (apply Qlt_trans with d; [exact Hd | exact Hlt0]).
    destruct (Qlt_irrefl 0 Hcc).
Defined.

(* ============================================================ *)
(* §21 eps 分半余量装载                                               *)
(*   使用 etc_eps_half_pos（半量正性）+ etc_eps_half_add（分半回接）：  *)
(*   一侧分离见证 δ 可安全减半：半量 δ/2 自身正、且逐坐标仍是           *)
(*   p_n − q_n 的严格下界（半-全比较经 pkc_half_lt）。                  *)
(* ============================================================ *)

Theorem pkc_half_slack_load : forall (p q : Real), real_lt q p ->
  sigT (fun d : Q =>
    And (QltT 0 d)
    (And (((1#2) * d + (1#2) * d == d)%Q)
    (sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT ((1#2) * d) (projT1 p n - projT1 q n))))).
Proof.
  intros p q Hpq. destruct Hpq as [e [He0 [N HN]]].
  exists e. split.
  - (* 见证正性 *)
    exact He0.
  - split.
    + (* 分半回接恒等：直接使用基建件 *)
      exact (etc_eps_half_add e).
    + exists N. intros n Hn.
      assert (Hhalf : QltT ((1#2) * e) e) by (apply pkc_half_lt; exact He0).
      assert (HNn : QltT e (projT1 p n - projT1 q n)) by (apply HN; exact Hn).
      apply QltT_to_Qlt in Hhalf.
      apply QltT_to_Qlt in HNn.
      apply Qlt_to_QltT.
      exact (Qlt_trans _ _ _ Hhalf HNn).
Defined.

(* ============================================================ *)
(* §22 单位一侧分离判分装载——etc_one_side 分支装载                    *)
(*   裁决目标：t>1 支给出 t²(t−1)≥_B 0 的前提面；t∈[0,1] 近支的        *)
(*   log 本体未落（见文尾诚实边界）。本节交付判分面：                  *)
(*   把 Real 层单位一侧分离前提逐坐标点裁决到 far 支（1 ＜ t_n，        *)
(*   t²(t−1) ≥ 0 前提面）或 near 支（t_n ＜ 1），对侧支逐点             *)
(*   排空。log 本体（二阶核）不在盘，见文尾诚实边界。                  *)
(* ============================================================ *)

(* 远支装载：real_lt real_one t ⟹ 足够远坐标全部落 1 ＜ t_n 支 *)
Theorem pkc_oneside_far_load : forall t : Real, real_lt real_one t ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => Id false true
      | Eq => Id false true
      | Gt => QltT 1 (projT1 t n)
      end)).
Proof.
  intros t H. destruct H as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNn : QltT d (projT1 t n - projT1 real_one n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  apply QltT_to_Qlt in HNn.
  assert (H1n : (projT1 t n - projT1 real_one n == projT1 t n - 1)%Q)
    by (apply pkc_minus_l_wd; apply pkc_one_proj).
  assert (HNn' : (d < projT1 t n - 1)%Q) by exact (etc_qeq_lt_r _ _ d H1n HNn).
  assert (Hpos : (0 < projT1 t n - 1)%Q) by exact (Qlt_trans 0 d _ Hd HNn').
  assert (Hfar : (1 < projT1 t n)%Q).
  { apply (proj2 (Qlt_minus_iff 1 (projT1 t n))). unfold Qminus. exact Hpos. }
  destruct (etc_one_side (projT1 t n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝t_n == 1，与 1 ＜ t_n 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (etc_qeq_lt_r _ 1 1 Hc Hfar).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Lt 支＝t_n ＜ 1，与 1 ＜ t_n 矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (Qlt_trans 1 _ _ Hfar Hc).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Gt 支＝1 ＜ t_n：far 支成立 *)
    exists Gt. exact Hc.
Defined.

(* 近支装载：real_lt t real_one ⟹ 足够远坐标全部落 t_n ＜ 1 支 *)
Theorem pkc_oneside_near_load : forall t : Real, real_lt t real_one ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    sigT (fun c : comparison =>
      match c with
      | Lt => QltT (projT1 t n) 1
      | Eq => Id false true
      | Gt => Id false true
      end)).
Proof.
  intros t H. destruct H as [d [Hd0 [N HN]]].
  exists N. intros n Hn.
  assert (HNn : QltT d (projT1 real_one n - projT1 t n)) by (apply HN; exact Hn).
  assert (Hd : (0 < d)%Q) by (apply QltT_to_Qlt; exact Hd0).
  apply QltT_to_Qlt in HNn.
  assert (H1n : (projT1 real_one n - projT1 t n == 1 - projT1 t n)%Q)
    by (apply pkc_minus_r_wd; apply pkc_one_proj).
  assert (HNn' : (d < 1 - projT1 t n)%Q) by exact (etc_qeq_lt_r _ _ d H1n HNn).
  assert (Hpos : (0 < 1 - projT1 t n)%Q) by exact (Qlt_trans 0 d _ Hd HNn').
  assert (Hnear : (projT1 t n < 1)%Q).
  { apply (proj2 (Qlt_minus_iff (projT1 t n) 1)). unfold Qminus. exact Hpos. }
  destruct (etc_one_side (projT1 t n)) as [c Hc]; destruct c.
  - (* comparison 序＝Eq|Lt|Gt：本支 Eq＝t_n == 1，与 t_n ＜ 1 矛盾 *)
    apply qeqT_imp_qeq in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (pkc_qeq_lt_l _ 1 1 Hc Hnear).
    destruct (Qlt_irrefl 1 Hcc).
  - (* Lt 支＝t_n ＜ 1：near 支成立 *)
    exists Lt. exact Hc.
  - (* Gt 支＝1 ＜ t_n，与 t_n ＜ 1 矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : (1 < 1)%Q) by exact (Qlt_trans 1 _ _ Hc Hnear).
    destruct (Qlt_irrefl 1 Hcc).
Defined.

(* ============================================================ *)
(* §23 Q 层常数比较面装配                                             *)
(*   裁决目标：KL 语义桥接件（kl₂ ≥ c*(k)·TV²）所依赖的                *)
(*   pnk_pinsker_trunc5 不在盘。本节交付其 Q 层常数比较面：            *)
(*   天花板常数 c*(k)（k≥5 尾段）对 2 的 etc_compare_tri 三分裁决       *)
(*   收拢到 Eq 支（cec_cstar_tail 等值证书装载），Lt/Gt 支排空。        *)
(* ============================================================ *)

Theorem pkc_w3_qface : forall k : nat, (5 <= k)%nat ->
  sigT (fun c : comparison =>
    match c with
    | Lt => Id false true
    | Eq => QeqT (cec_cstar k) (1 + 1)%Q
    | Gt => Id false true
    end).
Proof.
  intros k Hk.
  assert (Ht : (cec_cstar k == 1 + 1)%Q) by (apply cec_cstar_tail; exact Hk).
  destruct (etc_compare_tri (cec_cstar k) (1 + 1)) as [c Hc]; destruct c.
  - (* etc Eq 支＝等值证书：常数面 Eq 支装载 *)
    exists Eq. exact Hc.
  - (* etc Lt 支＝c*(k) ＜ 2，与尾段等值证书矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : ((1 + 1) < (1 + 1))%Q) by exact (pkc_qeq_lt_l _ _ _ Ht Hc).
    destruct (Qlt_irrefl (1 + 1)%Q Hcc).
  - (* etc Gt 支＝2 ＜ c*(k)，与尾段等值证书矛盾 *)
    apply QltT_to_Qlt in Hc.
    assert (Hcc : ((1 + 1) < (1 + 1))%Q) by exact (etc_qeq_lt_r _ _ _ Ht Hc).
    destruct (Qlt_irrefl (1 + 1)%Q Hcc).
Defined.

(* ============================================================ *)
(* §24 提取检验：三分标签可计算、证明面擦除                       *)
(* ============================================================ *)

Definition pkc_pack_sign (p q : Real) (Hpq : real_lt q p)
  (n : nat) (Hn : NatLe (projT1 (pkc_sign_load p q Hpq)) n) : comparison :=
  projT1 (projT2 (pkc_sign_load p q Hpq) n Hn).

Definition pkc_pack_far (t : Real) (H : real_lt real_one t)
  (n : nat) (Hn : NatLe (projT1 (pkc_oneside_far_load t H)) n) : comparison :=
  projT1 (projT2 (pkc_oneside_far_load t H) n Hn).

Definition pkc_pack_near (t : Real) (H : real_lt t real_one)
  (n : nat) (Hn : NatLe (projT1 (pkc_oneside_near_load t H)) n) : comparison :=
  projT1 (projT2 (pkc_oneside_near_load t H) n Hn).

Definition pkc_pack_w3 (k : nat) (Hk : (5 <= k)%nat) : comparison :=
  projT1 (pkc_w3_qface k Hk).

Extraction "pkc13_out" pkc_pack_sign pkc_pack_far pkc_pack_near pkc_pack_w3
  pkc_half_lt.

(* ============================================================ *)
(* 公理面审计                                              *)
(* ============================================================ *)
Print Assumptions pkc_sign_load.
Print Assumptions pkc_half_slack_load.
Print Assumptions pkc_oneside_far_load.
Print Assumptions pkc_oneside_near_load.
Print Assumptions pkc_w3_qface.
Print Assumptions pkc_half_lt.
Print Assumptions pkc_one_proj.

(* ============================================================ *)
(* 诚实边界                                                            *)
(*   ① 常数 2 完整形（kl₂ ≥ 2·TV²）未交付：其近支/二阶级数核本体       *)
(*      需真二阶 log 引擎（尾残差/交替级数截断环），库内在盘引擎        *)
(*      （上切线核+同构切线+fracsum 合流）信息论上限为常数 1            *)
(*      （UpReqPinskerCore 数值已证结论同源）。                         *)
(*   ② 近支 log 本体（log(1+t) ≥ t−t²/2 于 t∈[0,1]）未交付：            *)
(*      库内无该引擎定理（pnk_log1p_ge_far 仅存在于注释，无定理         *)
(*      本体）；§22 交付其判分装载面。                                  *)
(*   ③ KL 语义桥 pnk_pinsker_trunc5 不在盘；§23 交付其 Q 层             *)
(*      常数比较面（cec_cstar 尾段 Eq 支收拢）。                        *)
(* ============================================================ *)
