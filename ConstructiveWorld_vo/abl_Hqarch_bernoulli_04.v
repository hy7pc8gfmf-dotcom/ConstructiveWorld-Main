(* ==========================================================================)
   abl_Hqarch_bernoulli_04.v — R2BishopLogSel Hqarch 构造性闭合切片 1/2：Q 层 Bernoulli 下界件 + Hqarch 站点形状接口（独立消融件）
   使命: 独立闭合 ConstructiveWorld_Live/R2BishopLogSel.v 主件 mix_k_select_bishop
     前件 Hqarch（Q 层收缩幂 Archimedean 站点，L314-321）的构造性闭合第 1 片
     （源件自注 L314-315：「其构造性闭合件=Bernoulli×Archimedes」）。交付两件：
     ① abl_bern_lower——Bernoulli 不等式 Q 层下形 1 + n·q ≤ (1+q)^n
        （q ≥ 0，n:nat 迭代幂），纯 Q 循环归纳；随件 abl_qpow_ge1（≥1 面）。
     ② abl_hqarch_bern_step / abl_hqarch_via_bern——Hqarch 站点形状接口：
        Hqarch 前件精确形状（源件 L319-320）为
          forall (p v b : Q), Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
            sigT (fun j : nat => Qle (mixe_qpow p j * v) b)
        本件 abl_hqarch_via_bern 以同形 sigT 收束，谓词体内幂件为 abl_qpow。
     接口对应说明（abl_qpow ↔ mixe_qpow）：UpReqMixLogE.v:L296-299 mixe_qpow
       与本件 abl_qpow 为同体 Fixpoint（match 0 => 1 | S m => x * 自身 m end，
       仅命名异）——结论 Qle (abl_qpow p j * v) b 与站点 Qle (mixe_qpow p j * v) b
       逐项对应（同一函数更名）。本件取纯 Stdlib 依赖面（零本库 Require），
       故不 Require UpReqMixLogE，幂件自备同名体；两体文本恒同（源件
       UpReqMixLogE.v:296 对照确认）。
     下片（2/2 桥接件）接续点：第四前件 Qle v (b * (1 + n·(/p - 1)))（即
       v ≤ b·(1+n·w)，w := /p - 1 = (1-p)/p）的 n 见证生产——纯 Q 层
       Archimedean（w > 0 时取 n·w ≥ v/b）；Q 层参照=UpReqMixLogA real_arch
       （Real 层）与 Arch_UpReq_10 / Arch_UpAbl_30 的 Q 层 nat 尺度件。
   源件: ConstructiveWorld_Live/R2BishopLogSel.v:L311-321（Hqarch 自注+形状，
     只读对照）；库内参照: UpReqMixLogE.v:L287-299（mixe_qpow 定义+F 族清单）、
     UpReqMixLogE.v:L381（mixe_bern_lower 库内同形件——本件独立重证不引用）。
   依赖: 纯 Stdlib（QArith、ZArith、Lia、Extraction）——自包含新件。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑； witness 以 sigT（Set/Type 层）
     承载，序谓词沿站点口径用 stdlib Qle/Qlt（Hqarch 前件同款）。
   编译配方: 隔离池真拷单件，cpu_guard 包裹 rocq c -Q <池> "" 本件（cwd 异地）。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.

Open Scope Q_scope.

(* ============================================================ *)
(* Part A：Q 层传输小件（Qeq→Qle/Qlt 项式传输；Qeq 目标内 rewrite）       *)
(* ============================================================ *)

Lemma abl_qlt_01 : Qlt 0 1.
Proof. unfold Qlt. cbn. lia. Qed.

Lemma abl_qeq_le : forall a b : Q, Qeq a b -> Qle a b.
Proof.
  intros a b Hab. unfold Qle, Qeq in *. rewrite Hab. apply Z.le_refl.
Qed.

Lemma abl_qle_eq_l : forall a b c : Q, Qeq a b -> Qle b c -> Qle a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - apply abl_qeq_le. exact Hab.
  - exact Hbc.
Qed.

Lemma abl_qle_eq_r : forall a b c : Q, Qle a b -> Qeq b c -> Qle a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_trans a b c).
  - exact Hab.
  - apply abl_qeq_le. exact Hbc.
Qed.

Lemma abl_qlt_eq_l : forall a b c : Q, Qeq a b -> Qlt b c -> Qlt a c.
Proof.
  intros a b c Hab Hbc. apply (Qle_lt_trans a b c).
  - apply abl_qeq_le. exact Hab.
  - exact Hbc.
Qed.

Lemma abl_qlt_eq_r : forall a b c : Q, Qlt a b -> Qeq b c -> Qlt a c.
Proof.
  intros a b c Hab Hbc. apply (Qlt_le_trans a b c).
  - exact Hab.
  - apply abl_qeq_le. exact Hbc.
Qed.

Lemma abl_qmult_eq_l : forall a b c : Q, Qeq a b -> Qeq (a * c) (b * c).
Proof.
  intros a b c Hab. rewrite Hab. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* Part B：nat 尺度有理化与幂件（abl_qpow：同 mixe_qpow 体，自备零撞名）   *)
(* ============================================================ *)

Definition abl_qofnat (k : nat) : Q := (Z.of_nat k # 1)%Q.

Lemma abl_qofnat_nonneg : forall n : nat, Qle 0 (abl_qofnat n).
Proof.
  intro n. unfold Qle, abl_qofnat. cbn [Qnum Qden]. lia.
Qed.

Lemma abl_qofnat_S : forall n : nat, abl_qofnat (S n) == (1 + abl_qofnat n)%Q.
Proof.
  intro n. unfold Qeq, Qplus, abl_qofnat. cbn [Qnum Qden]. lia.
Qed.

Fixpoint abl_qpow (x : Q) (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S m => x * abl_qpow x m
  end.

Lemma abl_boost : forall (n : nat) (q : Q), Qle 0 q -> Qle 1 (1 + abl_qofnat n * q).
Proof.
  intros n q Hq0.
  assert (Hnq0 : Qle (0 * q) (abl_qofnat n * q)).
  { exact (Qmult_le_compat_r 0 (abl_qofnat n) q (abl_qofnat_nonneg n) Hq0). }
  assert (Hnq0' : Qle 0 (abl_qofnat n * q)).
  { apply (abl_qle_eq_l 0 (0 * q) (abl_qofnat n * q)).
    - ring.
    - exact Hnq0. }
  apply (abl_qle_eq_l 1 (1 + 0) (1 + abl_qofnat n * q)).
  - ring.
  - exact (Qplus_le_compat 1 1 0 (abl_qofnat n * q) (Qle_refl 1) Hnq0').
Qed.

Lemma abl_qpow_pos : forall (u : Q) (n : nat), Qlt 0 u -> Qlt 0 (abl_qpow u n).
Proof.
  intros u n Hu. induction n as [| n IH].
  - cbn [abl_qpow]. exact abl_qlt_01.
  - cbn [abl_qpow]. exact (Qmult_lt_0_compat u (abl_qpow u n) Hu IH).
Qed.

Lemma abl_qlt_neq0 : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof.
  intros x Hx Hc. apply (Qlt_irrefl 0).
  exact (abl_qlt_eq_r 0 x 0 Hx Hc).
Qed.

(* ============================================================ *)
(* Part C：Bernoulli 下界主件（本片核心交付①）                            *)
(*   (1+q)^n ≥ 1 + n·q（q ≥ 0）——nat 迭代幂，纯 Q 循环归纳：             *)
(*   步进肢两链：1+nq+q ≤ (1+q)^n+q（IH 平移）；(1+q)^n+q ≤ (1+q)^n+q(1+q)^n *)
(*   （q ≤ q·(1+q)^n 由 ≥1 面右乘）；合 (1+q)·(1+q)^n，q²·n 项吸收为换形。 *)
(* ============================================================ *)

Lemma abl_bern_lower : forall (q : Q) (n : nat),
  Qle 0 q -> Qle (1 + abl_qofnat n * q) (abl_qpow (1 + q) n).
Proof.
  intros q n Hq0. induction n as [| n IH].
  - cbn [abl_qpow].
    apply (abl_qle_eq_l (1 + abl_qofnat 0 * q) 1 1).
    + change (abl_qofnat 0) with 0%Q. ring.
    + apply Qle_refl.
  - cbn [abl_qpow].
    assert (Hge1 : Qle 1 (1 + abl_qofnat n * q)) by (apply (abl_boost n q Hq0)).
    assert (Hge1' : Qle 1 (abl_qpow (1 + q) n))
      by (apply (Qle_trans 1 (1 + abl_qofnat n * q) (abl_qpow (1 + q) n) Hge1 IH)).
    assert (Hqle : Qle q (q * abl_qpow (1 + q) n)).
    { apply (abl_qle_eq_l q (1 * q) (q * abl_qpow (1 + q) n)).
      - ring.
      - apply (abl_qle_eq_r (1 * q) (abl_qpow (1 + q) n * q)
                 (q * abl_qpow (1 + q) n)).
        + exact (Qmult_le_compat_r 1 (abl_qpow (1 + q) n) q Hge1' Hq0).
        + ring. }
    apply (abl_qle_eq_l (1 + abl_qofnat (S n) * q)
                        (1 + abl_qofnat n * q + q)
                        ((1 + q) * abl_qpow (1 + q) n)).
    + rewrite (abl_qofnat_S n). ring.
    + apply (abl_qle_eq_r (1 + abl_qofnat n * q + q)
               (abl_qpow (1 + q) n + q * abl_qpow (1 + q) n)
               ((1 + q) * abl_qpow (1 + q) n)).
      * apply (Qle_trans (1 + abl_qofnat n * q + q)
                 (abl_qpow (1 + q) n + q)
                 (abl_qpow (1 + q) n + q * abl_qpow (1 + q) n)).
        -- apply (Qplus_le_compat (1 + abl_qofnat n * q) (abl_qpow (1 + q) n)
                    q q IH (Qle_refl q)).
        -- apply (Qplus_le_compat (abl_qpow (1 + q) n) (abl_qpow (1 + q) n)
                    q (q * abl_qpow (1 + q) n)
                    (Qle_refl (abl_qpow (1 + q) n)) Hqle).
      * ring.
Qed.

(* Bernoulli ≥1 面：(1+q)^n ≥ 1（下界件直取） *)
Lemma abl_qpow_ge1 : forall (q : Q) (n : nat), Qle 0 q -> Qle 1 (abl_qpow (1 + q) n).
Proof.
  intros q n Hq0.
  apply (Qle_trans 1 (1 + abl_qofnat n * q) (abl_qpow (1 + q) n)).
  - exact (abl_boost n q Hq0).
  - exact (abl_bern_lower q n Hq0).
Qed.

(* ============================================================ *)
(* Part D：Hqarch 站点形状接口（本片核心交付②）                           *)
(*   倒数单调（正数上 ≤ 倒下）；幂倒数换形；Bernoulli 下形 ⟹ 收缩幂上界；  *)
(*   收束于 sigT 形（Hqarch 前件谓词体同形，abl_qpow↔mixe_qpow 同体）。    *)
(* ============================================================ *)

Lemma abl_qmult_cancel_r : forall (a x y : Q),
  ~ (a == 0) -> Qeq (x * a) (y * a) -> Qeq x y.
Proof.
  intros a x y Ha Hc.
  assert (Hs1 : Qeq x (x * (a * / a))).
  { rewrite (Qmult_inv_r a Ha). symmetry. apply Qmult_1_r. }
  assert (Hs2 : Qeq (x * (a * / a)) (x * a * / a)) by (apply Qmult_assoc).
  assert (Hs3 : Qeq (x * a * / a) (y * a * / a)) by (rewrite Hc; apply Qeq_refl).
  assert (Hs4 : Qeq (y * a * / a) (y * (a * / a))).
  { exact (Qeq_sym _ _ (Qmult_assoc y a (/ a))). }
  assert (Hs5 : Qeq (y * (a * / a)) y).
  { rewrite (Qmult_inv_r a Ha). apply Qmult_1_r. }
  exact (Qeq_trans _ _ _ Hs1 (Qeq_trans _ _ _ Hs2 (Qeq_trans _ _ _ Hs3 (Qeq_trans _ _ _ Hs4 Hs5)))).
Qed.

Lemma abl_qinv_eq_compat_nz : forall a b : Q,
  ~ (a == 0) -> Qeq a b -> Qeq (/ a) (/ b).
Proof.
  intros a b Ha Hab.
  assert (Hb0 : ~ (b == 0)).
  { intro Hc. apply Ha. rewrite <- Hc. exact Hab. }
  apply (abl_qmult_cancel_r a (/ a) (/ b) Ha).
  apply (Qeq_trans (/ a * a) 1 ((/ b) * a)).
  - rewrite (Qmult_comm (/ a) a). apply (Qmult_inv_r a Ha).
  - rewrite Hab. rewrite (Qmult_comm (/ b) b).
    symmetry. apply (Qmult_inv_r b Hb0).
Qed.

Lemma abl_qinv_le_contravar : forall a b : Q,
  Qlt 0 a -> Qlt 0 b -> Qle a b -> Qle (/ b) (/ a).
Proof.
  intros a b Ha Hb Hab.
  destruct (Qlt_le_dec a b) as [Hlt | Hge].
  - apply (Qlt_le_weak (/ b) (/ a)).
    exact (proj1 (Qinv_lt_contravar a b Ha Hb) Hlt).
  - apply abl_qeq_le.
    exact (abl_qinv_eq_compat_nz b a (abl_qlt_neq0 b Hb)
             (Qeq_sym _ _ (Qle_antisym a b Hab Hge))).
Qed.

Lemma abl_qpow_ext : forall (u v : Q) (n : nat),
  Qeq u v -> Qeq (abl_qpow u n) (abl_qpow v n).
Proof.
  intros u v n H. induction n as [| n IH].
  - apply Qeq_refl.
  - cbn [abl_qpow].
    apply (Qeq_trans _ (v * abl_qpow u n) _).
    + exact (abl_qmult_eq_l u v (abl_qpow u n) H).
    + rewrite IH. apply Qeq_refl.
Qed.

Lemma abl_qpow_inv : forall (u : Q) (n : nat),
  Qeq (abl_qpow (/ u) n) (/ (abl_qpow u n)).
Proof.
  intros u n. induction n as [| n IH].
  - cbn [abl_qpow]. apply Qeq_refl.
  - cbn [abl_qpow]. rewrite IH.
    exact (Qeq_sym _ _ (Qinv_mult_distr u (abl_qpow u n))).
Qed.

(* Bernoulli ⟹ 收缩步：p == 1/(1+w)，0 < v，v ≤ b·(1+n·w) ⟹ p^n·v ≤ b。
   证链：p^n == 1/(1+w)^n（幂倒数换形）≤ 1/(1+n·w)（Bernoulli 下界倒数化，
   正数上倒数反序）⟹ 乘 v 并以 (1+n·w) 倒数归一。
   四值前提 (0<w, 0<v, 0<b, p==1/(1+w)) 与 Hqarch 站点口径对齐。 *)
Lemma abl_hqarch_bern_step : forall (p w v b : Q) (n : nat),
  Qeq p (/ (1 + w)) -> Qle 0 w -> Qlt 0 v -> Qlt 0 b ->
  Qle v (b * (1 + abl_qofnat n * w)) ->
  Qle (abl_qpow p n * v) b.
Proof.
  intros p w v b n Hp Hw0 Hvt0 Hb0 Hv.
  assert (Hv0 : Qle 0 v) by (apply (Qlt_le_weak 0 v); exact Hvt0).
  assert (Hge : Qle 1 (1 + w)).
  { apply (abl_qle_eq_l 1 (1 + 0) (1 + w)).
    - ring.
    - exact (Qplus_le_compat 1 1 0 w (Qle_refl 1) Hw0). }
  assert (Hp1 : Qlt 0 (1 + w)) by (apply (Qlt_le_trans 0 1 (1 + w) abl_qlt_01 Hge)).
  assert (Hpowpos : Qlt 0 (abl_qpow (1 + w) n)) by (apply (abl_qpow_pos (1 + w) n Hp1)).
  assert (Hpowne : ~ (abl_qpow (1 + w) n == 0)) by (apply (abl_qlt_neq0 _ Hpowpos)).
  assert (HYpos : Qlt 0 (1 + abl_qofnat n * w))
    by (apply (Qlt_le_trans 0 1 (1 + abl_qofnat n * w) abl_qlt_01 (abl_boost n w Hw0))).
  assert (HYne : ~ (1 + abl_qofnat n * w == 0)) by (apply (abl_qlt_neq0 _ HYpos)).
  assert (HYinvpos : Qlt 0 (/ (1 + abl_qofnat n * w))) by (apply (Qinv_lt_0_compat _ HYpos)).
  assert (Hmp : Qeq (abl_qpow p n) (/ (abl_qpow (1 + w) n))).
  { apply (Qeq_trans _ (abl_qpow (/ (1 + w)) n) _).
    - exact (abl_qpow_ext p (/ (1 + w)) n Hp).
    - exact (abl_qpow_inv (1 + w) n). }
  assert (Hmono : Qle (/ (abl_qpow (1 + w) n)) (/ (1 + abl_qofnat n * w))).
  { apply (abl_qinv_le_contravar (1 + abl_qofnat n * w) (abl_qpow (1 + w) n)
             HYpos Hpowpos).
    exact (abl_bern_lower w n Hw0). }
  assert (Hstep1 : Qle (abl_qpow p n * v) (v * / (1 + abl_qofnat n * w))).
  { apply (abl_qle_eq_r (abl_qpow p n * v) (/ (1 + abl_qofnat n * w) * v)
             (v * / (1 + abl_qofnat n * w))).
    - apply (abl_qle_eq_l (abl_qpow p n * v) (/ (abl_qpow (1 + w) n) * v)
               (/ (1 + abl_qofnat n * w) * v)).
      + exact (abl_qmult_eq_l _ _ v Hmp).
      + exact (Qmult_le_compat_r (/ (abl_qpow (1 + w) n))
                   (/ (1 + abl_qofnat n * w)) v Hmono Hv0).
    - ring. }
  assert (Hcancel : Qeq ((b * (1 + abl_qofnat n * w)) * / (1 + abl_qofnat n * w)) b).
  { rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r (1 + abl_qofnat n * w) HYne).
    apply Qmult_1_r. }
  assert (Hstep2 : Qle (v * / (1 + abl_qofnat n * w)) b).
  { apply (abl_qle_eq_r (v * / (1 + abl_qofnat n * w))
             ((b * (1 + abl_qofnat n * w)) * / (1 + abl_qofnat n * w)) b).
    - exact (Qmult_le_compat_r v (b * (1 + abl_qofnat n * w))
                 (/ (1 + abl_qofnat n * w)) Hv
                 (Qlt_le_weak 0 (/ (1 + abl_qofnat n * w)) HYinvpos)).
    - exact Hcancel. }
  exact (Qle_trans _ _ _ Hstep1 Hstep2).
Qed.

(* 规范耦合：w := /p - 1（= (1-p)/p）满足 1 + w == 1/p，即 p == 1/(1+w)。 *)
Lemma abl_canon_w_inv : forall p : Q, Qeq p (/ (1 + (/ p - 1))).
Proof.
  intros p.
  assert (Hs : (1 + (/ p - 1))%Q == (/ p)%Q) by ring.
  rewrite Hs. symmetry. apply Qinv_involutive.
Qed.

Lemma abl_canon_w_pos : forall p : Q, Qlt 0 p -> Qlt p 1 -> Qlt 0 (/ p - 1).
Proof.
  intros p Hp0 Hp1.
  apply (proj1 (Qlt_minus_iff 1 (/ p))).
  apply (abl_qlt_eq_l 1 (/ 1) (/ p)).
  - apply Qeq_refl.
  - exact (proj1 (Qinv_lt_contravar p 1 Hp0 abl_qlt_01) Hp1).
Qed.

(* Hqarch 站点形状闭合：前件四值前提与源件 L319 逐项同形
   (Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b) + Bernoulli 桥步 ⟹ sigT 见证。
   与站点唯一文本差：幂件 abl_qpow 与 mixe_qpow 同体更名（头注接口对应说明）。
   下片（2/2 桥接件）只需由 Q 层 Archimedean 生产末前件的 n 见证。 *)
Lemma abl_hqarch_via_bern : forall (p v b : Q) (n : nat),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  Qle v (b * (1 + abl_qofnat n * (/ p - 1))) ->
  sigT (fun j : nat => Qle (abl_qpow p j * v) b).
Proof.
  intros p v b n Hp0 Hp1 Hvt0 Hb0 Hv.
  exists n.
  apply (abl_hqarch_bern_step p (/ p - 1) v b n).
  - exact (abl_canon_w_inv p).
  - apply (Qlt_le_weak 0 (/ p - 1)). exact (abl_canon_w_pos p Hp0 Hp1).
  - exact Hvt0.
  - exact Hb0.
  - exact Hv.
Qed.

(* ============================================================ *)
(* 检验审计：提取 Obj.magic 计数应为 0 + 逐件假设闭包                      *)
(* ============================================================ *)

Extraction "abl_hqarch_bern_04_G3.ml" abl_bern_lower abl_qpow_ge1
  abl_hqarch_bern_step abl_hqarch_via_bern.

Print Assumptions abl_qlt_01.
Print Assumptions abl_qeq_le.
Print Assumptions abl_qle_eq_l.
Print Assumptions abl_qle_eq_r.
Print Assumptions abl_qlt_eq_l.
Print Assumptions abl_qlt_eq_r.
Print Assumptions abl_qmult_eq_l.
Print Assumptions abl_qofnat_nonneg.
Print Assumptions abl_qofnat_S.
Print Assumptions abl_boost.
Print Assumptions abl_qpow_pos.
Print Assumptions abl_bern_lower.
Print Assumptions abl_qpow_ge1.
Print Assumptions abl_qlt_neq0.
Print Assumptions abl_qmult_cancel_r.
Print Assumptions abl_qinv_eq_compat_nz.
Print Assumptions abl_qinv_le_contravar.
Print Assumptions abl_qpow_ext.
Print Assumptions abl_qpow_inv.
Print Assumptions abl_hqarch_bern_step.
Print Assumptions abl_canon_w_inv.
Print Assumptions abl_canon_w_pos.
Print Assumptions abl_hqarch_via_bern.
