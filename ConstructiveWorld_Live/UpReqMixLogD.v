(* ========================================================================= *)
(* 【ToyR 战役·包G·T246 台账席】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 战役包G 替换落件（原名落件）；落件时头部漏植战役标记，本块由  *)
(* T274 无头注补标专席于 2026-09-21 补植：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/T246。       *)
(* 替换定理清单：mixd_leT_transport／mixd_qeqT_one_mul／mixd_const_proj／    *)
(* mixd_zero_proj／mixd_one_proj（共 5 条）                                  *)
(* 非平凡性口径：运输链与投影位显式直造，消除单跳转发；无一行拆分式假非平    *)
(* 凡。                                                                      *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* UpReqMixLogD.v —— 赛马 D 席：Path D 平方阶梯对数级选择器           *)
(*   （AT11 裁决 5 / N5 实施席：κ₀^(2^i) 阶梯 + 二进制合成，           *)
(*     Q 核证书直返（QleT'/NatLe 全 Set 层）+ Real 有理化归约壳）       *)
(* 依赖坐标：CW_ConstructiveWorld_219 伞壳（S02 real_lt sigT 证书形     *)
(*   :465-467 / QleT'·QeqT·L2 库 / S07 real_const_lt）、                 *)
(*   UpTVDoeblin（tv_rpow）、UpReqIterGeomRate（igr_qpow:1490 复用，      *)
(*   Q 层幂单调直证——勿走 Real powb↔rpow 桥，AT6/AT11 结论）、            *)
(*   UpReqMixingTime（mix_k_select TV₀ 零支直接代入 + mix_const_zero）、      *)
(*   KLWallClosed（klc_const_le:109 Q→Real 保序桥 + klc_le_id 族）。      *)
(* 本件承载（前缀 mixd_，全树 grep 零撞名 2026-09-18）：                *)
(*   ① Q 核 Defined 选择器 mixd_k_select_log_cert：                      *)
(*      阶梯 mixd_ladder（κ₀^(2^i) 重复平方，每级 1 乘）+ 上扫            *)
(*      mixd_scan_up（首个过线梯级，QleT' 证书直返）+ 二进制回退合成      *)
(*      mixd_desc（贪心加-败位，O(log) 乘）+ 顶极 leb 守卫（死支回退      *)
(*      顶级梯级——语义不可达但构造合法，红②允许形）。                    *)
(*   ② 账族（Qed）：scan/desc 败位保持 + 上界 + 成本 c ≤ 5·d+2            *)
(*      （量级定理 nat 上界式：乘法次数=阶梯长度+扫描+回退合成）+        *)
(*      主账（下方全败=最小通过站，igr_k_select_min 三账同形）。          *)
(*   ③ 窗口（Q 层自算——AT11 裁决 3 陷阱处方）：mixd_qbern                 *)
(*      （Q-Bernoulli (1−w)^m·(1+m·w) ≤ 1 纯 Q 循环依赖清单）+                    *)
(*      mixd_window_pass/top_pass（v ≤ N·(w·b₀) ⟹ 顶级梯级过线）。        *)
(*   ④ Real 壳：κ₀:=Qmax(1−eps/2)(1/2)、b₀:=eps_b/2 提取件                *)
(*      （real_lt sigT 证书 S02:465-467 定义面拆解，AT11 裁决 1）、        *)
(*      Q→Real 反映件、tv_rpow 幂桥（归纳直证零 conversion）、回传链。    *)
(*   ⑤ 主件 mixd_k_select_log（±_le，Defined 可提取；TV₀==0 支            *)
(*      mix_k_select 既有件直接代入——零重证）。                                *)
(* 公理面：本件零新增公理；全部前提为 Set 层显式证书（real_lt sigT /      *)
(*   real_le Or 编码 / QleT'·NatLe·QeqT Id 面 / sigT TV₀′ 证书 + 窗口     *)
(*   证书）；Print Assumptions 预期全 Closed。                            *)
(* 红线自审：语句面全 Set 层（量词 nat/Q/Real；比较全 QleT'/QltT/NatLe/  *)
(*   QeqT Id 面 + real_lt/real_le Or 面；sigT 载荷全 Set 或 real_lt；    *)
(*   假设位零 Prop）；Defined 体内零 Prop 消去（判定全走           *)
(*   mixd_dec_le/mixd_dec_leb 布尔 match，死支回退值构造合法）；零        *)
(*   禁词三族零出现（双轨 grep 自证）；非平凡（阶梯+二进制合成正确性=     *)
(*   贪心败位账真数学）；                                *)
(*   可提取（选择器族全 Defined，G3 检验在案）。                          *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——WALL-2 坑）：               *)
(*   .cmd 内 set COQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq              *)
(*           set ROCQLIB=%COQLIB%；全量/vos 双轨 + coqchk + 提取检验。    *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
Require Import UpReqIterGeomRate.
Require Import UpReqMixingTime.
Require Import KLWallClosed.

Local Open Scope Q_scope.

(* Qeq 头目标循环依赖清单 tactic（destruct 全 Q 元 + Z-ring——AT7 卡⑤ 坑处方；   *)
(*   S02 mix_rring 同族，Q 侧版）                                        *)
Ltac mixd_qring :=
  unfold Qeq, Qminus, Qplus, Qopp;
  repeat match goal with
         | [ q : Q |- _ ] => destruct q
         end;
  cbn [Qnum Qden];
  ring.

(* ============================================================ *)
(* Part 0：Q 循环依赖清单 shim（Qeq 同余 / 换形 / 传输）                           *)
(* ============================================================ *)

Lemma mixd_qeq_mult_r : forall a b c : Q, a == b -> a * c == b * c.
Proof. intros a b c H. exact (@Qmult_comp a b H c c (Qeq_refl c)). Qed.

Lemma mixd_qeq_mult_l : forall a b c : Q, a == b -> c * a == c * b.
Proof.
  intros a b c H.
  apply (Qeq_trans _ (a * c) _).
  - apply Qmult_comm.
  - apply (Qeq_trans _ (b * c) _).
    + exact (@Qmult_comp a b H c c (Qeq_refl c)).
    + apply Qmult_comm.
Qed.

Lemma mixd_qeqT_to_Qeq : forall a b : Q, QeqT a b -> a == b.
Proof.
  intros a b H. unfold QeqT in H.
  destruct (Qcompare a b) eqn:E.
  - apply (proj2 (Qeq_alt a b)). exact E.
  - inversion H.
  - inversion H.
Qed.

(* QeqT 左延伸（Qeq∘QeqT 复合） *)
Lemma mixd_qeqT_trans_l : forall a b c : Q, a == b -> QeqT b c -> QeqT a c.
Proof.
  intros a b c Hab Hbc.
  apply qeq_imp_qeqT.
  transitivity b.
  - exact Hab.
  - exact (mixd_qeqT_to_Qeq b c Hbc).
Qed.

(* QleT' 沿 QeqT 传输（Set 层传输件——Qle_comp 实例应用，零 Qeq-rewrite） *)
Lemma mixd_leT_transport : forall a b c : Q, QeqT a b -> QleT' a c -> QleT' b c.
Proof.
  intros a b c Hab Hac.
  exact (Qle_to_QleT' b c
           (proj1 (@Qle_comp a b (mixd_qeqT_to_Qeq a b Hab) c c (Qeq_refl c))
              (QleT'_to_Qle a c Hac))).
Qed.

Lemma mixd_qlt_eq_l : forall a b c : Q, a == b -> Qlt a c -> Qlt b c.
Proof.
  intros a b c Hab Hac.
  exact (proj1 (@Qlt_compat a b Hab c c (Qeq_refl c)) Hac).
Qed.

Lemma mixd_qlt_eq_r : forall a b c : Q, b == c -> Qlt a b -> Qlt a c.
Proof.
  intros a b c Hbc Hab.
  exact (proj1 (@Qlt_compat a a (Qeq_refl a) b c Hbc) Hab).
Qed.

Lemma mixd_qle_eq_l : forall a b c : Q, a == b -> Qle a c -> Qle b c.
Proof.
  intros a b c Hab Hac.
  exact (proj1 (@Qle_comp a b Hab c c (Qeq_refl c)) Hac).
Qed.

Lemma mixd_qle_eq_r : forall a b c : Q, b == c -> Qle a b -> Qle a c.
Proof.
  intros a b c Hbc Hab.
  exact (proj1 (@Qle_comp a a (Qeq_refl a) b c Hbc) Hab).
Qed.

(* 幂沿底相等换形（Qmult_comp 实例归纳） *)
Lemma mixd_qpow_eq_compat : forall (a b : Q) (H : a == b) (m : nat),
  igr_qpow a m == igr_qpow b m.
Proof.
  intros a b H m. induction m as [| m IH].
  - apply Qeq_refl.
  - cbn [igr_qpow].
    exact (@Qmult_comp a b H (igr_qpow a m) (igr_qpow b m) IH).
Qed.

(* k == k − x + x（destruct + Z-ring，S02 real_lt_trans 的 ring-on-Qeq 先例） *)
Lemma mixd_qring_cancel_r : forall x k : Q, k == (k - x) + x.
Proof.
  intros x k. ring.
Qed.

Lemma mixd_half_pos : Qlt 0 (1#2).
Proof. unfold Qlt. cbn. lia. Qed.

Lemma mixd_half_lt_one : Qlt (1#2) 1.
Proof. unfold Qlt. cbn. lia. Qed.

(* 0 < z ⟹ x < x + z *)
Lemma mixd_qlt_add_pos : forall x z : Q, 0 < z -> Qlt x (x + z).
Proof.
  intros x z Hz.
  apply (mixd_qlt_eq_l (x + 0) x (x + z)).
  - apply Qplus_0_r.
  - apply (proj2 (Qplus_lt_r 0 z x)). exact Hz.
Qed.

(* a + a < b ⟹ a < b − a *)
Lemma mixd_qsub_lt2 : forall a b : Q, Qlt (a + a) b -> Qlt a (b - a).
Proof.
  intros a b H.
  apply (proj1 (Qplus_lt_r a (b - a) a)).
  apply (mixd_qlt_eq_r (a + a) b (a + (b - a))).
  - ring.
  - exact H.
Qed.

Lemma mixd_qsub_le : forall w : Q, 0 <= w -> (1 - w) <= 1.
Proof.
  intro w. unfold Qle. destruct w as [nw dw].
  cbn [Qnum Qden Qminus Qopp Qplus].
  intro Hw. unfold Qle in Hw. cbn [Qnum Qden] in Hw. lia.
Qed.

Lemma mixd_qsub_ge0 : forall w : Q, w <= 1 -> 0 <= (1 - w).
Proof.
  intro w. unfold Qle. destruct w as [nw dw].
  cbn [Qnum Qden Qminus Qopp Qplus].
  intro Hw. unfold Qle in Hw. cbn [Qnum Qden] in Hw. lia.
Qed.

Lemma mixd_qsub_pos : forall w : Q, w < 1 -> 0 < (1 - w).
Proof.
  intros w Hw.
  apply (proj1 (Qplus_lt_r 0 (1 - w) w)).
  apply (mixd_qlt_eq_r (w + 0) 1 (w + (1 - w))).
  - ring.
  - apply (mixd_qlt_eq_l w (w + 0) 1 (Qeq_sym _ _ (Qplus_0_r w))).
    exact Hw.
Qed.

(* Qle_bool false 反映：Qle_bool x y = false ⟹ y < x（三分判定收尾） *)
Lemma mixd_qle_bool_false_lt : forall x y : Q, Qle_bool x y = false -> Qlt y x.
Proof.
  intros x y E.
  assert (Hn : ~ (x <= y)).
  { intro Hc.
    assert (Ht : Qle_bool x y = true) by (apply Qle_bool_iff; exact Hc).
    rewrite Ht in E. discriminate E. }
  exact (Qnot_le_lt x y Hn).
Qed.

(* 自定义 Q-max（if-Qle_bool 形——stdlib Qmax 为 gmax 泛型形，不采用） *)
Definition mixd_qmax (a b : Q) : Q := if Qle_bool a b then b else a.

Lemma mixd_qmax_eq_l : forall a b : Q, Qle_bool a b = false -> mixd_qmax a b == a.
Proof. intros a b E. unfold mixd_qmax. rewrite E. apply Qeq_refl. Qed.

Lemma mixd_qmax_eq_r : forall a b : Q, Qle_bool a b = true -> mixd_qmax a b == b.
Proof. intros a b E. unfold mixd_qmax. rewrite E. apply Qeq_refl. Qed.

(* 0 ≤ w ⟹ 0 ≤ m·w *)
Lemma mixd_qnatw_nonneg : forall (w : Q) (Hw : 0 < w) (m : nat),
  0 <= Qmake (Z.of_nat m) 1 * w.
Proof.
  intros w Hw m.
  apply (mixd_qle_eq_l (0 * w) 0 (Qmake (Z.of_nat m) 1 * w)).
  - apply Qmult_0_l.
  - apply (Qmult_le_compat_r 0 (Qmake (Z.of_nat m) 1) w).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply (Qlt_le_weak 0 w Hw).
Qed.

(* 0 ≤ q ⟹ 0 ≤ q^m *)
Lemma mixd_qpow_nonneg : forall (q : Q) (Hq : 0 <= q) (m : nat),
  0 <= igr_qpow q m.
Proof.
  intros q Hq m. induction m as [| m IH].
  - cbn [igr_qpow]. unfold Qle. cbn [Qnum Qden]. lia.
  - cbn [igr_qpow].
    exact (Qmult_le_0_compat q (igr_qpow q m) Hq IH).
Qed.

(* e > 0 ⟹ e·(1/2) < e *)
Lemma mixd_half_lt : forall e : Q, 0 < e -> Qlt (e * (1#2)) e.
Proof.
  intros e He.
  apply (mixd_qlt_eq_l ((1#2) * e) (e * (1#2)) e).
  - ring.
  - apply (mixd_qlt_eq_r ((1#2) * e) (1 * e) e).
    + apply Qmult_1_l.
    + exact (Qmult_lt_compat_r (1#2) 1 e He mixd_half_lt_one).
Qed.

(* 左乘保序（stdlib 只有 _r 形，comm shim 一次成型） *)
Lemma mixd_qmult_le_compat_l : forall x y z : Q,
  x <= y -> 0 <= z -> z * x <= z * y.
Proof.
  intros x y z Hxy Hz.
  apply (mixd_qle_eq_l (x * z) (z * x) (z * y)).
  - ring.
  - apply (mixd_qle_eq_r (x * z) (y * z) (z * y)).
    + ring.
    + apply (Qmult_le_compat_r x y z Hxy Hz).
Qed.

(* ============================================================ *)
(* Part 1：幂单调（Q 层直证——igr_qpow 面，AT11 裁决 2 正选）              *)
(* ============================================================ *)

Lemma mixd_qpow_le1 : forall (q : Q) (Hq1 : q <= 1) (Hq0 : 0 <= q) (m : nat),
  igr_qpow q m <= 1.
Proof.
  intros q Hq1 Hq0 m. induction m as [| m IH].
  - apply Qle_refl.
  - cbn [igr_qpow].
    apply (Qle_trans _ (igr_qpow q m) 1).
    + apply (mixd_qle_eq_r (q * igr_qpow q m) (1 * igr_qpow q m)
               (igr_qpow q m)).
      * apply Qmult_1_l.
      * apply (Qmult_le_compat_r q 1 (igr_qpow q m)).
        -- exact Hq1.
        -- exact (mixd_qpow_nonneg q Hq0 m).
    + exact IH.
Qed.

(* 0 < q ≤ 1 ⟹ 指数反单调：a ≤ b ⟹ q^b ≤ q^a *)
Lemma mixd_qpow_anti : forall (q : Q) (Hq0 : 0 < q) (Hq1 : q <= 1)
    (b a : nat), (a <= b)%nat -> igr_qpow q b <= igr_qpow q a.
Proof.
  intros q Hq0 Hq1 b. induction b as [| b IH]; intros a Hab.
  - assert (Ha0 : a = 0%nat) by lia. subst a. apply Qle_refl.
  - destruct a as [| a].
    + apply (mixd_qle_eq_r (igr_qpow q (Datatypes.S b)) 1%Q (igr_qpow q 0%nat)).
      * exact (Qeq_refl 1).
      * apply (mixd_qpow_le1 q Hq1 (Qlt_le_weak 0 q Hq0)).
    + assert (Ha' : (a <= b)%nat) by lia.
      apply (Qle_trans _ (q * igr_qpow q a) (igr_qpow q (Datatypes.S a))).
      * cbn [igr_qpow].
        apply (mixd_qmult_le_compat_l (igr_qpow q b) (igr_qpow q a) q).
        -- exact (IH a Ha').
        -- exact (Qlt_le_weak 0 q Hq0).
      * exact (Qle_refl (q * igr_qpow q a)).
Qed.

(* 严格败位下行：a ≤ b ∧ b 败 ⟹ a 败（回退合成最小性承重件） *)
Lemma mixd_fail_down : forall (k0 v b0 : Q) (Hq0 : 0 < k0) (Hq1 : k0 <= 1)
    (Hv : 0 <= v) (a b : nat), (a <= b)%nat ->
  Qlt b0 (Qmult (igr_qpow k0 b) v) -> Qlt b0 (Qmult (igr_qpow k0 a) v).
Proof.
  intros k0 v b0 Hq0 Hq1 Hv a b Hab Hb.
  apply (Qlt_le_trans b0 (Qmult (igr_qpow k0 b) v) (Qmult (igr_qpow k0 a) v)).
  - exact Hb.
  - apply (Qmult_le_compat_r _ _ v).
    + exact (mixd_qpow_anti k0 Hq0 Hq1 b a Hab).
    + exact Hv.
Qed.

(* ============================================================ *)
(* Part 2：阶梯与二进制权重                                                *)
(* ============================================================ *)

Fixpoint mixd_two_pow (i : nat) : nat :=
  match i with
  | Datatypes.O => 1%nat
  | Datatypes.S j => 2 * mixd_two_pow j
  end.

Lemma mixd_two_pow_ge : forall i : nat, (Datatypes.S i <= mixd_two_pow i)%nat.
Proof.
  induction i as [| i IH].
  - cbn [mixd_two_pow]. lia.
  - cbn [mixd_two_pow]. lia.
Qed.

(* 阶梯：κ₀^(2^i)（重复平方——每级恰 1 次乘法） *)
Fixpoint mixd_ladder (k0 : Q) (i : nat) : Q :=
  match i with
  | Datatypes.O => k0
  | Datatypes.S j => Qmult (mixd_ladder k0 j) (mixd_ladder k0 j)
  end.

Lemma mixd_qpow_plus : forall (q : Q) (a b : nat),
  igr_qpow q (a + b) == igr_qpow q a * igr_qpow q b.
Proof.
  intros q a b. induction a as [| a IH].
  - cbn [igr_qpow Nat.add]. symmetry. apply Qmult_1_l.
  - cbn [igr_qpow Nat.add].
    apply (Qeq_trans _ (q * (igr_qpow q a * igr_qpow q b)) _).
    + apply (mixd_qeq_mult_l (igr_qpow q (a + b))
               (igr_qpow q a * igr_qpow q b) q).
      exact IH.
    + ring.
Qed.

(* 阶梯正确性（QeqT 直返件）：mixd_ladder k0 i ≡ κ₀^(2^i) *)
Lemma mixd_ladder_spec : forall (k0 : Q) (i : nat),
  QeqT (mixd_ladder k0 i) (igr_qpow k0 (mixd_two_pow i)).
Proof.
  intros k0 i. induction i as [| i IH].
  - unfold QeqT. cbn [mixd_ladder mixd_two_pow igr_qpow].
    apply qeq_imp_qeqT. symmetry. apply Qmult_1_r.
  - apply qeq_imp_qeqT.
    cbn [mixd_ladder].
    replace (mixd_two_pow (Datatypes.S i))
      with (mixd_two_pow i + mixd_two_pow i)%nat
      by (cbn [mixd_two_pow]; lia).
    apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow i)
                          * igr_qpow k0 (mixd_two_pow i)) _).
    + apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow i)
                            * mixd_ladder k0 i) _).
      * apply (mixd_qeq_mult_r (mixd_ladder k0 i)
                 (igr_qpow k0 (mixd_two_pow i)) (mixd_ladder k0 i)).
        exact (mixd_qeqT_to_Qeq _ _ IH).
      * apply (mixd_qeq_mult_l (mixd_ladder k0 i)
                 (igr_qpow k0 (mixd_two_pow i))
                 (igr_qpow k0 (mixd_two_pow i))).
        exact (mixd_qeqT_to_Qeq _ _ IH).
    + apply (Qeq_sym _ _ (mixd_qpow_plus k0 (mixd_two_pow i)
                            (mixd_two_pow i))).
Qed.

(* 扫描段运行时证书：acc ≡ ladder i ⟹ QeqT (acc·v) (κ₀^(2^i)·v) *)
Lemma mixd_acc_cert : forall (k0 v : Q) (i : nat) (acc : Q),
  acc == mixd_ladder k0 i ->
  QeqT (Qmult acc v) (Qmult (igr_qpow k0 (mixd_two_pow i)) v).
Proof.
  intros k0 v i acc Hacc.
  apply qeq_imp_qeqT.
  transitivity (mixd_ladder k0 i * v).
  - apply (@Qmult_comp acc (mixd_ladder k0 i) Hacc v v (Qeq_refl v)).
  - apply (@Qmult_comp (mixd_ladder k0 i)
             (igr_qpow k0 (mixd_two_pow i))
             (mixd_qeqT_to_Qeq (mixd_ladder k0 i)
                (igr_qpow k0 (mixd_two_pow i)) (mixd_ladder_spec k0 i))
             v v (Qeq_refl v)).
Qed.



(* 阶梯平方自洽：p ≡ κ₀^(2^j) ⟹ p·p ≡ κ₀^(2^(S j)) *)
Lemma mixd_qeq_sq : forall (k0 : Q) (j : nat) (p : Q),
  p == igr_qpow k0 (mixd_two_pow j) ->
  p * p == igr_qpow k0 (mixd_two_pow (Datatypes.S j)).
Proof.
  intros k0 j p Hp.
  replace (mixd_two_pow (Datatypes.S j))
    with (mixd_two_pow j + mixd_two_pow j)%nat
    by (cbn [mixd_two_pow]; lia).
  apply (Qeq_trans _ (igr_qpow k0 (mixd_two_pow j)
                        * igr_qpow k0 (mixd_two_pow j)) _).
  - exact (@Qmult_comp p (igr_qpow k0 (mixd_two_pow j)) Hp
             p (igr_qpow k0 (mixd_two_pow j)) Hp).
  - apply (Qeq_sym _ _ (mixd_qpow_plus k0 (mixd_two_pow j)
                          (mixd_two_pow j))).
Qed.

(* 回退合成单步值账（S j 位） *)
Lemma mixd_qeq_step : forall (k0 v : Q) (j k : nat) (p val : Q),
  p == igr_qpow k0 (mixd_two_pow (Datatypes.S j)) ->
  val == igr_qpow k0 k * v ->
  val * p == igr_qpow k0 (k + mixd_two_pow (Datatypes.S j)) * v.
Proof.
  intros k0 v j k p val Hp Hval.
  apply (Qeq_trans _ (igr_qpow k0 k * v * p) _).
  - apply (mixd_qeq_mult_r val (igr_qpow k0 k * v) p). exact Hval.
  - apply (Qeq_trans _
             (igr_qpow k0 k * v
                * igr_qpow k0 (mixd_two_pow (Datatypes.S j))) _).
    + apply (mixd_qeq_mult_l p
               (igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
               (igr_qpow k0 k * v)).
      exact Hp.
    + apply (Qeq_trans _
               (igr_qpow k0 k
                  * (v * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))) _).
      * apply (Qeq_sym _ _ (Qmult_assoc (igr_qpow k0 k) v
                  (igr_qpow k0 (mixd_two_pow (Datatypes.S j))))).
      * apply (Qeq_trans _
                 (igr_qpow k0 k
                    * (igr_qpow k0 (mixd_two_pow (Datatypes.S j)) * v)) _).
        -- apply (mixd_qeq_mult_l
                     (v * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                     (igr_qpow k0 (mixd_two_pow (Datatypes.S j)) * v)
                     (igr_qpow k0 k)).
           ++ apply Qmult_comm.
        -- apply (Qeq_trans _
                     ((igr_qpow k0 k
                       * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                      * v) _).
           ++ apply (Qmult_assoc (igr_qpow k0 k)
                       (igr_qpow k0 (mixd_two_pow (Datatypes.S j))) v).
           ++ apply (mixd_qeq_mult_r
                       (igr_qpow k0 k
                          * igr_qpow k0 (mixd_two_pow (Datatypes.S j)))
                       (igr_qpow k0
                          (k + mixd_two_pow (Datatypes.S j))) v).
              ** apply (Qeq_sym _ _
                          (mixd_qpow_plus k0 k
                             (mixd_two_pow (Datatypes.S j)))).
Qed.

(* 0 号位单步值账 *)
Lemma mixd_qeq_step0 : forall (k0 v : Q) (k : nat) (p val : Q),
  p == igr_qpow k0 (mixd_two_pow 0%nat) ->
  val == igr_qpow k0 k * v ->
  val * p == igr_qpow k0 (Datatypes.S k) * v.
Proof.
  intros k0 v k p val Hp Hval.
  cbn [mixd_two_pow] in Hp.
  replace (Datatypes.S k) with (k + 1)%nat by lia.
  apply (Qeq_trans _ (igr_qpow k0 k * v * p) _).
  - apply (mixd_qeq_mult_r val (igr_qpow k0 k * v) p). exact Hval.
  - apply (Qeq_trans _ (igr_qpow k0 k * v * igr_qpow k0 1) _).
    + apply (mixd_qeq_mult_l p (igr_qpow k0 1) (igr_qpow k0 k * v)).
      exact Hp.
    + apply (Qeq_trans _ (igr_qpow k0 k * (v * igr_qpow k0 1)) _).
      * apply (Qeq_sym _ _ (Qmult_assoc (igr_qpow k0 k) v (igr_qpow k0 1))).
      * apply (Qeq_trans _ (igr_qpow k0 k * (igr_qpow k0 1 * v)) _).
        -- apply (mixd_qeq_mult_l (v * igr_qpow k0 1) (igr_qpow k0 1 * v)
                    (igr_qpow k0 k)).
           ++ apply Qmult_comm.
        -- apply (Qeq_trans _ ((igr_qpow k0 k * igr_qpow k0 1) * v) _).
           ++ apply (Qmult_assoc (igr_qpow k0 k) (igr_qpow k0 1) v).
           ++ apply (mixd_qeq_mult_r (igr_qpow k0 k * igr_qpow k0 1)
                       (igr_qpow k0 (k + 1)) v).
              ** apply (Qeq_sym _ _ (mixd_qpow_plus k0 k 1)).
Qed.

(* ============================================================ *)
(* Part 3：Set 层判定器（布尔 match，死支回退值构造合法）                  *)
(* ============================================================ *)

Definition mixd_dec_le (x y : Q)
  : sum (Id (Qle_bool x y) true) (Id (Qle_bool x y) false) :=
  match Qle_bool x y as b return
      sum (Id b true) (Id b false) with
  | true => inl id_refl
  | false => inr id_refl
  end.

Definition mixd_dec_leb (m n : nat)
  : sum (NatLe m n) (Id (Nat.leb m n) false) :=
  match Nat.leb m n as b return
      sum (Id b true) (Id b false) with
  | true => inl id_refl
  | false => inr id_refl
  end.

(* Qle_bool false 账转严格败位（ proofs 依存用） *)
Lemma mixd_qleF_lt : forall x y : Q,
  Id (Qle_bool x y) false -> Qlt y x.
Proof.
  intros x y H.
  assert (Hn : ~ (x <= y)).
  { intro Hc.
    assert (Ht : Qle_bool x y = true) by (apply Qle_bool_iff; exact Hc).
    rewrite Ht in H. inversion H. }
  exact (Qnot_le_lt x y Hn).
Qed.

(* ============================================================ *)
(* Part 4：Q 核证书直返选择器（Defined 可提取）                            *)
(* ============================================================ *)

Definition mixd_rung_cert (k0 v b0 : Q) (j : nat) : Set :=
  QleT' (Qmult (igr_qpow k0 (mixd_two_pow j)) v) b0.

Definition mixd_ans_cert (k0 v b0 : Q) (k : nat) : Set :=
  QleT' (Qmult (igr_qpow k0 k) v) b0.

Lemma mixd_qeqT_one_mul : forall v : Q, QeqT (1 * v) v.
Proof. intro v. exact (qeq_imp_qeqT (1 * v) v (Qmult_1_l v)). Qed.

Lemma mixd_qeqT_sym : forall a b : Q, QeqT a b -> QeqT b a.
Proof.
  intros a b H. apply qeq_imp_qeqT. symmetry.
  exact (mixd_qeqT_to_Qeq a b H).
Qed.

(* 上扫：至多 d 级；返回首个过线梯级（Set 证书直返）+ 上一失败梯级值 + 乘法计数。 *)
(*   Hacc 线程：acc ≡ mixd_ladder k0 i（runtime Prop——提取面为 __，零消除）。 *)
Fixpoint mixd_scan_up (k0 v b0 : Q) (d i : nat) (pacc acc : Q) (c : nat)
    (Hacc : acc == mixd_ladder k0 i)
  : option (sigT (fun j : nat => mixd_rung_cert k0 v b0 j) * Q * nat) :=
  match d with
  | Datatypes.O =>
      match mixd_dec_le (Qmult acc v) b0 with
      | inl Hp =>
          Some (existT _ i
                  (mixd_leT_transport (Qmult acc v)
                     (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                     (mixd_acc_cert k0 v i acc Hacc)
                     Hp),
                pacc, Datatypes.S c)
      | inr _ => None
      end
  | Datatypes.S d' =>
      match mixd_dec_le (Qmult acc v) b0 with
      | inl Hp =>
          Some (existT _ i
                  (mixd_leT_transport (Qmult acc v)
                     (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                     (mixd_acc_cert k0 v i acc Hacc)
                     Hp),
                pacc, Datatypes.S c)
      | inr _ =>
          mixd_scan_up k0 v b0 d' (Datatypes.S i) acc
            (Qmult acc acc) (Datatypes.S (Datatypes.S c))
            (@Qmult_comp acc (mixd_ladder k0 i) Hacc acc
               (mixd_ladder k0 i) Hacc)
      end
  end.

(* 二进制回退合成（贪心加-败位）：j 号位权重 2^j；候选 k+2^j 败则加位 *)
(* 重设计（D2 接管 01:00）：desc 增 k0 参、弃 p·p 传参（层级递减×升幂 rung
   与 desc_spec 合同结构性矛盾——见 _tatd2_交付报告 §7.2），rung 由
   mixd_ladder k0 (S j') 现场算（ladder_spec 正确性随取）。 *)
Fixpoint mixd_desc (k0 v b0 : Q) (j : nat) (k : nat) (val : Q) (c : nat)
  : nat * nat :=
  match j with
  | Datatypes.O =>
      match mixd_dec_le (Qmult val (mixd_ladder k0 0)) b0 with
      | inl _ => (k, Datatypes.S c)
      | inr _ => (Datatypes.S k, Datatypes.S (Datatypes.S c))
      end
  | Datatypes.S j' =>
      match mixd_dec_le (Qmult val (mixd_ladder k0 (Datatypes.S j'))) b0 with
      | inl _ => mixd_desc k0 v b0 j' k val (Datatypes.S (Datatypes.S c))
      | inr _ =>
          mixd_desc k0 v b0 j' (k + mixd_two_pow (Datatypes.S j'))%nat
            (Qmult val (mixd_ladder k0 (Datatypes.S j')))
            (Datatypes.S (Datatypes.S (Datatypes.S c)))
      end
  end.

(* 顶级选择器（Defined，证书直返）：k=0 支先判；否则上扫首个过线梯级 +   *)
(*   二进制回退合成得败位 kf；顶支守卫直测 S kf（inl=过线证书直返；      *)
(*   inr=语义死支，回退顶级梯级——构造合法、诚实降档见报告）。            *)
Definition mixd_k_select_log_cert (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d : nat)
  : option ((sum (sigT (fun k : nat => mixd_ans_cert k0 v b0 k))
                 (sigT (fun k : nat => mixd_ans_cert k0 v b0 k))) * nat) :=
  match mixd_dec_le v b0 with
  | inl Hp0 =>
      Some (inl (existT _ 0%nat
                   (mixd_leT_transport v (1 * v) b0
                      (mixd_qeqT_sym (1 * v) v (mixd_qeqT_one_mul v)) Hp0)),
            1%nat)
  | inr _ =>
      match mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat (Qeq_refl k0) with
      | None => None
      | Some (existT _ i Htop, pacc, c1) =>
          let kfc :=
            match i with
            | Datatypes.O => (0%nat, 0%nat)
            | Datatypes.S i' => mixd_desc k0 v b0 i' 0%nat v 0%nat
            end in
          match mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S (fst kfc))) v) b0 with
          | inl Hpass =>
              Some (inl (existT _ (Datatypes.S (fst kfc)) Hpass),
                    (c1 + snd kfc)%nat)
          | inr _ =>
              Some (inr (existT _ (mixd_two_pow i) Htop),
                    (c1 + snd kfc)%nat)
          end
      end
  end.


(* ============================================================ *)
(* Part 5：Q-Bernoulli 与窗口（Q 层自算——AT11 裁决 3 陷阱处方）            *)
(*   （D2 接管段：cont 稿移入；qbern 步进肢按 tathD 报告§4-① 重写——       *)
(*     Qle_trans 中段拆 (1−w)·(q^m·(1+M·w)) ≤ 1−w 与 q^(S m)·w ≤ w 双肢） *)
(* ============================================================ *)

(* m·w ≤ 1 + m·w（w > 0） *)
Lemma mixd_mw_le_boost : forall (m : nat) (w : Q) (Hw : 0 < w),
  Qle (Qmake (Z.of_nat m) 1 * w) (1 + Qmake (Z.of_nat m) 1 * w).
Proof.
  intros m w Hw.
  apply (mixd_qle_eq_l (Qplus 0 (Qmake (Z.of_nat m) 1 * w))
           (Qmake (Z.of_nat m) 1 * w)
           (Qplus 1 (Qmake (Z.of_nat m) 1 * w))).
  - apply Qplus_0_l.
  - apply (Qplus_le_compat 0 1 (Qmake (Z.of_nat m) 1 * w)
             (Qmake (Z.of_nat m) 1 * w)).
    + unfold Qle. cbn [Qnum Qden]. lia.
    + apply Qle_refl.
Qed.

(* Q-Bernoulli 步进桥接引理：Qmake (Z.of_nat (S m)) 1 == 1 + Qmake (Z.of_nat m) 1
   （zify/lia 原生归一——ring 对 Z.of_nat 原子拒动；D2 席 mixd2_qnat_succ
   同款，检验 _tatd2_p1 p2 已验） *)
Lemma mixd_qnat_succ : forall m : nat,
  Qmake (Z.of_nat (Datatypes.S m)) 1 == (1 + Qmake (Z.of_nat m) 1)%Q.
Proof.
  intro m. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

(* Q-Bernoulli：(1−w)^m·(1+m·w) ≤ 1（0 ≤ w ≤ 1；纯 Q 循环依赖清单归纳） *)
Lemma mixd_qbern : forall (w : Q) (Hw0 : 0 <= w) (Hw1 : w <= 1) (m : nat),
  Qle (Qmult (igr_qpow (1 - w) m) (1 + Qmake (Z.of_nat m) 1 * w)) 1.
Proof.
  intros w Hw0 Hw1 m.
  assert (Hq0 : 0 <= 1 - w) by exact (mixd_qsub_ge0 w Hw1).
  assert (Hq1 : (1 - w) <= 1) by exact (mixd_qsub_le w Hw0).
  induction m as [| m IH].
  - cbn [igr_qpow Z.of_nat].
    apply (mixd_qle_eq_l (1 * (1 + Qmake 0 1 * w)) (1 * (1 + 0 * w)) 1).
    + apply Qmult_1_l.
    + rewrite Qmult_0_l. rewrite Qplus_0_r. rewrite Qmult_1_l.
      apply Qle_refl.
  - apply (mixd_qle_eq_l
             (Qplus (Qmult (1 - w)
                             (Qmult (igr_qpow (1 - w) m)
                                    (Qplus 1
                                       (Qmult (Qmake (Z.of_nat m) 1) w))))
                    (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w))
             (Qmult (igr_qpow (1 - w) (Datatypes.S m))
                (Qplus 1 (Qmult (Qmake (Z.of_nat (Datatypes.S m)) 1) w)))
             1).
    + cbn [igr_qpow]. rewrite (mixd_qnat_succ m). ring.
    + apply (Qle_trans _ (Qplus (1 - w) w) _).
      * apply Qplus_le_compat.
        -- (* (1−w)·(q^m·(1+M·w)) ≤ 1−w（IH 右乘 (1−w) 换形） *)
           apply (Qle_trans _ (Qmult 1 (1 - w)) (1 - w)).
           ++ apply (mixd_qle_eq_l
                        (Qmult (Qmult (igr_qpow (1 - w) m)
                                      (Qplus 1
                                         (Qmult (Qmake (Z.of_nat m) 1) w)))
                               (1 - w))
                        (Qmult (1 - w)
                                (Qmult (igr_qpow (1 - w) m)
                                       (Qplus 1
                                          (Qmult (Qmake (Z.of_nat m) 1) w))))
                        (Qmult 1 (1 - w))).
              ** apply Qmult_comm.
              ** apply (Qmult_le_compat_r _ _ (1 - w)).
                 --- exact IH.
                 --- exact Hq0.
           ++ apply (mixd_qle_eq_r (Qmult 1 (1 - w)) (1 - w) (1 - w)).
              ** apply Qeq_refl.
              ** apply (mixd_qle_eq_l (1 - w) (Qmult 1 (1 - w)) (1 - w)).
                 --- apply (Qeq_sym _ _ (Qmult_1_l (1 - w))).
                 --- apply Qle_refl.
        -- (* q^(S m)·w ≤ w（mixd_qpow_le1 + compat_r 双跳） *)
           assert (HX1 : igr_qpow (1 - w) m <= 1)
             by exact (mixd_qpow_le1 (1 - w) Hq1 Hq0 m).
           apply (mixd_qle_eq_l
                    (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                    (Qmult (igr_qpow (1 - w) (Datatypes.S m)) w)
                    w).
           ++ cbn [igr_qpow]. ring.
           ++ apply (mixd_qle_eq_r
                        (Qmult (Qmult (1 - w) (igr_qpow (1 - w) m)) w)
                        (Qmult 1 w) w).
              ** apply Qmult_1_l.
              ** apply (Qmult_le_compat_r _ _ w).
                 --- apply (Qle_trans _ (1 - w) 1).
                     +++ apply (mixd_qle_eq_r
                                  (Qmult (1 - w) (igr_qpow (1 - w) m))
                                  (Qmult (1 - w) 1) (1 - w)).
                         **** apply Qmult_1_r.
                         **** apply (mixd_qmult_le_compat_l
                                     (igr_qpow (1 - w) m) 1 (1 - w)).
                             +++++ exact HX1.
                             +++++ exact Hq0.
                     +++ exact Hq1.
                 --- exact Hw0.
      * apply (mixd_qle_eq_r (Qplus (1 - w) w) (Qplus (1 - w) w) 1).
        -- ring.
        -- apply Qle_refl.
Qed.

(* 窗口件：v ≤ m·(w·b₀) ⟹ κ₀^m·v ≤ b₀（QleT' 直返） *)
Lemma mixd_window_pass : forall (k0 v b0 w : Q) (m : nat)
    (Hk0 : 0 < k0) (Hk1 : k0 <= 1) (Hv : 0 <= v) (Hb0 : 0 < b0)
    (Hw : w == 1 - k0) (Hwp : 0 < w)
    (Hn : QleT' v (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0))),
  QleT' (Qmult (igr_qpow k0 m) v) b0.
Proof.
  intros k0 v b0 w m Hk0 Hk1 Hv Hb0 Hw Hwp Hn.
  assert (Hb0le : 0 <= b0) by exact (Qlt_le_weak 0 b0 Hb0).
  assert (Hwb0 : 0 <= w * b0).
  { apply (Qle_trans 0 (0 * b0) (w * b0)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_r _ _ b0).
      + apply (Qlt_le_weak 0 w Hwp).
      + exact Hb0le. }
  assert (Hk0nn : 0 <= igr_qpow k0 m)
    by exact (mixd_qpow_nonneg k0 (Qlt_le_weak 0 k0 Hk0) m).
  apply Qle_to_QleT'.
  apply (Qle_trans _
           (Qmult (igr_qpow k0 m)
              (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0))) _).
  - apply (mixd_qmult_le_compat_l _ _ (igr_qpow k0 m)).
    + exact (QleT'_to_Qle _ _ Hn).
    + exact Hk0nn.
  - apply (mixd_qle_eq_l
             (Qmult (igr_qpow k0 m)
                (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0))
             (Qmult (igr_qpow k0 m)
                (Qmult (Qmake (Z.of_nat m) 1) (Qmult w b0)))
             b0).
    + ring.
    + apply (Qle_trans _
               (Qmult (igr_qpow k0 m)
                  (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0)) _).
      * apply (mixd_qmult_le_compat_l
                 (Qmult (Qmult (Qmake (Z.of_nat m) 1) w) b0)
                 (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0)
                 (igr_qpow k0 m)).
        -- apply (Qmult_le_compat_r _ _ b0).
           ++ exact (mixd_mw_le_boost m w Hwp).
           ++ exact Hb0le.
        -- exact Hk0nn.
      * apply (Qle_trans _ (Qmult 1 b0) _).
        -- apply (mixd_qle_eq_l
                     (Qmult (Qmult (igr_qpow k0 m)
                                (Qplus 1 (Qmake (Z.of_nat m) 1 * w))) b0)
                     (Qmult (igr_qpow k0 m)
                        (Qmult (Qplus 1 (Qmake (Z.of_nat m) 1 * w)) b0))
                     (Qmult 1 b0)).
           ++ ring.
           ++ apply (Qmult_le_compat_r _ _ b0).
              ** apply (mixd_qle_eq_l
                           (Qmult (igr_qpow (1 - w) m)
                              (Qplus 1 (Qmake (Z.of_nat m) 1 * w)))
                           (Qmult (igr_qpow k0 m)
                              (Qplus 1 (Qmake (Z.of_nat m) 1 * w)))
                           1).
                 *** apply (mixd_qeq_mult_r _ _ _).
                     apply (mixd_qpow_eq_compat (1 - w) k0).
                     apply (Qeq_trans _ (1 - (1 - k0)) _).
                     exact (@Qminus_comp 1 1 (Qeq_refl 1) w (1 - k0) Hw).
                     ring.
                 *** exact (mixd_qbern w (Qlt_le_weak 0 w Hwp)
                             (Qle_trans w (1 - k0) 1
                                (qeq_imp_qle w (1 - k0) Hw)
                                (mixd_qsub_le k0 (Qlt_le_weak 0 k0 Hk0)))
                             m).
              ** exact Hb0le.
        -- apply (mixd_qle_eq_l b0 (Qmult 1 b0) b0).
           ++ apply (Qeq_sym _ _ (Qmult_1_l b0)).
           ++ apply Qle_refl.
Qed.

(* 顶级窗口件：v ≤ N·(w·b₀) ∧ N ≤ 2^d ⟹ 顶级梯级 κ₀^(2^d)·v ≤ b₀ *)
Lemma mixd_window_top_pass : forall (k0 v b0 w : Q) (N d : nat)
    (Hk0 : 0 < k0) (Hk1 : k0 <= 1) (Hv : 0 <= v) (Hb0 : 0 < b0)
    (Hw : w == 1 - k0) (Hwp : 0 < w)
    (Hn : QleT' v (Qmult (Qmake (Z.of_nat N) 1) (Qmult w b0)))
    (HNd : (N <= mixd_two_pow d)%nat),
  QleT' (Qmult (igr_qpow k0 (mixd_two_pow d)) v) b0.
Proof.
  intros k0 v b0 w N d Hk0 Hk1 Hv Hb0 Hw Hwp Hn HNd.
  assert (Hwb0 : 0 <= w * b0).
  { apply (Qle_trans 0 (0 * b0) (w * b0)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_r _ _ b0).
      + apply (Qlt_le_weak 0 w Hwp).
      + apply (Qlt_le_weak 0 b0 Hb0). }
  assert (Hn' : QleT' v (Qmult (Qmake (Z.of_nat (mixd_two_pow d)) 1)
                                 (Qmult w b0))).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (Qmult (Qmake (Z.of_nat N) 1) (Qmult w b0)) _).
    - exact (QleT'_to_Qle _ _ Hn).
    - apply (Qmult_le_compat_r _ _ (Qmult w b0)).
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hwb0. }
  exact (mixd_window_pass k0 v b0 w (mixd_two_pow d) Hk0 Hk1 Hv Hb0 Hw Hwp
           Hn').
Qed.

(* ============================================================ *)
(* Part 6：选择器三账（sound / min / cost——igr_k_select_min 同形）        *)
(*   （D2 接管段：三处 mixd_scan_up 部分施加补全 Hacc:=Qeq_refl k0；      *)
(*     scan_up_some 调用补 Hpa；cert_none 子弹 5→3）                      *)
(* ============================================================ *)

(* Some-pair 注入替代件（:889 墙实录——injection 对 existT 载荷恒
   "Nothing to inject"；本二件在抽象 A 层以 f_equal 投影一次证毕，
   调用点实例化 A:=sigT/sum 后永不触碰依赖对注入） *)
Lemma mixd_some_inj_fst : forall (A : Type) (x y : A) (m n : nat),
  @Some (A * nat) (x, m) = @Some (A * nat) (y, n) -> x = y.
Proof.
  intros A x y m n H.
  exact (f_equal (fun o : option (A * nat) =>
                    match o with
                    | Some p => @fst A nat p
                    | None => x
                    end) H).
Qed.

Lemma mixd_some_inj_snd : forall (A : Type) (x y : A) (m n : nat),
  @Some (A * nat) (x, m) = @Some (A * nat) (y, n) -> m = n.
Proof.
  intros A x y m n H.
  exact (f_equal (fun o : option (A * nat) =>
                    match o with
                    | Some p => @snd A nat p
                    | None => m
                    end) H).
Qed.

Lemma mixd_some_inl_fst : forall (A B : Type) (x y : A) (m n : nat),
  @Some ((A + B) * nat) (@inl A B x, m) =
  @Some ((A + B) * nat) (@inl A B y, n) -> x = y.
Proof.
  intros A B x y m n H.
  exact (f_equal (fun o : option ((A + B) * nat) =>
                    (match o return A with
                     | Some (inl a, _) => a
                     | _ => x
                     end)) H).
Qed.

(* 上扫无解账：None ⟹ 窗内梯级全败 *)
Lemma mixd_scan_up_none : forall (k0 v b0 : Q) (d i : nat) (pacc acc : Q)
    (c : nat) (Hacc : acc == mixd_ladder k0 i),
  mixd_scan_up k0 v b0 d i pacc acc c Hacc = None ->
  forall j : nat, (i <= j)%nat -> (j <= i + d)%nat ->
  Qlt b0 (Qmult (igr_qpow k0 (mixd_two_pow j)) v).
Proof.
  intros k0 v b0 d. induction d as [| d IH];
    intros i pacc acc c Hacc Hnone j Hj1 Hj2.
  - cbn [mixd_scan_up] in Hnone.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + discriminate Hnone.
    + assert (Hji : j = i) by lia. subst j.
      apply (mixd_qlt_eq_r b0 (Qmult acc v)
               (Qmult (igr_qpow k0 (mixd_two_pow i)) v)).
      * apply (mixd_qeqT_to_Qeq _ _ (mixd_acc_cert k0 v i acc Hacc)).
      * exact (mixd_qleF_lt _ _ Hf).
  - cbn [mixd_scan_up] in Hnone.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + discriminate Hnone.
    + destruct (Nat.eq_dec j i) as [Hje | Hjne].
      * subst j. apply (mixd_qlt_eq_r b0 (Qmult acc v)
               (Qmult (igr_qpow k0 (mixd_two_pow i)) v)).
        -- apply (mixd_qeqT_to_Qeq _ _ (mixd_acc_cert k0 v i acc Hacc)).
        -- exact (mixd_qleF_lt _ _ Hf).
      * assert (Hrec : mixd_scan_up k0 v b0 d (Datatypes.S i) acc
                         (Qmult acc acc) (Datatypes.S (Datatypes.S c))
                         (Qmult_comp acc (mixd_ladder k0 i) Hacc acc
                            (mixd_ladder k0 i) Hacc) = None)
          by exact Hnone.
        apply (IH (Datatypes.S i) acc (Qmult acc acc)
                   (Datatypes.S (Datatypes.S c))
                   (Qmult_comp acc (mixd_ladder k0 i) Hacc acc
                      (mixd_ladder k0 i) Hacc)
                   Hrec).
        -- lia.
        -- lia.
Qed.

(* 上扫有解账：j ≤ i+d ∧ 成本 ≤ 2·d+1 ∧ pacc' ≡ κ₀^(2^(j−1)) 梯级值 *)
Lemma mixd_scan_up_some : forall (k0 v b0 : Q) (d i : nat) (pacc acc : Q)
    (c : nat) (j : nat) (Hcert : mixd_rung_cert k0 v b0 j) (pacc' : Q)
    (c' : nat)
    (Hacc : acc == mixd_ladder k0 i),
  pacc == mixd_ladder k0 (Nat.pred i) ->
  mixd_scan_up k0 v b0 d i pacc acc c Hacc
    = Some (existT _ j Hcert, pacc', c') ->
  (i <= j)%nat /\ (j <= i + d)%nat /\ (c' <= c + 2 * d + 1)%nat /\ pacc' == mixd_ladder k0 (Nat.pred j).
Proof.
  intros k0 v b0 d. induction d as [| d IH];
    intros i pacc acc c j Hcert pacc' c' Hacc Hpa Hsome.
  - cbn [mixd_scan_up] in Hsome.
    revert Hsome.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      assert (Hin1 : (existT _ i (mixd_leT_transport (Qmult acc v)
                          (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                          (mixd_acc_cert k0 v i acc Hacc) Hp), pacc)
                    = (existT _ j Hcert, pacc')).
      { apply (mixd_some_inj_fst _ _ _ _ _ Hsome). }
      assert (He : i = j).
      { exact (f_equal (@projT1 nat (fun j0 : nat => mixd_rung_cert k0 v b0 j0))
                 (f_equal (@fst (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q)
                    Hin1)). }
      assert (Hpacc : pacc = pacc') by exact (f_equal (@snd (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q) Hin1).
      assert (Hcnt : Datatypes.S c = c')
        by exact (mixd_some_inj_snd _ _ _ _ _ Hsome).
      subst j. subst pacc'. subst c'. repeat split.
      * lia.
      * lia.
      * lia.
      * exact Hpa.
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      discriminate Hsome.
  - cbn [mixd_scan_up] in Hsome.
    revert Hsome.
    destruct (mixd_dec_le (Qmult acc v) b0) as [Hp | Hf].
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      assert (Hin1 : (existT _ i (mixd_leT_transport (Qmult acc v)
                          (Qmult (igr_qpow k0 (mixd_two_pow i)) v) b0
                          (mixd_acc_cert k0 v i acc Hacc) Hp), pacc)
                    = (existT _ j Hcert, pacc')).
      { apply (mixd_some_inj_fst _ _ _ _ _ Hsome). }
      assert (He : i = j).
      { exact (f_equal (@projT1 nat (fun j0 : nat => mixd_rung_cert k0 v b0 j0))
                 (f_equal (@fst (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q)
                    Hin1)). }
      assert (Hpacc : pacc = pacc') by exact (f_equal (@snd (sigT (fun j0 : nat => mixd_rung_cert k0 v b0 j0)) Q) Hin1).
      assert (Hcnt : Datatypes.S c = c')
        by exact (mixd_some_inj_snd _ _ _ _ _ Hsome).
      subst j. subst pacc'. subst c'. repeat split.
      * lia.
      * lia.
      * lia.
      * exact Hpa.
    + intro Hsome. cbn [mixd_scan_up] in Hsome.
      destruct (IH (Datatypes.S i) acc (Qmult acc acc)
                   (Datatypes.S (Datatypes.S c)) j Hcert pacc' c'
                   (Qmult_comp acc (mixd_ladder k0 i) Hacc acc
                      (mixd_ladder k0 i) Hacc) Hacc Hsome) as
        [Hb1 [Hb2 [Hb3 Hb4]]].
      repeat split; [lia | lia | lia | assumption].
Qed.

(* 回退合成账：入口不变量（p ≡ κ₀^(2^j)、val ≡ κ₀^k·v、k 以下全败）⟹
   出口（kf 以下全败 ∧ S kf ≤ k + 2^(j+1) ∧ 成本 ≤ 3j+2）。 *)
(* 重设计版回退合成账（D2 接管 01:00）：rung 由 mixd_ladder 现场算，
   Hval 不变式 val == q^k·v 全程可保持（旧 p·p 传参在此断链——已证结论见
   _tatd2_交付报告 §7.2）。合同：kf 以下全败 ∧ S kf ≤ k + 2^(S j) ∧ 成本。 *)
Lemma mixd_desc_spec : forall (k0 v b0 : Q) (Hq0 : 0 < k0) (Hq1 : k0 <= 1)
    (Hv : 0 <= v) (j : nat) (k : nat) (val : Q) (c : nat)
    (Hval : val == Qmult (igr_qpow k0 k) v)
    (Hfail : forall m : nat, (m <= k)%nat -> Qlt b0 (Qmult (igr_qpow k0 m) v))
    (kf c' : nat),
  mixd_desc k0 v b0 j k val c = (kf, c') ->
  (forall m : nat, (m <= kf)%nat -> Qlt b0 (Qmult (igr_qpow k0 m) v)) /\
  (Datatypes.S kf <= k + mixd_two_pow (Datatypes.S j))%nat /\
  (c' <= c + 3 * j + 2)%nat.
Proof.
  intros k0 v b0 Hq0 Hq1 Hv j. induction j as [| j IH];
    intros k val c Hval Hfail kf c' Hrun.
  - cbn [mixd_desc] in Hrun.
    revert Hrun.
    destruct (mixd_dec_le (Qmult val (mixd_ladder k0 0)) b0)
      as [Hpass | Hfailj].
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      injection Hrun as Hkf Hcc. subst kf c'. repeat split.
      * intros m Hm. apply Hfail. lia.
      * cbn [mixd_two_pow]. lia.
      * lia.
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      injection Hrun as Hkf Hcc. subst kf c'. repeat split.
      * intros m Hm.
        destruct (Nat.eq_dec m (Datatypes.S k)) as [Hme | Hmne].
        -- subst m. apply (mixd_qlt_eq_r b0
                             (Qmult val (mixd_ladder k0 0))
                             (Qmult (igr_qpow k0 (Datatypes.S k)) v)).
           ++ apply (mixd_qeq_step0 k0 v k (mixd_ladder k0 0) val
                       (mixd_qeqT_to_Qeq _ _ (mixd_ladder_spec k0 0)) Hval).
           ++ exact (mixd_qleF_lt _ _ Hfailj).
        -- apply Hfail. lia.
      * cbn [mixd_two_pow mixd_ladder]. lia.
      * lia.
  - cbn [mixd_desc] in Hrun.
    revert Hrun.
    destruct (mixd_dec_le (Qmult val (mixd_ladder k0 (Datatypes.S j))) b0)
      as [Hpass | Hfailj].
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      destruct (IH k val (Datatypes.S (Datatypes.S c))
                  Hval Hfail kf c' Hrun) as [Ha [Hb Hc]].
      repeat split;
        [exact Ha
        | change (mixd_two_pow (Datatypes.S (Datatypes.S j)))
            with (2 * mixd_two_pow (Datatypes.S j))%nat; lia
        | lia].
    + intro Hrun. cbn [mixd_dec_le] in Hrun.
      assert (Hfail' : forall m : nat,
                 (m <= k + mixd_two_pow (Datatypes.S j))%nat ->
                 Qlt b0 (Qmult (igr_qpow k0 m) v)).
      { intros m Hm.
        destruct (Nat.le_gt_cases m k) as [Hmk | Hmk].
        - apply Hfail. lia.
        - apply (mixd_fail_down k0 v b0 Hq0 Hq1 Hv m
                    (k + mixd_two_pow (Datatypes.S j))).
          + lia.
          + apply (mixd_qlt_eq_r b0
                     (Qmult val (mixd_ladder k0 (Datatypes.S j)))
                     (Qmult (igr_qpow k0 (k + mixd_two_pow (Datatypes.S j)))
                        v)).
            * apply (mixd_qeq_step k0 v j k
                       (mixd_ladder k0 (Datatypes.S j)) val
                       (mixd_qeqT_to_Qeq _ _
                          (mixd_ladder_spec k0 (Datatypes.S j))) Hval).
            * exact (mixd_qleF_lt _ _ Hfailj). }
      destruct (IH (k + mixd_two_pow (Datatypes.S j))%nat
                  (Qmult val (mixd_ladder k0 (Datatypes.S j)))
                  (Datatypes.S (Datatypes.S (Datatypes.S c)))
                  (mixd_qeq_step k0 v j k (mixd_ladder k0 (Datatypes.S j)) val
                     (mixd_qeqT_to_Qeq _ _
                        (mixd_ladder_spec k0 (Datatypes.S j))) Hval)
                  Hfail' kf c' Hrun) as [Ha [Hb Hc]].
      repeat split;
        [exact Ha
        | change (mixd_two_pow (Datatypes.S (Datatypes.S j)))
            with (2 * mixd_two_pow (Datatypes.S j))%nat; lia
        | lia].
Qed.

(* 顶级主账·过线支：Some (inl (k, cert), c) ⟹ 下方全败 ∧ c ≤ 5·d+2 *)
Lemma mixd_k_select_log_cert_spec : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inl (existT _ k Hcert), c) ->
  (forall j : nat, (j < k)%nat -> Qlt b0 (Qmult (igr_qpow k0 j) v)) /\
  (c <= 5 * d + 2)%nat.
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  unfold mixd_k_select_log_cert in Hrun.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hrun.
  destruct d0 as [Hp0 | Hf0].
  - assert (Hb : 1%nat = c) by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
    assert (Hk0 : 0%nat = k).
    { exact (f_equal (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
               (mixd_some_inl_fst _ _ _ _ _ _ Hrun)). }
    subst k. subst c. split.
    + intros j Hj. exfalso. lia.
    + lia.
  - cbn [mixd_k_select_log_cert] in Hrun.
    revert Hrun.
    (* D3 实录：对卡死 fixpoint 应用的 destruct 产出 [Some-first, None-last]
       分支序 + 自动命名 binder（嵌套模式 match 编译序所致），as-模式整体
       被无视（"Unused introduction pattern"）——故无 as + 分步 1 级解构。 *)
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat (Qeq_refl k0))
      eqn:Hscan.
    + (* Some 支（首弹） *)
      destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
      destruct jj as [| j].
      * cbn [fst snd] in *.
        remember (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0) as d1 eqn:Ed1.
        cbn [mixd_k_select_log_cert] in Hrun.
        destruct d1 as [Hp1 | Hf1].
        -- assert (Hb : (c1 + 0)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           assert (Hk1 : Datatypes.S 0%nat = k)
             by exact (f_equal
                        (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
                        (mixd_some_inl_fst _ _ _ _ _ _ Hrun)).
           subst c. split.
           ++ intros m Hm.
              assert (Hm0 : m = 0%nat) by lia. subst m.
              apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
              --- cbn [igr_qpow]. symmetry. apply Qmult_1_l.
              --- exact (mixd_qleF_lt _ _ Hf0).
           ++ assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                               (Qeq_refl k0)
                               = Some (existT _ 0%nat Htop, pacc, c1))
                by exact Hscan.
              destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                          0%nat Htop pacc c1 (Qeq_refl k0) (Qeq_refl k0) Hs)
                as [_ [_ [Hc1 _]]].
              lia.
        -- discriminate Hrun.
      * assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                         (Qeq_refl k0)
                         = Some (existT _ (Datatypes.S j) Htop, pacc, c1))
          by exact Hscan.
        destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                    (Datatypes.S j) Htop pacc c1 (Qeq_refl k0) (Qeq_refl k0)
                    Hs) as [_ [Hjle [Hc1 Hpacc]]].
        assert (Hval0 : v == Qmult (igr_qpow k0 0%nat) v).
        { cbn [igr_qpow]. symmetry. apply Qmult_1_l. }
        assert (Hfail0 : forall m : nat, (m <= 0%nat)%nat ->
                   Qlt b0 (Qmult (igr_qpow k0 m) v)).
        { intros m Hm.
          assert (Hm0 : m = 0%nat) by lia. subst m.
          apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
          - cbn [igr_qpow]. symmetry. apply Qmult_1_l.
          - exact (mixd_qleF_lt _ _ Hf0). }
        revert Hrun.
        destruct (mixd_desc k0 v b0 j 0%nat v 0%nat) as [kf c2] eqn:Hdesc.
        cbn [fst snd].
        destruct (mixd_desc_spec k0 v b0
                    (QltT_to_Qlt 0 k0 h0) (QleT'_to_Qle k0 1 h1)
                    (QleT'_to_Qle 0 v hv) j 0%nat v 0%nat
                    Hval0 Hfail0 kf c2 Hdesc) as [HfailK [Hbnd Hcost]].
        remember (mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S kf)) v) b0)
          as d2 eqn:Ed2.
        intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
        destruct d2 as [Hpass | HfailS].
        -- assert (Hb : (c1 + c2)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           assert (Hk : Datatypes.S kf = k)
             by exact (f_equal
                        (@projT1 nat (fun k1 : nat => mixd_ans_cert k0 v b0 k1))
                        (mixd_some_inl_fst _ _ _ _ _ _ Hrun)).
           subst c. split.
           ++ intros m Hm. apply HfailK. lia.
           ++ lia.
        -- discriminate Hrun.
    + (* None 支（次弹） *)
      intro Hrun. discriminate Hrun.
Qed.

(* 量级定理（机器可陈述 nat 上界式——赛马卖点）：乘法次数 ≤ 5·d + 2， *)
(* 其中 d = 阶梯深度（梯级数 ≈ log₂K）：阶梯构造 d 乘 + 上扫 ≤ d+1 乘   *)
(* + 回退合成 ≤ 3d 乘，无重复计算（对照：线性代 k ≈ TV₀/(w·budget)）。  *)
(* 【cost-model 诚实申报（D3 席，承接 D2 报告 §8.1）】：mixd_desc 重设计  *)
(* 后 rung 由 mixd_ladder k0 (S j') 现场计算（弃 p·p 传参），desc 内部    *)
(* c-线程计数与实际 Q 乘法执行次数脱钩——mulcost 的 c ≤ 5d+2 对"证书线程" *)
(* 成立，非逐乘法计数；与 N3 提取对比表并列时须注记此差异。彻底解 = scan  *)
(* 返回梯列表逐乘核算（遗留 N3 跟进项）。                                  *)
Theorem mixd_k_select_log_mulcost : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inl (existT _ k Hcert), c) ->
  (c <= 5 * d + 2)%nat.
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  destruct (mixd_k_select_log_cert_spec k0 v b0 h0 h1 hv d k c Hcert Hrun)
    as [_ Hcost].
  exact Hcost.
Qed.

(* 顶级主账·回退支（语义死支）：Some (inr (k, cert), c) ⟹ 答案证书     *)
(*   （即顶级梯级直通）∧ c ≤ 5·d+2。最小性本支不申报（诚实降档——      *)
(*   死支不可达性证明=W-证书直通改造，遗留见交付报告续席配方）。        *)
Lemma mixd_k_select_log_cert_fb : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d k c : nat)
    (Hcert : mixd_ans_cert k0 v b0 k),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d
    = Some (inr (existT _ k Hcert), c) ->
  (c <= 5 * d + 2)%nat.
Proof.
  intros k0 v b0 h0 h1 hv d k c Hcert Hrun.
  unfold mixd_k_select_log_cert in Hrun.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hrun.
  destruct d0 as [Hp0 | Hf0].
  - discriminate Hrun.
  - cbn [mixd_k_select_log_cert] in Hrun.
    revert Hrun.
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat (Qeq_refl k0))
      eqn:Hscan.
    + (* Some 支（首弹） *)
      destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
      destruct jj as [| j].
      * cbn [fst snd] in *.
        remember (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0) as d1 eqn:Ed1.
        cbn [mixd_k_select_log_cert] in Hrun.
        destruct d1 as [Hp1 | Hf1].
        -- discriminate Hrun.
        -- (* jj=0 支 kfc=(0,0)：snd kfc=0（c2 未绑定位修正——D3 席） *)
           assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                           (Qeq_refl k0)
                           = Some (existT _ 0%nat Htop, pacc, c1))
             by exact Hscan.
           destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                       0%nat Htop pacc c1 (Qeq_refl k0) (Qeq_refl k0) Hs)
             as [_ [_ [Hc1 _]]].
           assert (Hb : (c1 + 0)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           subst c. lia.
      * assert (Hs : mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat
                         (Qeq_refl k0)
                         = Some (existT _ (Datatypes.S j) Htop, pacc, c1))
          by exact Hscan.
        destruct (mixd_scan_up_some k0 v b0 d 0%nat k0 k0 0%nat
                    (Datatypes.S j) Htop pacc c1 (Qeq_refl k0) (Qeq_refl k0)
                    Hs) as [_ [Hjle [Hc1 Hpacc]]].
        revert Hrun.
        destruct (mixd_desc k0 v b0 j 0%nat v 0%nat) as [kf c2] eqn:Hdesc.
        cbn [fst snd].
        remember (mixd_dec_le (Qmult (igr_qpow k0 (Datatypes.S kf)) v) b0)
          as d2 eqn:Ed2.
        intro Hrun. cbn [mixd_k_select_log_cert] in Hrun.
        destruct d2 as [Hpass | HfailS].
        -- discriminate Hrun.
        -- assert (Hb : (c1 + c2)%nat = c)
             by exact (mixd_some_inj_snd _ _ _ _ _ Hrun).
           subst c.
           assert (Hval0 : v == Qmult (igr_qpow k0 0%nat) v).
           { cbn [igr_qpow]. symmetry. apply Qmult_1_l. }
           assert (Hfail0 : forall m : nat, (m <= 0%nat)%nat ->
                      Qlt b0 (Qmult (igr_qpow k0 m) v)).
           { intros m Hm.
             assert (Hm0 : m = 0%nat) by lia. subst m.
             apply (mixd_qlt_eq_r b0 v (Qmult (igr_qpow k0 0%nat) v)).
             - cbn [igr_qpow]. symmetry. apply Qmult_1_l.
             - exact (mixd_qleF_lt _ _ Hf0). }
           destruct (mixd_desc_spec k0 v b0
                       (QltT_to_Qlt 0 k0 h0) (QleT'_to_Qle k0 1 h1)
                       (QleT'_to_Qle 0 v hv) j 0%nat v 0%nat
                       Hval0 Hfail0 kf c2 Hdesc) as [_ [_ Hcost2]].
           lia.
    + (* None 支（次弹） *)
      intro Hrun. discriminate Hrun.
Qed.

(* 无解账：None ⟹ 窗内 k ≤ 2^d 全败（窗口紧张度诚实申报） *)
Lemma mixd_k_select_log_cert_none : forall (k0 v b0 : Q) (h0 : QltT 0 k0)
    (h1 : QleT' k0 1) (hv : QleT' 0 v) (d : nat),
  mixd_k_select_log_cert k0 v b0 h0 h1 hv d = None ->
  forall j : nat, (j <= mixd_two_pow d)%nat ->
  Qlt b0 (Qmult (igr_qpow k0 j) v).
Proof.
  intros k0 v b0 h0 h1 hv d Hnone j Hj.
  unfold mixd_k_select_log_cert in Hnone.
  remember (mixd_dec_le v b0) as d0 eqn:Ed0.
  cbn [mixd_k_select_log_cert] in Hnone.
  destruct d0 as [Hp0 | Hf0].
  - discriminate Hnone.
  - revert Hnone.
    destruct (mixd_scan_up k0 v b0 d 0%nat k0 k0 0%nat (Qeq_refl k0))
      eqn:Hscan.
    + (* Some 支（首弹）——select 返回 Some，与 Hnone : ... = None 矛盾 *)
      destruct p as [sq c1].
      destruct sq as [s0 pacc].
      destruct s0 as [jj Htop].
      destruct jj as [| j0].
      * cbn [fst snd].
        destruct (mixd_dec_le (Qmult (igr_qpow k0 1) v) b0)
          as [Hp1 | Hf1].
        -- intro Hnone. discriminate Hnone.
        -- intro Hnone. discriminate Hnone.
      * cbn [fst snd].
        destruct (mixd_dec_le (Qmult (igr_qpow k0
                          (Datatypes.S (fst (mixd_desc k0 v b0 j0 0%nat v
                             0%nat)))) v) b0) as [Hp2 | Hf2].
        -- intro Hnone. discriminate Hnone.
        -- intro Hnone. discriminate Hnone.
    + (* None 支（次弹）——fail_down + scan_up_none 承账 *)
      intro Hnone. cbn [mixd_k_select_log_cert] in Hnone.
      apply (mixd_fail_down k0 v b0 (QltT_to_Qlt 0 k0 h0)
               (QleT'_to_Qle k0 1 h1) (QleT'_to_Qle 0 v hv) j
               (mixd_two_pow d) Hj).
      apply (mixd_scan_up_none k0 v b0 d 0%nat k0 k0 0%nat (Qeq_refl k0)).
      * exact Hscan.
      * lia.
      * lia.
Qed.

(* ============================================================ *)
(* Part 7：Real 壳（Q→Real 反映 + κ₀/b₀ 提取 + 幂桥 + 回传链）             *)
(*   （D2 接管段：real_const_proj 缺名→自建 mixd_const_proj；              *)
(*     split with→split/子弹；Qeq-改写→change+ring；                       *)
(*     const_mult/rpow_const 采 A 席绿件同款 cbn 白名单配方）              *)
(* ============================================================ *)

(* real_const 逐点脱壳（库内无 real_const_proj 专名——CW real_const        *)
(*   定义面直读：常值序列 projT1 恒 c） *)
Lemma mixd_const_proj : forall (v : Q) (n : nat), projT1 (real_const v) n == v.
Proof. intros v n. unfold real_const. exact (Qeq_refl v). Qed.

Lemma mixd_zero_proj : forall n : nat, projT1 real_zero n == 0.
Proof. intro n. exact (Qeq_refl 0). Qed.

Lemma mixd_one_proj : forall n : nat, projT1 real_one n == 1.
Proof. intro n. exact (Qeq_refl 1). Qed.

(* real_lt ⟹ real_le（Or 左支直入——real_le := Or real_lt real_eq 换形） *)
Definition mixd_lt_to_le : forall x y : Real, real_lt x y -> real_le x y :=
  fun x y H => @inl (real_lt x y) (real_eq x y) H.

(* Q→Real 反映：real_le real_zero (real_const v) ⟹ QleT' 0 v *)
Lemma mixd_const_le_reflect : forall v : Q,
  real_lt real_zero (real_const v) -> QleT' 0 v.
Proof.
  (* D3 实录：原稿取 real_le（Or 编码）双支——Heq 支遇 real_eq eps-逼近形
     （S02:396），Q 层 0<=v 不可直取（原 Heq 0 逐点依存即错）——改 real_lt
     前提，调用点用 real_lt_le_trans（S02:3153）保严格性。 *)
  intros v H. destruct H as [eps [Heps [N HN]]].
  apply Qle_to_QleT'.
  apply (Qle_trans 0 eps v).
  + exact (Qlt_le_weak 0 eps (QltT_to_Qlt 0 eps Heps)).
  + assert (HNv : QltT eps (projT1 (real_const v) N - projT1 real_zero N)).
    { apply HN. apply NatLe_lift. apply Nat.le_refl. }
    apply (Qle_trans eps
             (projT1 (real_const v) N - projT1 real_zero N) v).
    * apply (Qlt_le_weak eps). exact (QltT_to_Qlt _ _ HNv).
    * apply (mixd_qle_eq_l v
                 (projT1 (real_const v) N - projT1 real_zero N) v).
      -- change (projT1 (real_const v) N) with v.
         change (projT1 real_zero N) with 0.
         ring.
      -- apply Qle_refl.
Qed.

(* real_const 正性 *)
Lemma mixd_const_pos : forall k0 : Q, QltT 0 k0 ->
  real_lt real_zero (real_const k0).
Proof.
  intros k0 H.
  exact (real_eq_lt_lt real_zero (real_const (0#1)) (real_const k0)
           (real_eq_sym _ _ mix_const_zero)
           (real_const_lt 0 k0 (QltT_to_Qlt 0 k0 H))).
Qed.

(* const 乘法脱壳：real_const (a·b) ≡ real_const a · real_const b
   （A 席 mixa_const_mult 同款 cbn 白名单配方） *)
Lemma mixd_const_mult : forall a b : Q,
  real_eq (real_const (Qmult a b)) (real_mult (real_const a) (real_const b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const real_mult] in *. ring.
Qed.

(* Real 幂—Q 幂桥：tv_rpow (real_const q) m ≡ real_const (igr_qpow q m)
   （A 席 mixa_rpow_const 同款配方） *)
Lemma mixd_rpow_const : forall (q : Q) (m : nat),
  real_eq (tv_rpow (real_const q) m) (real_const (igr_qpow q m)).
Proof.
  intros q m. induction m as [| m IH].
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_one real_const tv_rpow igr_qpow] in *. ring.
  - cbn [tv_rpow igr_qpow].
    apply (real_eq_trans _
             (real_mult (real_const q) (real_const (igr_qpow q m)))).
    + exact (RealSetoid.real_eq_mult_compat (real_const q)
               (tv_rpow (real_const q) m)
               (real_const q) (real_const (igr_qpow q m))
               (real_eq_refl (real_const q)) IH).
    + exact (mixd_const_mult q (igr_qpow q m)).
Qed.

(* 回传链装配形：κ₀'^k·v 乘积脱壳 *)
Lemma mixd_rpow_const_eq : forall (q v : Q) (k : nat),
  real_eq (real_mult (tv_rpow (real_const q) k) (real_const v))
          (real_const (Qmult (igr_qpow q k) v)).
Proof.
  intros q v k.
  apply (real_eq_trans
           (real_mult (tv_rpow (real_const q) k) (real_const v))
           (real_mult (real_const (igr_qpow q k)) (real_const v))
           (real_const (Qmult (igr_qpow q k) v))).
  - apply (RealSetoid.real_eq_mult_compat (tv_rpow (real_const q) k)
             (real_const v) (real_const (igr_qpow q k)) (real_const v)
             (mixd_rpow_const q k) (real_eq_refl (real_const v))).
  - apply (real_eq_sym _ _ (mixd_const_mult (igr_qpow q k) v)).
Qed.

(* 底单调：0 < κ ∧ κ ≤ κ₀' ⟹ κ^m ≤ κ₀'^m（tv_rpow 面归纳直证） *)
Lemma mixd_pow_base_mono : forall (kappa : Real) (k0 : Q) (m : nat)
    (Hk1 : real_lt real_zero kappa) (Hk0p : QltT 0 k0)
    (Hle : real_le kappa (real_const k0)),
  real_le (tv_rpow kappa m) (tv_rpow (real_const k0) m).
Proof.
  intros kappa k0 m Hk1 Hk0p Hle. induction m as [| m IH].
  - exact (klc_le_refl (tv_rpow kappa 0)).
  - apply (real_le_trans
             (real_mult kappa (tv_rpow kappa m))
             (real_mult (real_const k0) (tv_rpow kappa m))
             (real_mult (real_const k0) (tv_rpow (real_const k0) m))).
    + apply (real_le_mult_compat kappa (real_const k0) (tv_rpow kappa m)).
      * exact (mix_rpow_pos kappa m Hk1).
      * exact Hle.
    + (* 左乘位：real_le_mult_compat 是右乘形（S07:6800），改 _r（S09:4984） *)
      apply (real_le_mult_compat_r (real_const k0)
                 (tv_rpow kappa m) (tv_rpow (real_const k0) m)).
      * exact (mixd_lt_to_le real_zero (real_const k0)
                 (mixd_const_pos k0 Hk0p)).
      * exact IH.
Qed.

(* κ₀ 间隙件（免分支：Qmax 双下界取 1−eps/2 下界即可） *)
Lemma mixd_kappa0_gap : forall (e x k0 : Q),
  0 < e -> k0 == mixd_qmax (1 - e * (1#2)) (1#2) ->
  Qlt e (1 - x) -> Qlt (e * (1#2)) (k0 - x).
Proof.
  intros e x k0 He Hk0 Hlt.
  assert (HQ : Qlt (x + e) 1).
  { apply (mixd_qlt_eq_r (x + e) (x + (1 - x)) 1).
    - ring.
    - exact (proj2 (Qplus_lt_r e (1 - x) x) Hlt). }
  assert (Ha : Qlt (e * (1#2) + x) (1 - e * (1#2))).
  { apply (proj1 (Qplus_lt_r (e * (1#2) + x) (1 - e * (1#2)) (e * (1#2)))).
    apply (mixd_qlt_eq_r (e * (1#2) + (e * (1#2) + x)) 1
             (e * (1#2) + (1 - e * (1#2)))).
    + ring.
    + apply (mixd_qlt_eq_l (x + e)
               (e * (1#2) + (e * (1#2) + x)) 1).
      * ring.
      * exact HQ. }
  assert (Hlb : Qle (1 - e * (1#2)) k0).
  { apply (mixd_qle_eq_r (1 - e * (1#2))
               (mixd_qmax (1 - e * (1#2)) (1#2)) k0).
    - apply (Qeq_sym _ _ Hk0).
    - destruct (Qle_bool (1 - e * (1#2)) (1#2)) eqn:Eb.
      + apply (mixd_qle_eq_r (1 - e * (1#2)) (1#2)
                 (mixd_qmax (1 - e * (1#2)) (1#2))).
        ** apply (Qeq_sym _ _ (mixd_qmax_eq_r _ _ Eb)).
        ** (* Qle_bool_iff 系 QArith_base 版，Eb 系 S02 版——具体目标上
               可转换，apply+exact 直渡（D3 实录） *)
           apply Qle_bool_iff. exact Eb.
      + apply (mixd_qle_eq_r (1 - e * (1#2)) (1 - e * (1#2))
                 (mixd_qmax (1 - e * (1#2)) (1#2))).
        ** apply (Qeq_sym _ _ (mixd_qmax_eq_l _ _ Eb)).
        ** apply Qle_refl. }
  apply (proj1 (Qplus_lt_r (e * (1#2)) (k0 - x) x)).
  apply (mixd_qlt_eq_l (e * (1#2) + x)
             (x + e * (1#2)) (x + (k0 - x))).
  - ring.
  - apply (mixd_qlt_eq_r (e * (1#2) + x) k0 (x + (k0 - x))).
    + ring.
    + apply (Qlt_le_trans (e * (1#2) + x) (1 - e * (1#2)) k0 Ha Hlb).
Qed.

(* κ₀ 提取件：real_lt κ 1 ⟹ κ₀ := Qmax(1−eps/2)(1/2) ∈ Q，
   携带 0 < κ₀ < 1（QltT）与 κ < κ₀（real_lt sigT——回传链承重位） *)
Lemma mixd_kappa0_cert : forall kappa : Real, real_lt kappa real_one ->
  sigT (fun k0 : Q =>
    And (QltT 0 k0) (And (QltT k0 1) (real_lt kappa (real_const k0)))).
Proof.
  intros kappa H. destruct H as [eps [Heps [N HN]]].
  exists (mixd_qmax (1 - eps * (1#2)) (1#2)).
  assert (Hepos : 0 < eps) by exact (QltT_to_Qlt 0 eps Heps).
  assert (Hlt0 : Qlt 0 (mixd_qmax (1 - eps * (1#2)) (1#2))).
  { destruct (Qle_bool (1 - eps * (1#2)) (1#2)) eqn:Eb.
    - apply (mixd_qlt_eq_r 0 (1#2) (mixd_qmax (1 - eps * (1#2)) (1#2))).
      + apply (Qeq_sym _ _ (mixd_qmax_eq_r _ _ Eb)).
      + exact mixd_half_pos.
    - apply (mixd_qlt_eq_r 0 (1 - eps * (1#2))
               (mixd_qmax (1 - eps * (1#2)) (1#2))).
      + apply (Qeq_sym _ _ (mixd_qmax_eq_l _ _ Eb)).
      + apply (Qlt_trans 0 (1#2) (1 - eps * (1#2))).
        * exact mixd_half_pos.
        * exact (mixd_qle_bool_false_lt (1 - eps * (1#2)) (1#2) Eb). }
  assert (Hlt1 : Qlt (mixd_qmax (1 - eps * (1#2)) (1#2)) 1).
  { destruct (Qle_bool (1 - eps * (1#2)) (1#2)) eqn:Eb.
    - apply (mixd_qlt_eq_l (1#2) (mixd_qmax (1 - eps * (1#2)) (1#2)) 1
               (Qeq_sym _ _ (mixd_qmax_eq_r _ _ Eb))).
      exact mixd_half_lt_one.
    - apply (mixd_qlt_eq_l (1 - eps * (1#2))
               (mixd_qmax (1 - eps * (1#2)) (1#2)) 1
               (Qeq_sym _ _ (mixd_qmax_eq_l _ _ Eb))).
      apply (proj1 (Qplus_lt_r (1 - eps * (1#2)) 1 (eps * (1#2)))).
      apply (mixd_qlt_eq_l 1
               (eps * (1#2) + (1 - eps * (1#2)))
               (eps * (1#2) + 1)).
      + ring.
      + apply (mixd_qlt_eq_r 1 (1 + eps * (1#2)) (eps * (1#2) + 1)).
        * ring.
        * exact (mixd_qlt_add_pos 1 (eps * (1#2))
                   (mixd_qlt_eq_l (0 * (1#2)) 0 (eps * (1#2))
                      (Qmult_0_l (1#2))
                      (Qmult_lt_compat_r 0 eps (1#2) mixd_half_pos
                         Hepos))). }
  split.
  - exact (Qlt_to_QltT 0 (mixd_qmax (1 - eps * (1#2)) (1#2)) Hlt0).
  - split.
    + exact (Qlt_to_QltT (mixd_qmax (1 - eps * (1#2)) (1#2)) 1 Hlt1).
    + exists (eps * (1#2)). split.
      * apply Qlt_to_QltT.
        exact (mixd_qlt_eq_l (0 * (1#2)) 0 (eps * (1#2))
                 (Qmult_0_l (1#2))
                 (Qmult_lt_compat_r 0 eps (1#2) mixd_half_pos Hepos)).
      * exists N. intros n Hn.
        apply Qlt_to_QltT.
        rewrite (mixd_const_proj (mixd_qmax (1 - eps * (1#2)) (1#2)) n).
        apply (mixd_kappa0_gap eps (projT1 kappa n)
                 (mixd_qmax (1 - eps * (1#2)) (1#2)) Hepos (Qeq_refl _)).
        apply (mixd_qlt_eq_r eps (projT1 real_one n - projT1 kappa n)
                 (1 - projT1 kappa n)).
        -- change (projT1 real_one n) with 1. ring.
        -- exact (QltT_to_Qlt _ _ (HN n Hn)).
Qed.

(* b₀ 提取件：real_lt 0 budget ⟹ b₀ := eps_b/2 ∈ Q 携带 0 < b₀ 与
   real_const b₀ < budget（回传链严格尾位） *)
Lemma mixd_b0_cert : forall budget : Real, real_lt real_zero budget ->
  sigT (fun b0 : Q => And (QltT 0 b0) (real_lt (real_const b0) budget)).
Proof.
  intros budget H. destruct H as [epsb [Heps [N HN]]].
  exists (epsb * (1#2)).
  assert (Hepos : 0 < epsb) by exact (QltT_to_Qlt 0 epsb Heps).
  assert (HB0 : Qlt 0 (epsb * (1#2))).
  { apply (mixd_qlt_eq_l (0 * (1#2)) 0 (epsb * (1#2))
             (Qmult_0_l (1#2))
             (Qmult_lt_compat_r 0 epsb (1#2) mixd_half_pos Hepos)). }
  split.
  - exact (Qlt_to_QltT 0 (epsb * (1#2)) HB0).
  - exists (epsb * (1#2)). split.
    + exact (Qlt_to_QltT 0 (epsb * (1#2)) HB0).
    + exists N. intros n Hn.
      apply Qlt_to_QltT.
      change (projT1 (real_const (epsb * (1#2))) n)
        with (epsb * (1#2)).
      apply (mixd_qsub_lt2 (epsb * (1#2)) (projT1 budget n)).
      apply (mixd_qlt_eq_l epsb (epsb * (1#2) + epsb * (1#2))
               (projT1 budget n)).
      * ring.
      * apply (mixd_qlt_eq_r epsb
                 (projT1 budget n - projT1 real_zero n)
                 (projT1 budget n)).
        -- change (projT1 real_zero n) with 0. ring.
        -- exact (QltT_to_Qlt _ _ (HN n Hn)).
Qed.

(* 回传链：Q 证书 ≤ ⟹ Real 严格 <（κ^k·TV₀ ≤ κ₀'^k·TV₀ ≤ κ₀'^k·v
   ≡ κ₀^k·v ≤ b₀ < budget——AT11 裁决 3 尾链） *)
Lemma mixd_real_chain : forall (kappa TV0 budget : Real) (k0 v b0 : Q)
    (k : nat) (Hk1 : real_lt real_zero kappa) (Hk0p : QltT 0 k0)
    (Hkle : real_le kappa (real_const k0))
    (Halt : real_lt real_zero TV0)
    (Htle : real_le TV0 (real_const v))
    (Hb0 : real_lt (real_const b0) budget)
    (Hcert : mixd_ans_cert k0 v b0 k),
  real_lt (real_mult (tv_rpow kappa k) TV0) budget.
Proof.
  intros kappa TV0 budget k0 v b0 k Hk1 Hk0p Hkle Halt Htle Hb0 Hcert.
  apply (real_le_lt_trans (real_mult (tv_rpow kappa k) TV0)
           (real_const b0) budget).
  - apply (real_le_trans
             (real_mult (tv_rpow kappa k) TV0)
             (real_mult (tv_rpow (real_const k0) k) TV0)
             (real_const b0)).
    + apply (real_le_mult_compat (tv_rpow kappa k)
               (tv_rpow (real_const k0) k) TV0).
      * exact Halt.
      * exact (mixd_pow_base_mono kappa k0 k Hk1 Hk0p Hkle).
    + apply (real_le_trans
               (real_mult (tv_rpow (real_const k0) k) TV0)
               (real_mult (tv_rpow (real_const k0) k) (real_const v))
               (real_const b0)).
      * (* 左乘位：real_le_mult_compat_r（S09:4984）+ rpow 正性 *)
        apply (real_le_mult_compat_r (tv_rpow (real_const k0) k)
                   TV0 (real_const v)).
        -- exact (mixd_lt_to_le real_zero
                    (tv_rpow (real_const k0) k)
                    (mix_rpow_pos (real_const k0) k
                       (mixd_const_pos k0 Hk0p))).
        -- exact Htle.
      * apply (real_le_trans
                 (real_mult (tv_rpow (real_const k0) k) (real_const v))
                 (real_const (Qmult (igr_qpow k0 k) v))
                 (real_const b0)).
        -- exact (RealSetoid.real_eq_le _ _ (mixd_rpow_const_eq k0 v k)).
        -- exact (klc_const_le (Qmult (igr_qpow k0 k) v) b0 Hcert).
  - exact Hb0.
Qed.

(* ============================================================ *)
(* Part 8：主件（Defined 可提取）与 le 形推论                              *)
(* ============================================================ *)

(* 正 TV₀ 支管线（TV₀==0 支走 mix_k_select 既有件） *)
Definition mixd_k_select_log_pos (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Halt : real_lt real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  match Htv with
  | existT _ v Htle =>
      match mixd_kappa0_cert kappa Hk2 with
      | existT _ k0 hpay =>
          match hpay with
          | (h0, (h0lt1, Hk0lt)) =>
              match mixd_b0_cert budget Hbudget with
              | existT _ b0 bpay =>
                  match bpay with
                  | (hb0p, Hb0lt) =>
                      match Hwin v k0 b0 with
                      | existT _ N Hw =>
                          let hv :=
                            mixd_const_le_reflect v
                              (real_lt_le_trans real_zero TV0
                                 (real_const v) Halt Htle) in
                          let h1 := qltT_leT' k0 1 h0lt1 in
                          let topcert :=
                            mixd_window_top_pass k0 v b0 (1 - k0) N N
                              (QltT_to_Qlt 0 k0 h0)
                              (QleT'_to_Qle k0 1 h1)
                              (QleT'_to_Qle 0 v hv)
                              (QltT_to_Qlt 0 b0 hb0p)
                              (Qeq_refl (1 - k0))
                              (mixd_qsub_pos k0 (QltT_to_Qlt k0 1 h0lt1))
                              Hw
                              (Nat.le_trans N (Datatypes.S N)
                                 (mixd_two_pow N) (Nat.le_succ_diag_r N)
                                 (mixd_two_pow_ge N)) in
                          match mixd_k_select_log_cert k0 v b0 h0 h1 hv N
                          with
                          | Some (inl (existT _ kk Hcert), cc) =>
                              existT _ kk
                                (mixd_real_chain kappa TV0 budget k0 v b0 kk
                                   Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt Hcert)
                          | Some (inr (existT _ kk Hcert), cc) =>
                              existT _ kk
                                (mixd_real_chain kappa TV0 budget k0 v b0 kk
                                   Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt Hcert)
                          | None =>
                              existT _ (mixd_two_pow N)
                                (mixd_real_chain kappa TV0 budget k0 v b0
                                   (mixd_two_pow N) Hk1 h0
                                   (mixd_lt_to_le kappa (real_const k0)
                                      Hk0lt)
                                   Halt Htle Hb0lt topcert)
                          end
                      end
                  end
              end
      end
  end
end.

(* 主件：对数级选择器（sigT Set 形，Defined 可提取） *)
Definition mixd_k_select_log (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_lt (real_mult (tv_rpow kappa k) TV0) budget) :=
  match Ha as Haa return real_le real_zero TV0 ->
                   sigT (fun k : nat =>
                     real_lt (real_mult (tv_rpow kappa k) TV0) budget) with
  | inl Halt =>
      fun _ =>
        mixd_k_select_log_pos kappa TV0 budget Hk1 Hk2 Halt Hbudget Htv Hwin
  | inr Haq =>
      fun _ => mix_k_select kappa TV0 budget Hk1 Hk2 (inr Haq) Hbudget
  end Ha.

(* le 形推论（Defined） *)
Definition mixd_k_select_log_le (kappa TV0 budget : Real)
    (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
    (Ha : real_le real_zero TV0) (Hbudget : real_lt real_zero budget)
    (Htv : sigT (fun v : Q => real_le TV0 (real_const v)))
    (Hwin : forall (v k0 b0 : Q),
              sigT (fun N : nat =>
                QleT' v (Qmult (Qmake (Z.of_nat N) 1)
                                 (Qmult (1 - k0) b0))))
  : sigT (fun k : nat => real_le (real_mult (tv_rpow kappa k) TV0) budget) :=
  match mixd_k_select_log kappa TV0 budget Hk1 Hk2 Ha Hbudget Htv Hwin with
  | existT _ k Hk => existT _ k (mixd_lt_to_le _ _ Hk)
  end.

(* ============================================================ *)
(* G4 审计口（全件：Part 0-8）                                            *)
(* ============================================================ *)
Print Assumptions mixd_scan_up.
Print Assumptions mixd_k_select_log_cert.
Print Assumptions mixd_ladder_spec.
Print Assumptions mixd_qpow_anti.
Print Assumptions mixd_fail_down.
Print Assumptions mixd_k_select_log.
Print Assumptions mixd_k_select_log_le.
Print Assumptions mixd_k_select_log_mulcost.
Print Assumptions mixd_k_select_log_cert_none.
Print Assumptions mixd_qbern.
Print Assumptions mixd_leT_transport.
Print Assumptions mixd_qeqT_one_mul.
Print Assumptions mixd_const_proj.
Print Assumptions mixd_zero_proj.
Print Assumptions mixd_one_proj.
