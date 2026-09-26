(* ============================================================ *)
(* ToyR 玩具证替换件 —— T254 台账席 战役包O（tier2 第五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   eoe_abs_bound（原 L325，3 句玩具证）                                 *)
(*   eoe_abs_Qle（原 L318，2 句玩具证）                                   *)
(*   qleT'_weaken（原 L63，5 句玩具证）                                   *)
(*   Qlt_to_QltT'（原 L60，2 句玩具证）                                   *)
(*   QltT'_to_Qlt（原 L57，3 句玩具证）                                   *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T321 恒等守恒更正注记】2026-09-22 包AW九 台账席（恒等头注更正全量第一批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321 台账。                        *)
(* 附记：T277 判级全文恒等；包O 全量第一批整批直推（T317 六·1 方案①）                           *)
(* ============================================================ *)

(* ============================================================ *)
(* ExpOneEnvelope.v —— 施工席位 C8（2026-09-16）                  *)
(* e 的显式有理双区间——A5 数值果 4 基础版（Q 层自足）。            *)
(*                                                              *)
(* 主对象：exp_partial n 1 = Σ_{k<n} 1/k!（S03 引擎，x := 1）。    *)
(* 三件（语句面全 Set 层，出口一律 QltT'/QleT'/NatLe/sigT）：      *)
(*  1. eoe_two_sided（主件，sigT 双端点形）：                     *)
(*     forall n, 1 ≤ n -> sigT lo, hi,                           *)
(*       QltT' 0 (hi − lo) ∧ （∀ m ≥ n，S_n ≤ S_m ≤ hi−lo 夹）    *)
(*     取 lo := S_n，hi := S_n + 2/n!，隙宽 == 2/n! > 0 显式；    *)
(*     配套 eoe_abs_bound（直接双 QleT' 形）：                    *)
(*     |S_m − S_n| ≤ 2/n!（1 ≤ n ≤ m）—— 任一后继部分和          *)
(*     落在显式有理区间 [S_n, S_n + 2/n!] 内（e_target 的 Q 层    *)
(*     自足替代：S07 的 cauchy_real_exp 接口过深，照任务书走       *)
(*     Q 自足版 + 单调支）。                                      *)
(*  2. eoe_cauchy_modulus（精度可计算支，B4 模量同款纪律）：       *)
(*     forall eps, QltT' 0 eps -> sigT N, ∀ m n ≥ N,              *)
(*     |S_m − S_n| < eps，N := eoe_modulus eps =                  *)
(*     S (Z.to_nat (Qceiling (2/eps)))——ceil(2/eps) 显式可抽取。  *)
(*  3. 支撑 ≥2：eoe_fact_mono（n! 单调）/ eoe_fact_ge_one·        *)
(*     eoe_fact_ge_self（n! ≥ max(1,n)）/ eoe_mono（部分和递增，  *)
(*     正项）/ eoe_term_pos（项正性）。                            *)
(*                                                              *)
(* 尾界引擎（grep 实测取可用者）：exp_partial_diff_bound@S03:678  *)
(*   （内部走 exp_tail_abs_geom2@S03:614 ≤ (A^m/m!)·2 +           *)
(*   exp_partial_diff_tail@S03:534 差恒等），A := Qabs 1。        *)
(* 模板对照（Live/build/LogTwoEnvelope.v，只参照不 Require）：     *)
(*   l2e_gap1/gap2 → eoe 差恒等（simpl+ring）；                   *)
(*   l2e_mag_antitone → eoe_fact_mono（n! 单调）；                *)
(*   l2e_tail_bound → eoe_tail_explicit（尾 ≤ 2/n! 显式公式）；    *)
(*   l2e_cauchy_modulus → eoe_cauchy_modulus（sigT + NatLe +      *)
(*     Qceiling 模量，leb 分案同构）；                            *)
(*   qleT'_weaken/QltT' 桥 → §0 原样复用。                        *)
(* 已知坑对防（C3 席实测）：stdlib 无 Qabs_eq（只用 Qabs_pos       *)
(*   分档）；Qeq 显式 Q 参数（Qeq_sym _ _）；apply 不做项序归一    *)
(*   （1*a vs a*1 走 qeq_le + ring == 链 / eoe_mult_le_l 桥）；    *)
(*   Qdiv 出现处先 unfold Qdiv 再 ring（防 ring 按原子误配）。     *)
(* 红线自审：公理面零假设（无公理/自认/参数声明/猜想/中止类语句，  *)
(*   零经典逻辑/排中律）；出口 QltT'/QleT'/NatLe/sigT；     *)
(*   尾界 2/n! 为显式公式，非恒真壳；文末 Print Assumptions 留痕。 *)
(* 领土纪律：本席仅新建 Live/build/ExpOneEnvelope.v；其余只读      *)
(*   （特别不 Require/不触碰 SumInvFactEscape.v）。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               ZArith.ZArith Arith.Arith Bool.Bool Lists.List.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ============================================================ *)
(* §0 Set 层出口件：QltT'（Qlt_bool 反映形，Id-of-bool，同 B4 §0） *)
(* ============================================================ *)

Definition QltT' (x y : Q) : Set := Id (Qlt_bool x y) true.

Lemma QltT'_to_Qlt : forall x y : Q, QltT' x y -> Qlt x y.
Proof. intros x y H. exact (QltT_to_Qlt x y H). Qed.

Lemma Qlt_to_QltT' : forall x y : Q, Qlt x y -> QltT' x y.
Proof. intros x y H. exact (Qlt_to_QltT x y H). Qed.

Lemma qleT'_weaken : forall a b c : Q, Qle a b -> b == c -> QleT' a c.
Proof.
  intros a b c H Hbc.
  exact (Qle_to_QleT' a c (Qle_trans a b c H (qeq_le b c Hbc))).
Qed.

(* ============================================================ *)
(* §1 序/等小桥：Qeq 运输、乘左单调、倒数反序、除法单调             *)
(* ============================================================ *)

(* ---- Qeq 左端运输：x == y -> y < z -> x < z ---- *)
Lemma eoe_lt_eq_l : forall x y z : Q, x == y -> Qlt y z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz. exact (Qle_lt_trans x y z (qeq_le x y Hxy) Hyz).
Qed.

(* ---- Qeq 右端运输：x < y -> y == z -> x < z ---- *)
Lemma eoe_lt_eq_r : forall x y z : Q, Qlt x y -> y == z -> Qlt x z.
Proof.
  intros x y z Hxy Hyz.
  exact (Qlt_le_trans x y z Hxy (qeq_le y z Hyz)).
Qed.

(* ---- 乘左单调（Qmult_le_compat_r 的项序桥：u*v ≤ u*w） ---- *)
Lemma eoe_mult_le_l : forall u v w : Q, Qle v w -> Qle 0 u -> Qle (u * v) (u * w).
Proof.
  intros u v w Hvw Hu.
  exact (Qle_trans (u * v) (v * u) (u * w)
           (qeq_le (u * v) (v * u) (Qmult_comm u v))
           (Qle_trans (v * u) (w * u) (u * w)
              (Qmult_le_compat_r v w u Hvw Hu)
              (qeq_le (w * u) (u * w) (Qmult_comm w u)))).
Qed.

(* ---- 倒数反序（Qle 形）：0 < x -> 0 < y -> y ≤ x -> /x ≤ /y ---- *)
Lemma eoe_qinv_le : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qle y x -> Qle (/ x) (/ y).
Proof.
  intros x y Hx Hy Hyx.
  destruct (Qle_lt_or_eq y x Hyx) as [Hlt | Heq].
  - exact (Qlt_le_weak (/ x) (/ y) (proj1 (Qinv_lt_contravar y x Hy Hx) Hlt)).
  - rewrite Heq. exact (Qle_refl (/ x)).
Qed.

(* ---- 除法单调（Qle 形）：同分子、正分母，大分母商更小 ---- *)
Lemma eoe_div_le : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qle z y -> Qle (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  exact (Qle_trans (a / y) (/ y * a) (a / z)
           (qeq_le (a / y) (/ y * a) (Qmult_comm a (/ y)))
           (Qle_trans (/ y * a) (/ z * a) (a / z)
              (Qmult_le_compat_r (/ y) (/ z) a (eoe_qinv_le y z Hy Hz Hzy)
                 (Qlt_le_weak 0 a Ha))
              (qeq_le (/ z * a) (a / z) (Qmult_comm (/ z) a)))).
Qed.

(* ---- 除法单调（Qlt 形）：严格版 ---- *)
Lemma eoe_div_lt : forall a y z : Q,
  Qlt 0 a -> Qlt 0 y -> Qlt 0 z -> Qlt z y -> Qlt (a / y) (a / z).
Proof.
  intros a y z Ha Hy Hz Hzy.
  exact (eoe_lt_eq_l (a / y) (/ y * a) (a / z)
           (Qmult_comm a (/ y))
           (eoe_lt_eq_r (/ y * a) (/ z * a) (a / z)
              (Qmult_lt_compat_r (/ y) (/ z) a Ha
                 (proj1 (Qinv_lt_contravar z y Hz Hy) Hzy))
              (Qmult_comm (/ z) a))).
Qed.

(* ============================================================ *)
(* §2 阶乘序结构（支撑件 1：n! 单调正，≥ max(1, n)）               *)
(* ============================================================ *)

Lemma eoe_fact_ge_one : forall k : nat, Qle (1%Q) (q_fact k).
Proof.
  induction k as [| k IH].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1))).
    + unfold Qle. simpl. lia.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * (1%Q))).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
        -- apply eoe_mult_le_l.
           ++ exact IH.
           ++ unfold Qle. simpl. lia.
        -- apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_ge_self : forall k : nat, Qle (Z.of_nat k # 1) (q_fact k).
Proof.
  intro k. destruct k as [| j].
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * (1%Q))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      * apply eoe_mult_le_l.
        -- apply eoe_fact_ge_one.
        -- unfold Qle. simpl. lia.
      * apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_step_ge : forall k : nat, Qle (q_fact k) (q_fact (Datatypes.S k)).
Proof.
  intro k.
  apply (Qle_trans _ ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)).
  - apply (Qle_trans _ (q_fact k * (Z.of_nat (Datatypes.S k) # 1))).
    + apply (Qle_trans _ (q_fact k * 1%Q)).
      * apply qeq_le. ring.
      * apply eoe_mult_le_l.
        -- unfold Qle. simpl. lia.
        -- apply (Qlt_le_weak 0 (q_fact k)). apply q_fact_pos.
    + apply qeq_le. ring.
  - apply qeq_le. reflexivity.
Qed.

Lemma eoe_fact_mono_add : forall d a : nat, Qle (q_fact a) (q_fact (a + d)).
Proof.
  intros d a. induction d as [| d IH].
  - replace (a + 0)%nat with a by lia. apply Qle_refl.
  - replace (a + Datatypes.S d)%nat with (Datatypes.S (a + d)) by lia.
    apply (Qle_trans _ (q_fact (a + d))).
    + exact IH.
    + exact (eoe_fact_step_ge (a + d)).
Qed.

Lemma eoe_fact_mono : forall a b : nat, (a <= b)%nat -> Qle (q_fact a) (q_fact b).
Proof.
  intros a b Hab.
  replace b with (a + (b - a))%nat by lia.
  exact (eoe_fact_mono_add (b - a) a).
Qed.

(* ============================================================ *)
(* §3 部分和序结构（支撑件 2：正项 ⟹ 递增；2/n! 恒正）             *)
(* ============================================================ *)

Lemma eoe_q_pow_one : forall n : nat, q_pow 1 n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow 1 (Datatypes.S n)) with (1 * q_pow 1 n).
    rewrite IH. apply Qmult_1_l.
Qed.

Lemma eoe_two_fact_pos : forall n : nat, Qlt 0 ((1 + 1)%Q / q_fact n).
Proof.
  intro n.
  apply (eoe_lt_eq_l _ (0 * / q_fact n)).
  - rewrite Qmult_0_l. reflexivity.
  - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ q_fact n)).
    + apply Qinv_lt_0_compat. apply q_fact_pos.
    + unfold Qlt. simpl. lia.
Qed.

Lemma eoe_term_pos : forall n : nat,
  Qlt 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
Proof.
  intro n. rewrite (eoe_q_pow_one (Datatypes.S n)).
  exact (eoe_lt_eq_r 0 (/ q_fact (Datatypes.S n)) (1 / q_fact (Datatypes.S n))
           (Qinv_lt_0_compat (q_fact (Datatypes.S n)) (q_fact_pos (Datatypes.S n)))
           (Qeq_sym (1 * / q_fact (Datatypes.S n)) (/ q_fact (Datatypes.S n))
              (Qmult_1_l (/ q_fact (Datatypes.S n))))).
Qed.

Lemma eoe_step_pos : forall n : nat,
  Qlt 0 (exp_partial (Datatypes.S n) 1 - exp_partial n 1).
Proof.
  intro n.
  assert (Hd : exp_partial (Datatypes.S n) 1 - exp_partial n 1 ==
               q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n)).
  { simpl. ring. }
  exact (eoe_lt_eq_r 0 (q_pow 1 (Datatypes.S n) / q_fact (Datatypes.S n))
           (exp_partial (Datatypes.S n) 1 - exp_partial n 1)
           (eoe_term_pos n) (Qeq_sym _ _ Hd)).
Qed.

Lemma eoe_mono_add : forall d m : nat, Qle (exp_partial m 1) (exp_partial (m + d) 1).
Proof.
  intros d m. induction d as [| d IH].
  - replace (m + 0)%nat with m by lia. apply Qle_refl.
  - replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d)) by lia.
    apply (Qle_trans _ (exp_partial (m + d) 1)).
    + exact IH.
    + apply (proj2 (Qle_minus_iff (exp_partial (m + d) 1)
                                  (exp_partial (Datatypes.S (m + d)) 1))).
      apply (Qlt_le_weak 0 (exp_partial (Datatypes.S (m + d)) 1 -
                            exp_partial (m + d) 1)).
      apply eoe_step_pos.
Qed.

Lemma eoe_mono : forall m n : nat, (m <= n)%nat -> Qle (exp_partial m 1) (exp_partial n 1).
Proof.
  intros m n Hmn.
  replace n with (m + (n - m))%nat by lia.
  exact (eoe_mono_add (n - m) m).
Qed.

(* ============================================================ *)
(* §4 尾界显式公式：m ≤ n ⟹ |S_n − S_m| ≤ 2/m!                    *)
(*   （引擎 exp_partial_diff_bound@S03:678，A := Qabs 1）          *)
(* ============================================================ *)

Lemma eoe_one_abs : Qabs 1 == 1.
Proof. apply Qabs_pos. unfold Qle. simpl. lia. Qed.

Lemma eoe_q_pow_one_abs : forall n : nat, q_pow (Qabs 1) n == 1.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - change (q_pow (Qabs 1) (Datatypes.S n)) with (Qabs 1 * q_pow (Qabs 1) n).
    rewrite eoe_one_abs. rewrite IH. reflexivity.
Qed.

Lemma eoe_diff_bound : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1))
      ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q).
Proof.
  intros m n H1m Hmn.
  apply (exp_partial_diff_bound 1 (Qabs 1) m n).
  - reflexivity.
  - rewrite eoe_one_abs. unfold Qle. simpl. lia.
  - intros t Hmt. unfold Qle. simpl. lia.
  - exact Hmn.
Qed.

Lemma eoe_tail_explicit : forall m n : nat, (1 <= m)%nat -> (m <= n)%nat ->
  Qle (Qabs (exp_partial n 1 - exp_partial m 1)) ((1 + 1)%Q / q_fact m).
Proof.
  intros m n H1m Hmn.
  apply (Qle_trans _ ((q_pow (Qabs 1) m / q_fact m) * (1 + 1)%Q)).
  - apply (exp_partial_diff_bound 1 (Qabs 1) m n).
    + reflexivity.
    + rewrite eoe_one_abs. unfold Qle. simpl. lia.
    + intros t Hmt. unfold Qle. simpl. lia.
    + exact Hmn.
  - apply qeq_le.
    rewrite (eoe_q_pow_one_abs m). unfold Qdiv. ring.
Qed.

(* ---- 对称化（出口主用形）：1 ≤ n ≤ m ⟹ |S_m − S_n| ≤ 2/n! ---- *)
Lemma eoe_abs_Qle : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  Qle (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (eoe_tail_explicit n m H1n Hnm).
Qed.

Theorem eoe_abs_bound : forall m n : nat, (1 <= n)%nat -> (n <= m)%nat ->
  QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) ((1 + 1)%Q / q_fact n).
Proof.
  intros m n H1n Hnm.
  exact (Qle_to_QleT' _ _ (eoe_abs_Qle m n H1n Hnm)).
Qed.

(* ============================================================ *)
(* §5 主件：e 的显式有理双区间（sigT 双端点 + 正隙宽 + 全后继夹逼） *)
(*   lo := S_n，hi := S_n + 2/n!，hi − lo == 2/n! > 0，           *)
(*   ∀ m ≥ n：lo ≤ S_m ≤ hi（即 S_n ≤ e 的任一后继近似 ≤ hi）。    *)
(* ============================================================ *)

Theorem eoe_two_sided : forall n : nat, (1 <= n)%nat ->
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      prod (QltT' 0 (hi - lo))
           (forall m : nat, NatLe n m ->
              prod (QleT' lo (exp_partial m 1))
                   (QleT' (Qabs (exp_partial m 1 - exp_partial n 1)) (hi - lo))))).
Proof.
  intros n H1n.
  exists (exp_partial n 1).
  exists (exp_partial n 1 + (1 + 1)%Q / q_fact n).
  split.
  - (* 隙宽显式：hi − lo == 2/n! > 0 *)
    apply Qlt_to_QltT'.
    assert (Hgap : (exp_partial n 1 + (1 + 1)%Q / q_fact n) - exp_partial n 1 ==
                   (1 + 1)%Q / q_fact n) by ring.
    rewrite Hgap. apply eoe_two_fact_pos.
  - intros m Hnm.
    assert (Hnm' : (n <= m)%nat) by (apply NatLe_drop in Hnm; exact Hnm).
    split.
    + (* 下翼：S_n ≤ S_m（正项递增） *)
      apply Qle_to_QleT'.
      apply eoe_mono. exact Hnm'.
    + (* 上翼：|S_m − S_n| ≤ hi − lo == 2/n!（隙宽显式） *)
      apply (qleT'_weaken _ ((1 + 1)%Q / q_fact n) _).
      * apply eoe_abs_Qle; assumption.
      * ring.
Qed.

(* ============================================================ *)
(* §6 精度可计算支：N := S(ceil(2/eps)) 显式模量（B4 同款纪律）     *)
(* ============================================================ *)

Definition eoe_modulus (eps : Q) : nat :=
  Datatypes.S (Z.to_nat (Qceiling ((1 + 1)%Q / eps))).

Lemma eoe_modulus_bound : forall eps : Q, Qlt 0 eps ->
  Qlt ((1 + 1)%Q / q_fact (eoe_modulus eps)) eps.
Proof.
  intros eps Hlt.
  unfold eoe_modulus.
  assert (Hinv0 : Qlt 0 (/ eps)) by (apply Qinv_lt_0_compat; exact Hlt).
  assert (H2e : Qlt 0 ((1 + 1)%Q / eps)).
  { apply (eoe_lt_eq_l _ (0 * / eps)).
    - rewrite Qmult_0_l. reflexivity.
    - apply (Qmult_lt_compat_r 0 (1 + 1)%Q (/ eps)).
      + exact Hinv0.
      + unfold Qlt. simpl. lia. }
  remember (Qceiling ((1 + 1)%Q / eps)) as c eqn:Hcdef.
  assert (Hle : Qle ((1 + 1)%Q / eps) (c # 1)) by (rewrite Hcdef; apply Qle_ceiling).
  assert (Hc1 : (1 <= c)%Z).
  { assert (Hlt1 : Qlt 0 (c # 1))
      by (apply (Qlt_le_trans 0 ((1 + 1)%Q / eps) (c # 1)); assumption).
    unfold Qlt in Hlt1. simpl in Hlt1. lia. }
  assert (Hk : Z.of_nat (Z.to_nat c) = c) by lia.
  assert (Hceil : Qle ((1 + 1)%Q / eps) ((Z.of_nat (Z.to_nat c)) # 1))
    by (rewrite Hk; exact Hle).
  (* 2/eps ≤ k#1 ≤ k! ⟹ 2 ≤ k!·eps *)
  assert (H2fact : Qle ((1 + 1)%Q / eps) (q_fact (Z.to_nat c))).
  { apply (Qle_trans _ ((Z.of_nat (Z.to_nat c)) # 1)).
    - exact Hceil.
    - apply eoe_fact_ge_self. }
  assert (Hmul : Qle ((1 + 1)%Q / eps * eps) (q_fact (Z.to_nat c) * eps)).
  { apply Qmult_le_compat_r.
    - exact H2fact.
    - apply (Qlt_le_weak 0 eps). exact Hlt. }
  assert (Hid : (1 + 1)%Q / eps * eps == (1 + 1)%Q).
  { field. intro Hzz. apply (Qlt_not_eq 0 eps Hlt). exact (Qeq_sym _ _ Hzz). }
  assert (H2 : Qle (1 + 1)%Q (q_fact (Z.to_nat c) * eps)).
  { apply (Qle_trans _ ((1 + 1)%Q / eps * eps)).
    - apply qeq_le. symmetry. exact Hid.
    - exact Hmul. }
  (* N = S k 的阶乘 = (k+1)·k! ≥ 2·k!，严格衰减压过 eps *)
  assert (HN2 : Qle (1 + 1)%Q ((Z.of_nat (Datatypes.S (Z.to_nat c))) # 1)).
  { unfold Qle. simpl. lia. }
  assert (Hden : Qle ((1 + 1)%Q * q_fact (Z.to_nat c))
                     (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Z.to_nat c)) # 1) * q_fact (Z.to_nat c))).
    - apply Qmult_le_compat_r.
      + exact HN2.
      + apply (Qlt_le_weak 0 (q_fact (Z.to_nat c))). apply q_fact_pos.
    - apply qeq_le. reflexivity. }
  assert (Hstrict : Qlt (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
  { apply (eoe_lt_eq_l _ (1 * q_fact (Z.to_nat c))).
    - symmetry. apply Qmult_1_l.
    - apply (Qmult_lt_compat_r 1 (1 + 1)%Q (q_fact (Z.to_nat c))).
      + apply q_fact_pos.
      + unfold Qlt. simpl. lia. }
  assert (HqN : Qlt (q_fact (Z.to_nat c)) (q_fact (Datatypes.S (Z.to_nat c)))).
  { apply (Qlt_le_trans (q_fact (Z.to_nat c)) ((1 + 1)%Q * q_fact (Z.to_nat c))).
    - exact Hstrict.
    - exact Hden. }
  assert (Hdrop : Qlt ((1 + 1)%Q / q_fact (Datatypes.S (Z.to_nat c)))
                      ((1 + 1)%Q / q_fact (Z.to_nat c))).
  { apply (eoe_div_lt (1 + 1)%Q (q_fact (Datatypes.S (Z.to_nat c))) (q_fact (Z.to_nat c))).
    - unfold Qlt. simpl. lia.
    - apply q_fact_pos.
    - apply q_fact_pos.
    - exact HqN. }
  assert (H2inv : Qle ((1 + 1)%Q * / q_fact (Z.to_nat c))
                      ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
  { apply Qmult_le_compat_r.
    - exact H2.
    - apply (Qlt_le_weak 0 (/ q_fact (Z.to_nat c))).
      apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hid2 : (q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c) == eps).
  { field. intro Hzz. apply (q_neq_of_lt (q_fact (Z.to_nat c)) (q_fact_pos (Z.to_nat c))).
    exact Hzz. }
  assert (Hfinal : Qle ((1 + 1)%Q / q_fact (Z.to_nat c)) eps).
  { apply (Qle_trans _ ((1 + 1)%Q * / q_fact (Z.to_nat c))).
    - apply qeq_le. reflexivity.
    - apply (Qle_trans _ ((q_fact (Z.to_nat c) * eps) * / q_fact (Z.to_nat c))).
      + exact H2inv.
      + apply qeq_le. exact Hid2. }
  apply (Qlt_le_trans _ ((1 + 1)%Q / q_fact (Z.to_nat c))).
  - exact Hdrop.
  - exact Hfinal.
Qed.

(* ---- 出口二：sigT 柯西模量（N 显式 = ceil(2/eps)+1，可抽取） ---- *)
Theorem eoe_cauchy_modulus : forall eps : Q, QltT' 0 eps ->
  sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
    QltT' (Qabs (exp_partial m 1 - exp_partial n 1)) eps).
Proof.
  intros eps Heps.
  assert (Hlt : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  exists (eoe_modulus eps).
  intros m n HNm HNn.
  apply NatLe_drop in HNm.
  apply NatLe_drop in HNn.
  apply Qlt_to_QltT'.
  assert (HN1 : (1 <= eoe_modulus eps)%nat) by (unfold eoe_modulus; lia).
  assert (H1m : (1 <= m)%nat) by lia.
  assert (H1n : (1 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:E.
  - (* m ≤ n：|S_n − S_m| ≤ 2/m! ≤ 2/N! < eps *)
    apply Nat.leb_le in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact m)).
      * rewrite Qabs_Qminus. apply (eoe_tail_explicit m n); assumption.
      * apply (eoe_div_le (1 + 1)%Q (q_fact m) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNm.
    + apply eoe_modulus_bound. exact Hlt.
  - (* n < m：|S_m − S_n| ≤ 2/n! ≤ 2/N! < eps *)
    apply Nat.leb_gt in E.
    apply (Qle_lt_trans _ ((1 + 1)%Q / q_fact (eoe_modulus eps))).
    + apply (Qle_trans _ ((1 + 1)%Q / q_fact n)).
      * apply (eoe_tail_explicit n m); lia.
      * apply (eoe_div_le (1 + 1)%Q (q_fact n) (q_fact (eoe_modulus eps))).
        -- unfold Qlt. simpl. lia.
        -- apply q_fact_pos.
        -- apply q_fact_pos.
        -- apply eoe_fact_mono. exact HNn.
    + apply eoe_modulus_bound. exact Hlt.
Qed.

(* ============================================================ *)
(* §7 假设留痕（红线④：Print Assumptions ≥ 1）                    *)
(* ============================================================ *)

Print Assumptions eoe_two_sided.
Print Assumptions eoe_abs_bound.
Print Assumptions eoe_cauchy_modulus.
Print Assumptions eoe_mono.
