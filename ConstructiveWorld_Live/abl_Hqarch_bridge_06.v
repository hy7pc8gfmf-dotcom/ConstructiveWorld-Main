(* ==========================================================================
   abl_Hqarch_bridge_06.v — R2BishopLogSel Hqarch 构造性闭合切片 2/2（桥接件）：
   Q 层 Archimedean nat 见证生产 + Hqarch 全站闭合（独立消融件）
   使命: 接续 X4 落件 abl_Hqarch_bernoulli_04.v（切片 1/2）的接续点——以 Q 层
     Archimedean 性质生产末前件 Qle v (b * (1 + n·(/p−1))) 的 nat 见证 n，
     再由 X4 件内已证的 abl_hqarch_via_bern 一步闭合 Hqarch 全站。
   交付三件：
     ① abl_arch / abl_q_arch_sig——Q 层 Archimedean nat 见证核：任 q:Q 取
        n := Z.to_nat (Qnum q)，则 q ≤ abl_qofnat n（Q 层序 nat 尺度）。构造：
        QDen 正性（Q 记录 Qden:positive，Pos2Z.is_pos）+ Z2Nat.id /
        Nat2Z.is_nonneg 双支二分（Z_lt_le_dec，sumbool 纯构造）+
        Zmult_le_compat_r 归一（num≥0 支 num ≤ num·den；num<0 支 0 ≤ witness 封顶）。
     ② abl_bridge_step / abl_hqarch_witness_site——末前件 n 见证生产：
        t := (v−b)·/(b·w)（w := /p−1，正性由 X4 件 abl_canon_w_pos 供给），
        Arch 取 n := Z.to_nat (Qnum t)，由 t ≤ n 右乘 b·w>0 得 v−b ≤ n·(b·w)，
        加 b 归一得 v ≤ b·(1+n·w)。见证为 v,b,p 的闭式计算项（abl_hqarch_nat）。
     ③ abl_hqarch_site_closed——Hqarch 全站闭合定理（本片核心交付）。
   站点形状逐项对应（对照 R2BishopLogSel.v L316-321）：源件 L319-320 前件位
     forall (p v b : Q), Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
       sigT (fun j : nat => Qle (mixe_qpow p j * v) b)；
     本件（幂件 abl_qpow，同体更名，对应说明承 X4 件头注接口对应条目）：
     四前提逐项同形（Qlt 0 p / Qlt p 1 / Qlt 0 v / Qlt 0 b），见证形式同为
     sigT (fun j : nat => ...)（Set/Type 层），谓词体同构（幂件更名）。
   接口引用（零重做）：X4 件 abl_Hqarch_bernoulli_04 之 abl_hqarch_via_bern
     （四前提+末前件 → sigT 闭合，X4 件内 Qed 闭合）、abl_canon_w_pos
     （w:=/p−1 正性）、abl_qpow（幂件）、abl_qlt_neq0 / abl_qle_eq_l /
     abl_qle_eq_r（传输小件）。
   依赖: 纯 Stdlib（QArith、ZArith、ZArith_dec、Lia、Extraction）+ X4 落件
     （同池真拷编译）；本件零新公理、零承认词面。
   构造性: 全件 Qed 闭合；见证以 sigT（Set/Type 层）承载——
     n := Z.to_nat (Qnum ((v−b)·/(b·(/p−1)))) 闭式可计算，提取审计
     abl_hqarch_bridge_06_G3.ml 实测 Obj.magic=0；序谓词沿站点口径用
     stdlib Qle/Qlt（Hqarch 前件同款，承 X4 件先例）。
   编译配方: 隔离池 /tmp/x6pool 真拷 X4 件+本件，cwd=池，cpu_guard 包裹
     rocq c -Q /tmp/x6pool "" （先编 X4 件出 .vo，再编本件）。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZArith.ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.

Require Import abl_Hqarch_bernoulli_04.

Open Scope Q_scope.

(* ============================================================ *)
(* Part A：Q 层 Archimedean nat 见证核                                *)
(*   n := Z.to_nat (Qnum q) 满足 q ≤ n（nat 尺度）。                  *)
(*   证法：Qle 展开为 Z 不等式后按 Qnum q 符号二分——                 *)
(*     num ≥ 0 支：Z2Nat.id 归 witness 为 num，1 ≤ den 右乘保序；     *)
(*     num < 0 支：Nat2Z.is_nonneg 给 witness ≥ 0，负 num 封顶。      *)
(* ============================================================ *)

Definition abl_arch_nat (q : Q) : nat := Z.to_nat (Qnum q).

Lemma abl_arch : forall q : Q, Qle q (abl_qofnat (abl_arch_nat q)).
Proof.
  intro q.
  destruct q as [m e].
  assert (He : (0 < Z.pos e)%Z) by exact (Pos2Z.is_pos e).
  assert (H1e : (1 <= Z.pos e)%Z) by lia.
  unfold Qle, abl_qofnat, abl_arch_nat. cbn [Qnum Qden].
  destruct (Z_lt_le_dec m 0) as [Hm | Hm].
  - (* num < 0：witness ≥ 0 封顶 *)
    assert (H0 : (0 <= Z.of_nat (Z.to_nat m))%Z)
      by exact (Nat2Z.is_nonneg (Z.to_nat m)).
    assert (Hx : (1 * Z.of_nat (Z.to_nat m) <= Z.pos e * Z.of_nat (Z.to_nat m))%Z)
      by (apply Zmult_le_compat_r; assumption).
    rewrite Zmult_1_l in Hx.
    rewrite (Zmult_comm (Z.pos e) (Z.of_nat (Z.to_nat m))) in Hx.
    rewrite Zmult_1_r. lia.
  - (* num ≥ 0：witness 归 num，den ≥ 1 右乘保序 *)
    rewrite (Z2Nat.id m Hm). rewrite Zmult_1_r.
    assert (Hx : (1 * m <= Z.pos e * m)%Z)
      by (apply Zmult_le_compat_r; assumption).
    rewrite Zmult_1_l in Hx.
    rewrite (Zmult_comm (Z.pos e) m) in Hx.
    exact Hx.
Qed.

(* sigT 形 Archimedean（见证 Type 层承载，供提取审计与记录） *)
Lemma abl_q_arch_sig : forall q : Q, sigT (fun n : nat => Qle q (abl_qofnat n)).
Proof.
  intro q. exists (abl_arch_nat q). apply abl_arch.
Qed.

(* ============================================================ *)
(* Part B：末前件 n 见证生产                                          *)
(*   t := (v−b)·/(b·w)：t ≤ n（Arch）→ 右乘 b·w>0 → v−b ≤ n·(b·w)     *)
(*   → 加 b 归一 → v ≤ b·(1+n·w)。v ≤ b 时 t ≤ 0、n=0 自动覆盖。       *)
(* ============================================================ *)

Definition abl_bridge_ratio (v b w : Q) : Q := (v - b) * / (b * w).

Definition abl_hqarch_nat (p v b : Q) : nat :=
  abl_arch_nat (abl_bridge_ratio v b (/ p - 1)).

Lemma abl_bridge_step : forall (v b w : Q) (n : nat),
  Qlt 0 b -> Qlt 0 w ->
  Qle (abl_bridge_ratio v b w) (abl_qofnat n) ->
  Qle v (b * (1 + abl_qofnat n * w)).
Proof.
  intros v b w n Hb0 Hw0 Hratio.
  assert (Hr0 : Qlt 0 (b * w)) by exact (Qmult_lt_0_compat b w Hb0 Hw0).
  assert (Hrle : Qle 0 (b * w)) by exact (Qlt_le_weak 0 (b * w) Hr0).
  assert (Hrne : ~ ((b * w) == 0)) by exact (abl_qlt_neq0 (b * w) Hr0).
  (* 比例右乘归形：t·(b·w) == v − b（倒数归一，comm 形归右逆） *)
  assert (Htr : Qeq ((abl_bridge_ratio v b w) * (b * w)) (v - b)).
  { unfold abl_bridge_ratio.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ (b * w)) (b * w)).
    rewrite (Qmult_inv_r (b * w) Hrne).
    apply Qmult_1_r. }
  assert (Hsc : Qle ((abl_bridge_ratio v b w) * (b * w))
                    (abl_qofnat n * (b * w))).
  { exact (Qmult_le_compat_r (abl_bridge_ratio v b w) (abl_qofnat n) (b * w)
             Hratio Hrle). }
  assert (H1 : Qle (v - b) (abl_qofnat n * (b * w))).
  { exact (abl_qle_eq_l (v - b) ((abl_bridge_ratio v b w) * (b * w))
             (abl_qofnat n * (b * w)) (Qeq_sym _ _ Htr) Hsc). }
  assert (H2 : Qle v (abl_qofnat n * (b * w) + b)).
  { apply (abl_qle_eq_l v (v - b + b) (abl_qofnat n * (b * w) + b)).
    - ring.
    - exact (Qplus_le_compat (v - b) (abl_qofnat n * (b * w)) b b H1
               (Qle_refl b)). }
  apply (abl_qle_eq_r v (abl_qofnat n * (b * w) + b)
           (b * (1 + abl_qofnat n * w))).
  - exact H2.
  - ring.
Qed.

(* 末前件见证引理：四前提 ⟹ sigT (fun n => v ≤ b·(1+n·w))，
   w := /p−1，见证 n := abl_hqarch_nat p v b（闭式计算项）。 *)
Lemma abl_hqarch_witness_site : forall (p v b : Q),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  sigT (fun n : nat => Qle v (b * (1 + abl_qofnat n * (/ p - 1)))).
Proof.
  intros p v b Hp0 Hp1 Hvt0 Hb0.
  exists (abl_hqarch_nat p v b).
  apply (abl_bridge_step v b (/ p - 1) (abl_hqarch_nat p v b) Hb0).
  - exact (abl_canon_w_pos p Hp0 Hp1).
  - unfold abl_hqarch_nat. apply abl_arch.
Qed.

(* ============================================================ *)
(* Part C：Hqarch 全站闭合定理（本片核心交付）                            *)
(*   与源件 R2BishopLogSel.v L319-320 前件位逐项同形                    *)
(*   （四前提 + sigT 谓词体；幂件 abl_qpow↔mixe_qpow 同体更名），       *)
(*   由 X4 件 abl_hqarch_via_bern 一步闭合——Hqarch 全站落定。           *)
(* ============================================================ *)

Theorem abl_hqarch_site_closed : forall (p v b : Q),
  Qlt 0 p -> Qlt p 1 -> Qlt 0 v -> Qlt 0 b ->
  sigT (fun j : nat => Qle (abl_qpow p j * v) b).
Proof.
  intros p v b Hp0 Hp1 Hvt0 Hb0.
  destruct (abl_hqarch_witness_site p v b Hp0 Hp1 Hvt0 Hb0) as [n Hn].
  exact (abl_hqarch_via_bern p v b n Hp0 Hp1 Hvt0 Hb0 Hn).
Qed.

(* ============================================================ *)
(* 检验审计：提取 Obj.magic 计数应为 0 + 逐件假设闭包                      *)
(* ============================================================ *)

Extraction "abl_hqarch_bridge_06_G3.ml" abl_q_arch_sig abl_hqarch_witness_site
  abl_hqarch_site_closed.

Print Assumptions abl_arch.
Print Assumptions abl_q_arch_sig.
Print Assumptions abl_bridge_step.
Print Assumptions abl_hqarch_witness_site.
Print Assumptions abl_hqarch_site_closed.
Print Assumptions abl_hqarch_via_bern.
Print Assumptions abl_canon_w_pos.
