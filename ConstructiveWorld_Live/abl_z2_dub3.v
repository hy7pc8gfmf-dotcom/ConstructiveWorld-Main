(* ============================================================ *)
(* abl_z2_dub3.v —— d_n := lcm(1..n) ≤ 3^n（Hanson 1972）路线基础段     *)
(*                                                               *)
(* 使命：d_n 的指数增长控制 d_n ≤ 3^n 是 ζ2 塔整性面 d_n²·I_n 终装配的   *)
(*   登记硬前置。本件交付 Hanson 路线的地基段：Sylvester 序列            *)
(*   a_1 = 2，a_{k+1} = a_1·…·a_k + 1（记 P_k = a_1···a_k），及其上的     *)
(*   稠密不等式（Hanson 引理一的核）：                                   *)
(*     1 + Σ_{j<k} ⌊s/a_{j+1}⌋ ≤ s（1 ≤ s）。                           *)
(* 数学内容：Hanson（Canad. Math. Bull. 15 (1972)，33–37）证              *)
(*   lcm(1..n) = ∏_{p^a ≤ n} p < 3^n。其以 C(n) = n!/∏_i⌊n/a_i⌋! 为中介： *)
(*   稠密不等式给出逐素数赋值不等式 ⌊log_p n⌋ ≤ v_p(C(n))（对每个         *)
(*   j ≤ ⌊log_p n⌋ 取 Y = ⌊n/p^j⌋ ≥ 1 代入本件主定理即得），故 lcm(1..n)  *)
(*   整除 C(n)；C(n) 的上界由 Σ_i (ln a_i)/a_i < ln 3 封顶。本件交付      *)
(*   稠密不等式全强度；赋值桥（Legendre 和恒等式 + 逐层比较）与           *)
(*   C(n) < 3^n 档为后续件，见件尾诚实边界登记。                         *)
(* 依赖：Stdlib（Arith.Arith/Lia）+ HansonLcm（Set 面比较器 hl_le_t）。   *)
(* 构造性：全件 Qed，零公理声明、零经典逻辑；主语句面 hl_le_t : Set       *)
(*   （HansonLcm 承载，Id 型承载），支撑引理为 nat 层 Prop 面、仅服务      *)
(*   推理；z2d_sylv_P 与 z2d_sylv_sum 皆 Fixpoint 可执行；                *)
(*   文尾 Print Assumptions 全语句清单复核。                             *)
(* 编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&      *)
(*   ulimit -s 65532 && nice -19 rocq c -native-compiler no               *)
(*   -Q vo_local_world_unified_0930 "" -Q . "" abl_z2_dub3.v              *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Lia.
Require Import HansonLcm.

(* ============================================================ *)
(* §A Sylvester 序列与求和承载                                          *)
(* ============================================================ *)

(* P_k = a_1·…·a_k：P_0 = 1（空积），P_{k+1} = P_k·(P_k + 1)；
   a_{k+1} := P_k + 1，即 a_1 = 2，a_2 = 3，a_3 = 7，a_4 = 43，… *)
Fixpoint z2d_sylv_P (k : nat) : nat :=
  match k with
  | O => 1
  | S k' => z2d_sylv_P k' * (z2d_sylv_P k' + 1)
  end.

Definition z2d_sylv_a (k : nat) : nat := z2d_sylv_P k + 1.

(* Σ_{j<k} ⌊Y/a_{j+1}⌋：有限和承载（a_{j+1} > Y 的项自然为零） *)
Fixpoint z2d_sylv_sum (k Y : nat) : nat :=
  match k with
  | O => 0
  | S k' => z2d_sylv_sum k' Y + Y / z2d_sylv_a k'
  end.

Lemma z2d_sylv_P_pos : forall k : nat, 1 <= z2d_sylv_P k.
Proof.
  induction k as [| k IH]; cbn [z2d_sylv_P]; lia.
Qed.

Lemma z2d_sylv_a_neq0 : forall k : nat, z2d_sylv_a k <> 0.
Proof.
  intro k. unfold z2d_sylv_a. pose proof (z2d_sylv_P_pos k). lia.
Qed.

(* 数值锚：P_3 = 2·3·7 = 42（小实例直算） *)
Lemma z2d_sylv_P_3 : z2d_sylv_P 3 = 42.
Proof. reflexivity. Qed.

(* 数值锚：Σ_{j<3}⌊10/a_{j+1}⌋ = ⌊10/2⌋+⌊10/3⌋+⌊10/7⌋ = 5+3+1 = 9 *)
Lemma z2d_sylv_sum_3_10 : z2d_sylv_sum 3 10 = 9.
Proof. reflexivity. Qed.

(* ============================================================ *)
(* §B 序列整除与和的数乘交换                                            *)
(* ============================================================ *)

(* P_k 的因子封闭：j < k 则 a_{j+1} 整除 P_k（Sylvester 序列两两互素之根） *)
Lemma z2d_sylv_dvd : forall j k : nat,
  j < k -> Nat.divide (z2d_sylv_a j) (z2d_sylv_P k).
Proof.
  intros j k. induction k as [| k IH]; intros Hj.
  - lia.
  - destruct (Nat.eq_dec j k) as [E|NE].
    + rewrite E. unfold z2d_sylv_a. cbn [z2d_sylv_P].
      exists (z2d_sylv_P k). ring.
    + assert (Hjk : j < k) by lia.
      destruct (IH Hjk) as [q Hq].
      cbn [z2d_sylv_P].
      exists (q * (z2d_sylv_P k + 1)).
      rewrite Hq. ring.
Qed.

(* 乘除换位不等式：a 整除 d 时 d·⌊s/a⌋ ≤ (d/a)·s。
   （a·⌊s/a⌋ ≤ s 与 d = (d/a)·a 逐项放大。） *)
Lemma z2d_div_mul_le : forall d a s : nat,
  a <> 0 -> Nat.divide a d -> d * (s / a) <= (d / a) * s.
Proof.
  intros d a s Ha [q Hq].
  assert (Eda : d / a = q) by (rewrite Hq; apply Nat.div_mul; exact Ha).
  pose proof (Nat.div_mod_eq s a) as Hdm.
  rewrite Eda, Hq.
  rewrite <- Nat.mul_assoc. apply Nat.mul_le_mono_l. lia.
Qed.

(* 和的数乘交换：诸 a_{j+1} 皆整除 X 时，Σ⌊c·X/a_{j+1}⌋ = c·Σ⌊X/a_{j+1}⌋ *)
Lemma z2d_sylv_sum_mul : forall k c X : nat,
  (forall j : nat, j < k -> Nat.divide (z2d_sylv_a j) X) ->
  z2d_sylv_sum k (c * X) = c * z2d_sylv_sum k X.
Proof.
  induction k as [| k IH]; intros c X H.
  - cbn [z2d_sylv_sum]. lia.
  - cbn [z2d_sylv_sum].
    rewrite (IH c X) by (intros j Hj; apply H; lia).
    pose proof (z2d_sylv_a_neq0 k) as Ha.
    destruct (H k (Nat.lt_succ_diag_r k)) as [q Hq].
    assert (E1 : (c * X) / z2d_sylv_a k = c * (X / z2d_sylv_a k)).
    { rewrite Hq. rewrite Nat.mul_assoc.
      rewrite Nat.div_mul by exact Ha.
      rewrite Nat.div_mul by exact Ha.
      reflexivity. }
    assert (E2 : X / z2d_sylv_a k = q).
    { rewrite Hq. apply Nat.div_mul. exact Ha. }
    rewrite E1, E2. ring.
Qed.

(* 导数恒等式：Σ_{j<k} ⌊P_k/a_{j+1}⌋ + 1 = P_k
   （P_k 的真因子和恰亏一——P_3 = 42 = 21+14+6+1 之一般形） *)
Lemma z2d_sylv_deriv : forall k : nat,
  z2d_sylv_sum k (z2d_sylv_P k) + 1 = z2d_sylv_P k.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [z2d_sylv_P z2d_sylv_sum].
    rewrite (Nat.mul_comm (z2d_sylv_P k) (z2d_sylv_P k + 1)).
    rewrite (z2d_sylv_sum_mul k (z2d_sylv_P k + 1) (z2d_sylv_P k))
      by (intros j Hj; apply z2d_sylv_dvd; exact Hj).
    pose proof (z2d_sylv_a_neq0 k) as Ha.
    assert (E1 : (z2d_sylv_P k + 1) * z2d_sylv_P k / z2d_sylv_a k
                 = z2d_sylv_P k).
    { unfold z2d_sylv_a. rewrite Nat.mul_comm. apply Nat.div_mul. exact Ha. }
    rewrite E1.
    assert (Eshape : (z2d_sylv_P k + 1) * (z2d_sylv_sum k (z2d_sylv_P k) + 1)
                     = (z2d_sylv_P k + 1) * z2d_sylv_sum k (z2d_sylv_P k)
                       + z2d_sylv_P k + 1) by ring.
    rewrite <- Eshape, IH. ring.
Qed.

(* ============================================================ *)
(* §C 稠密不等式（Hanson 引理一的核）                                    *)
(* ============================================================ *)

(* 密度不等式：P_k·Σ_{j<k}⌊s/a_{j+1}⌋ + s ≤ s·P_k。
   论证：P_{k+1} = P_k·(P_k+1) 分解后，逐项以 a_{k+1} 整除换位放大；
   尾部由归纳前提 P_k·Σ + s ≤ s·P_k 乘 (P_k+1) 与
   (P_k+1)·⌊s/(P_k+1)⌋ ≤ s（div_mod）两肢线性闭合。 *)
Lemma z2d_sylv_sum_density : forall k s : nat,
  z2d_sylv_P k * z2d_sylv_sum k s + s <= s * z2d_sylv_P k.
Proof.
  intros k s. induction k as [| k IH].
  - cbn [z2d_sylv_P z2d_sylv_sum]. lia.
  - pose proof (Nat.div_mod_eq s (z2d_sylv_a k)) as Hdm.
    assert (Hd : z2d_sylv_a k * (s / z2d_sylv_a k) <= s) by lia.
    pose proof (Nat.mul_le_mono_l (z2d_sylv_P k * z2d_sylv_sum k s + s)
                  (s * z2d_sylv_P k) (z2d_sylv_a k) IH) as HIH.
    unfold z2d_sylv_a in *.
    cbn [z2d_sylv_P z2d_sylv_sum].
    unfold z2d_sylv_a.
    assert (H41 : (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
                  + z2d_sylv_P k * s + s
                  = (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s + s))
      by ring.
    assert (H42 : (z2d_sylv_P k + 1) * (s * z2d_sylv_P k)
                  = s * (z2d_sylv_P k * (z2d_sylv_P k + 1))) by ring.
    assert (H43 : z2d_sylv_P k * (z2d_sylv_P k + 1)
                    * (z2d_sylv_sum k s + s / (z2d_sylv_P k + 1)) + s
                  = (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
                    + z2d_sylv_P k * ((z2d_sylv_P k + 1) * (s / (z2d_sylv_P k + 1)))
                    + s) by ring.
    assert (H44 : z2d_sylv_P k * ((z2d_sylv_P k + 1) * (s / (z2d_sylv_P k + 1)))
                  <= z2d_sylv_P k * s)
      by (apply Nat.mul_le_mono_l; exact Hd).
    rewrite H43.
    apply Nat.le_trans with
      (m := (z2d_sylv_P k + 1) * (z2d_sylv_P k * z2d_sylv_sum k s)
            + z2d_sylv_P k * s + s).
    + apply Nat.add_le_mono_r. apply Nat.add_le_mono_l. exact H44.
    + rewrite H41, <- H42. exact HIH.
Qed.

(* 稠密不等式（商形）：1 ≤ s 则 Σ_{j<k}⌊s/a_{j+1}⌋ < s *)
Lemma z2d_sylv_sum_lt : forall k s : nat,
  1 <= s -> z2d_sylv_sum k s < s.
Proof.
  intros k s Hs.
  pose proof (z2d_sylv_sum_density k s) as HD.
  destruct (Nat.lt_ge_cases (z2d_sylv_sum k s) s) as [Hlt|Hge]; [exact Hlt|].
  exfalso.
  pose proof (Nat.mul_le_mono_r s (z2d_sylv_sum k s) (z2d_sylv_P k) Hge) as Hm.
  lia.
Qed.

(* ============================================================ *)
(* §D 主定理（Set 面承载）与诚实边界登记                                 *)
(* ============================================================ *)

(* 主定理（Sylvester 稠密不等式，Set 面）：对一切 k 与 1 ≤ s，
   1 + Σ_{j<k}⌊s/a_{j+1}⌋ ≤ s。
   Hanson 1972 引理一之核：对素数 p 与 j ≤ ⌊log_p n⌋ 取 s = ⌊n/p^j⌋ ≥ 1，
   即得 ⌊n/p^j⌋ - Σ_i⌊n/(a_{i+1}·p^j)⌋ ≥ 1，逐层求和给出
   ⌊log_p n⌋ ≤ v_p(n!/∏_i⌊n/a_{i+1}⌋!)，从而 lcm(1..n) 整除
   n!/∏_i⌊n/a_{i+1}⌋!。 *)
Theorem z2d_sylv_floor_t : forall k s : nat,
  1 <= s -> hl_le_t (z2d_sylv_sum k s + 1) s.
Proof.
  intros k s Hs. apply hl_le_to_le_t.
  pose proof (z2d_sylv_sum_lt k s Hs). lia.
Qed.

(* 诚实边界登记（非虚报声明）：本件主定理为 Hanson 1972 路线的地基段。
   通往 z2d 目标语句（hl_lcm_upto n ≤ 3^n）的余下三段为后续件，尚未入栈：
   其一，Legendre 和恒等式 v_p(m!) = Σ_j⌊m/p^j⌋（两向）；
   其二，赋值桥 ⌊log_p n⌋ ≤ v_p(n!/∏_i⌊n/a_{i+1}⌋!)（逐层取
   s = ⌊n/p^j⌋ 用本件主定理，配嵌套除法 ⌊⌊n/p^j⌋/a⌋ = ⌊n/(a·p^j)⌋）；
   其三，上界档 n!/∏_i⌊n/a_{i+1}⌋! ≤ 3^n（Sylvester 熵不等式
   Σ_i (ln a_i)/a_i < ln 3 的 nat 化，含小 n 档核对）。
   三段皆未在本件以任何形式声称完成。 *)

(* 假设审计：以下 Print Assumptions 输出应为零依赖（零承认复核）。
   （Print Assumptions 日志不回显定理名，证据按本清单挂序对照。） *)
Print Assumptions z2d_sylv_P_pos.
Print Assumptions z2d_sylv_a_neq0.
Print Assumptions z2d_sylv_P_3.
Print Assumptions z2d_sylv_sum_3_10.
Print Assumptions z2d_sylv_dvd.
Print Assumptions z2d_div_mul_le.
Print Assumptions z2d_sylv_sum_mul.
Print Assumptions z2d_sylv_deriv.
Print Assumptions z2d_sylv_sum_density.
Print Assumptions z2d_sylv_sum_lt.
Print Assumptions z2d_sylv_floor_t.
