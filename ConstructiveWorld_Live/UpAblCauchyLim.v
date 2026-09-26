(* UpAblCauchyLim.v —— 调和序列 ucl_harm_seq 的完备性与极限＝0        *) (*   （real_lim 面非平凡具体输入实例）                                 *)
(* 使命：为实数极限谓词 real_lim 提供非平凡具体输入的完整实例——调和型 *) (*   序列 ucl_harm_seq（第 n 项＝1/(n+2)）：其双柯西条件经阿基米德性质 *)
(*   q_arch_inv 逐 eps 构造阈值（N 依赖 eps，非 O），由完备性           *)
(*   real_cauchy_complete 得抽象极限，再证极限＝real_const 0 并经       *)
(*   real_lim_unique 等同。                                             *)
(* 非平凡性：ucm_ 系各件的见证全为 N := O（零序列输入面）；本件阈值     *)
(*   N 依赖 eps（经 q_arch_inv 逐 eps 构造）——这是完备性定理在非平凡   *)
(*   具体输入面上的实际应用。                                           *)
(* 供给结构（八件，ucl_ 前缀）： *)
(*   基件四：ucl_harm_pos / ucl_harm_mono / ucl_harm_tail_lt /          *)
(*      ucl_harm_diff_abs_lt——1/(n+2) 的正性（由 q_arch_inv_pos）＋     *)
(*      单调（循 q_arch_inv_mono 的 Qinv_lt_contravar 链）＋尾界＋      *)
(*      双侧尾差界（q_abs_lt_two_sided 链）；                            *)
(*   A ucl_harm_cauchy——real_cauchy_complete 前提所要求的实值双柯西    *)
(*      条件（同形）在 ucl_harm_seq 面的实例，见证 N := q_arch_inv(eps/2)；*)
(*   B ucl_harm_complete——sigT(l, real_lim ucl_harm_seq l)，由          *)
(*      real_cauchy_complete 直接给出（抽象正则化对角线极限）；          *)
(*   C ucl_harm_lim_zero——real_lim ucl_harm_seq (real_const 0)；        *)
(*   D ucl_harm_limit_eq_zero——real_lim_unique 将 B 的抽象极限与        *)
(*      real_const 0 等同（real_eq 为 Set 层逐 eps 相等）。               *)
(* Q 层注记：eps/2 这类除法目标上 lra 失效，相关改写一律经              *)
(*   setoid_replace（ring/field 收束）＋ Qle_lt_trans/Qplus_le_compat    *)
(*   ＋ q_bound_eps_half/q_abs_lt_two_sided 完成。                        *)
(* 构造性注记：全件 Qed 闭合、零承认词面、无经典逻辑；交付语句面全       *)
(*   Set 层值（real_lt/real_eq/real_lim、And/Or、sigT 见证）；Prop 面改写 *)
(*   （Qlt/Qeq/Qle）全内联于证明内部；八件 Print Assumptions 全 Closed。  *)
(* 依赖：CW_ConstructiveWorld_219（q_arch_inv 系与完备性/唯一性定理所在）。*)
(* 对标：Bishop 完备性（正则化对角线构造）与调和型序列的构造性实例化。   *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard -LoadLimit 85 -CoreN 2 包裹，  *)
(*   输出经 -o 临时目录，树内 .vo 不重写。                                *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import Arith.PeanoNat.
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

(* 调和型尾项：ucl_harm n := 1/(n+2)（与 q_arch_inv 的单位分数形同形，
   q_arch_inv/q_arch_inv_mono/q_arch_inv_pos 经定义展开直接应用）。 *)
Definition ucl_harm (n : nat) : Q := (1 / (Z.of_nat (n + 2) # 1))%Q.

(* 具体序列：第 n 项＝常值实数 1/(n+2)——每一项各自具体、整体非平凡
   （非常值序列，非 real_zero/real_const 退化输入） *)
Definition ucl_harm_seq : nat -> Real := fun n => real_const (ucl_harm n).

(* 基件一：正性——由 q_arch_inv_pos 经 ucl_harm 定义展开直接推得 *)
Lemma ucl_harm_pos : forall n : nat, Qlt 0 (ucl_harm n).
Proof. intro n. exact (q_arch_inv_pos n). Qed.

(* 基件二：单调（n ≤ m ⟹ 1/(m+2) ≤ 1/(n+2)，分母增大则值减小；
   n < m 情形循 q_arch_inv_mono 的 Qinv_lt_contravar 链得严格不等） *)
Lemma ucl_harm_mono : forall n m : nat, (n <= m)%nat -> Qle (ucl_harm m) (ucl_harm n).
Proof.
  intros n m Hle.
  destruct (Nat.eq_dec n m) as [Heq | Hne].
  - subst. apply Qle_refl.
  - assert (Hlt : (n < m)%nat) by lia.
    apply Qlt_le_weak.
    setoid_replace (ucl_harm m) with (/ (Z.of_nat (m + 2) # 1))
      by (unfold ucl_harm, Qdiv; apply Qmult_1_l).
    setoid_replace (ucl_harm n) with (/ (Z.of_nat (n + 2) # 1))
      by (unfold ucl_harm, Qdiv; apply Qmult_1_l).
    assert (HposN : Qlt 0 (Z.of_nat (n + 2) # 1)) by (unfold Qlt; simpl; lia).
    assert (HposM : Qlt 0 (Z.of_nat (m + 2) # 1)) by (unfold Qlt; simpl; lia).
    apply (proj1 (Qinv_lt_contravar (Z.of_nat (n + 2) # 1) (Z.of_nat (m + 2) # 1)
                  HposN HposM)).
    unfold Qlt. simpl. lia.
Qed.

(* 基件三：尾界（N ≤ n 且 ucl_harm N < eps ⟹ ucl_harm n < eps，由单调性） *)
Lemma ucl_harm_tail_lt : forall (eps : Q) (N n : nat),
  (N <= n)%nat -> Qlt (ucl_harm N) eps -> Qlt (ucl_harm n) eps.
Proof.
  intros eps N n Hn Hlt.
  apply (Qle_lt_trans (ucl_harm n) (ucl_harm N) eps).
  - apply ucl_harm_mono. exact Hn.
  - exact Hlt.
Qed.

(* 基件四：双侧尾差界（0 ≤ a,b < e ⟹ |a − b| < e；应用 q_abs_lt_two_sided，
   两侧各以 Qopp_lt_compat 与 Qplus_le_compat 的单调链推得） *)
Lemma ucl_harm_diff_abs_lt : forall (a b e : Q),
  Qlt 0 e -> Qle 0 a -> Qle 0 b -> Qlt a e -> Qlt b e -> Qlt (Qabs (a - b)) e.
Proof.
  intros a b e He Hap Hbp Hae Hbe.
  apply (q_abs_lt_two_sided (a - b) e He).
  - (* −e < a − b：−e < −b（Qopp_lt_compat 反号）＋ −b ≤ −b + a（Qplus_le_compat） *)
    assert (H1 : Qlt (- e) (- b)) by (apply Qopp_lt_compat; exact Hbe).
    assert (H2 : Qle ((- b) + 0) ((- b) + a)).
    { apply (Qplus_le_compat (- b) (- b) 0 a).
      - apply Qle_refl.
      - exact Hap. }
    setoid_replace ((- b) + 0) with (- b) in H2 by ring.
    setoid_replace ((- b) + a) with (a - b) in H2 by ring.
    exact (Qlt_le_trans (- e) (- b) (a - b) H1 H2).
  - (* a − b < e：a − b = a + (−b) ≤ a + 0（Qplus_le_compat，−b ≤ 0）< e *)
    assert (H3 : Qle ((- b) + 0) ((- b) + b)).
    { apply (Qplus_le_compat (- b) (- b) 0 b).
      - apply Qle_refl.
      - exact Hbp. }
    setoid_replace ((- b) + 0) with (- b) in H3 by ring.
    setoid_replace ((- b) + b) with 0 in H3 by ring.
    assert (H4 : Qle (a + (- b)) (a + 0)).
    { apply (Qplus_le_compat a a (- b) 0).
      - apply Qle_refl.
      - exact H3. }
    setoid_replace (a + (- b)) with (a - b) in H4 by ring.
    setoid_replace (a + 0) with a in H4 by ring.
    exact (Qle_lt_trans (a - b) a e H4 Hae).
Qed.

(* A. 双柯西条件的实例化：real_cauchy_complete 前提所要求的实值双柯西条件
   （同形）在 ucl_harm_seq 面的实例。见证 N := q_arch_inv(eps/2) 的实例——
   阿基米德阈值（对比 ucm_ 系的 N := O，此处为非平凡见证）。 *)
Corollary ucl_harm_cauchy :
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      (N <= m)%nat -> (N <= n)%nat ->
      And (real_lt (real_plus (ucl_harm_seq m) (real_opp (ucl_harm_seq n))) (real_const eps))
          (real_lt (real_plus (ucl_harm_seq n) (real_opp (ucl_harm_seq m))) (real_const eps))).
Proof.
  intros eps Heps.
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps2q : Qlt 0 (eps / 2)) by (apply QltT_to_Qlt; exact Heps2).
  destruct (q_arch_inv (eps / 2)%Q Heps2q) as [N0 HN0].
  exists N0.
  intros m n Hm Hn.
  assert (Hmb : Qlt (ucl_harm m) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 m Hm HN0)).
  assert (Hnb : Qlt (ucl_harm n) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 n Hn HN0)).
  assert (Hmpos : Qle 0 (ucl_harm m)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (Hnpos : Qle 0 (ucl_harm n)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (Habs : Qlt (Qabs (ucl_harm m - ucl_harm n)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm m) (ucl_harm n) (eps / 2)%Q
               Heps2q Hmpos Hnpos Hmb Hnb)).
  assert (Habs2 : Qlt (Qabs (ucl_harm n - ucl_harm m)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm n) (ucl_harm m) (eps / 2)%Q
               Heps2q Hnpos Hmpos Hnb Hmb)).
  split.
  - (* 前向：eps − (a − b) == (b − a) + eps（ring）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (real_plus (ucl_harm_seq m) (real_opp (ucl_harm_seq n))) k)
        with (ucl_harm m - ucl_harm n)%Q.
      change (projT1 (real_const eps) k) with eps.
      apply Qlt_to_QltT.
      setoid_replace (eps - (ucl_harm m - ucl_harm n))
        with ((ucl_harm n - ucl_harm m) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm n - ucl_harm m) eps Hepsq Habs2).
  - (* 反向：对称（m、n 互换）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (real_plus (ucl_harm_seq n) (real_opp (ucl_harm_seq m))) k)
        with (ucl_harm n - ucl_harm m)%Q.
      change (projT1 (real_const eps) k) with eps.
      apply Qlt_to_QltT.
      setoid_replace (eps - (ucl_harm n - ucl_harm m))
        with ((ucl_harm m - ucl_harm n) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm m - ucl_harm n) eps Hepsq Habs).
Qed.

(* B. 完备性的实际使用：real_cauchy_complete（Bishop 正则化、零自由变元）
   应用于具体调和序列面——产出抽象正则化对角线极限。 *)
Corollary ucl_harm_complete :
  sigT (fun l : Real => real_lim ucl_harm_seq l).
Proof. exact (real_cauchy_complete ucl_harm_seq ucl_harm_cauchy). Qed.

(* C. 具体极限：ucl_harm_seq 收敛到 real_const 0，
   见证 N := q_arch_inv(eps/2) 的实例（阿基米德阈值）。 *)
Corollary ucl_harm_lim_zero : real_lim ucl_harm_seq (real_const 0).
Proof.
  intros eps Heps.
  assert (Heps2 : QltT 0 (eps / 2)%Q).
  { apply Qlt_to_QltT. apply Qlt_shift_div_l.
    - reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  assert (Hepsq : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps2q : Qlt 0 (eps / 2)) by (apply QltT_to_Qlt; exact Heps2).
  destruct (q_arch_inv (eps / 2)%Q Heps2q) as [N0 HN0].
  exists N0.
  intros n Hn.
  assert (Hnb : Qlt (ucl_harm n) (eps / 2)%Q)
    by (apply (ucl_harm_tail_lt (eps / 2)%Q N0 n Hn HN0)).
  assert (Hnpos : Qle 0 (ucl_harm n)) by (apply Qlt_le_weak; apply ucl_harm_pos).
  assert (HabsC : Qlt (Qabs (ucl_harm n - 0)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt (ucl_harm n) 0 (eps / 2)%Q
               Heps2q Hnpos (Qle_refl 0) Hnb Heps2q)).
  assert (HabsC2 : Qlt (Qabs (0 - ucl_harm n)) (eps / 2)%Q)
    by (apply (ucl_harm_diff_abs_lt 0 (ucl_harm n) (eps / 2)%Q
               Heps2q (Qle_refl 0) Hnpos Heps2q Hnb)).
  split.
  - (* 前向：(0 + eps) − x == (0 − x) + eps（ring，真等式）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (ucl_harm_seq n) k) with (ucl_harm n).
      change (projT1 (real_plus (real_const 0) (real_const eps)) k) with (0 + eps)%Q.
      apply Qlt_to_QltT.
      setoid_replace ((0 + eps) - ucl_harm n) with ((0 - ucl_harm n) + eps) by ring.
      exact (q_bound_eps_half (0 - ucl_harm n) eps Hepsq HabsC2).
  - (* 反向：x − (0 + −eps) == (x − 0) + eps（ring）⟹ q_bound_eps_half *)
    exists (eps / 2)%Q. split.
    + exact Heps2.
    + exists O. intros k Hk.
      change (projT1 (ucl_harm_seq n) k) with (ucl_harm n).
      change (projT1 (real_plus (real_const 0) (real_opp (real_const eps))) k)
        with (0 + - eps)%Q.
      apply Qlt_to_QltT.
      setoid_replace (ucl_harm n - (0 + - eps))
        with ((ucl_harm n - 0) + eps) by ring.
      exact (q_bound_eps_half (ucl_harm n - 0) eps Hepsq HabsC).
Qed.

(* D. 唯一性：real_lim_unique 将 ucl_harm_complete 的抽象正则化对角线极限
   与 real_const 0 等同（完备性与唯一性联用，real_eq 为 Set 层逐 eps 相等）。 *)
Corollary ucl_harm_limit_eq_zero :
  real_eq (projT1 ucl_harm_complete) (real_const 0).
Proof.
  exact (real_lim_unique ucl_harm_seq (projT1 ucl_harm_complete) (real_const 0)
         (projT2 ucl_harm_complete) ucl_harm_lim_zero).
Qed.

(* 假设审计：八件 Print Assumptions 全 Closed *)
Print Assumptions ucl_harm_pos.
Print Assumptions ucl_harm_mono.
Print Assumptions ucl_harm_tail_lt.
Print Assumptions ucl_harm_diff_abs_lt.
Print Assumptions ucl_harm_cauchy.
Print Assumptions ucl_harm_complete.
Print Assumptions ucl_harm_lim_zero.
Print Assumptions ucl_harm_limit_eq_zero.
