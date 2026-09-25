(* ============================================================
   UpAblMixACount —— 使命行：mixa 对数二分选择器的谓词求值次数显式计数件。
   本件为二分搜索 mixa_bsearch 配备逐步计数的伴随函数 macnt_bsearch，
   证明其搜索结果与 mixa_bsearch 逐点一致（同构展开，计数不空）且谓词求值
   次数以燃料配给为上界；量级实例（区间 [0,K]、燃料 S(log₂(S K))）给出
   计数 ≤ S(log₂(S K)) = log₂(K+1)+1 的显式定理，并实例化到 Q 层选择器
   mixa_k_log_of，其窗口上端为 K_win = mixa_win v (1-k0) b0。
   依赖：UpReqMixLogA（mixa_bsearch / mixa_test / mixa_win /
   mixa_k_log_of / mixa_sel_accounts）；stdlib 仅 PeanoNat、Lia、QArith。
   对标：UpReqMixLogB.v mixb_sel_count（无窗两相选择器的计数定理）在本库的
   单相带窗对偶形；stdlib Nat.log2_spec。
   构造性注记：macnt_bsearch 是 Set 层 (nat*nat) 值的结构递归函数（递归位为
   燃料参数）；全部语句为 nat/Q 面的等式与序；零承认；全件可提取。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================*)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import QArith.
Require Import UpReqMixLogA.

Local Open Scope Q_scope.

(* ================= §1 计数伴随二分与基础性质 ================= *)

(** 计数伴随函数：与 mixa_bsearch 相同的分枝骨架，额外累计谓词求值次数。
    返回 (搜索结果, 谓词求值次数)；两枝递归调用经 let 约束共享一份计算。 *)
Fixpoint macnt_bsearch (test : nat -> bool) (f lo hi : nat) : nat * nat :=
  match f with
  | Datatypes.O => (lo, Datatypes.O)
  | Datatypes.S f' =>
      if Nat.eqb lo hi then (lo, Datatypes.O)
      else if test (Nat.div2 (Nat.add lo hi))
        then let r := macnt_bsearch test f' lo (Nat.div2 (Nat.add lo hi)) in
             (fst r, Datatypes.S (snd r))
        else let r := macnt_bsearch test f' (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi in
             (fst r, Datatypes.S (snd r))
  end.

(** 计数不空：macnt_bsearch 的搜索结果与 mixa_bsearch 逐点一致。
    两函数的分枝骨架逐枝相同（区间端点相等判定、中点谓词判定、两枝递归），
    对燃料参数作归纳，按两个布尔判定分情形后由归纳假设即得。 *)
Lemma macnt_bsearch_result : forall (test : nat -> bool) (f lo hi : nat),
  fst (macnt_bsearch test f lo hi) = mixa_bsearch test f lo hi.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - reflexivity.
  - cbn [macnt_bsearch mixa_bsearch]. cbv zeta. cbn [fst snd].
    destruct (Nat.eqb lo hi); [reflexivity |].
    destruct (test (Nat.div2 (Nat.add lo hi))); cbn [fst snd];
      rewrite IH; reflexivity.
Qed.

(** 计数上界：谓词求值次数不超过燃料配给（无条件：不需单调性、
    端点通过性或任何窗口前提）。每层燃料至多一次谓词求值：
    区间端点相等的层与燃料耗尽的层零次。对燃料参数归纳。 *)
Lemma macnt_bsearch_c_le : forall (test : nat -> bool) (f lo hi : nat),
  Nat.le (snd (macnt_bsearch test f lo hi)) f.
Proof.
  intros test f. induction f as [| f IH]; intros lo hi.
  - cbn [macnt_bsearch snd]. lia.
  - cbn [macnt_bsearch]. destruct (Nat.eqb lo hi).
    + cbn [snd]. lia.
    + destruct (test (Nat.div2 (Nat.add lo hi))).
      * cbv zeta. cbn [snd].
        specialize (IH lo (Nat.div2 (Nat.add lo hi))). lia.
      * cbv zeta. cbn [snd].
        specialize (IH (Datatypes.S (Nat.div2 (Nat.add lo hi))) hi). lia.
Qed.

(* ================= §2 量级实例形与 Q 层选择器实例 ================= *)

(** 量级实例（窗口宽 K）：区间 [0,K]（候选数 S K = K+1 面，含 K=0）上
    以燃料 S(log₂(S K)) 运行，与 mixa_fuel_log 的配给一致；
    谓词求值次数 ≤ S(log₂(S K)) = log₂(K+1)+1。由 macnt_bsearch_c_le
    以燃料配给实例化直接推得。 *)
Theorem macnt_win_count : forall (test : nat -> bool) (K : nat),
  Nat.le (snd (macnt_bsearch test (Datatypes.S (Nat.log2 (Datatypes.S K))) 0 K))
         (Datatypes.S (Nat.log2 (Datatypes.S K))).
Proof.
  intros test K.
  pose proof (macnt_bsearch_c_le test
               (Datatypes.S (Nat.log2 (Datatypes.S K))) 0 K).
  lia.
Qed.

(** Q 层选择器实例的计数不空：mixa_k_log_of k0 v b0 的求值结果等于
    计数伴随函数在完全相同实参下的第一分量；故其谓词求值次数即
    macnt_bsearch 的计数分量。由 macnt_bsearch_result 直接推得。 *)
Theorem macnt_k_log_of_exec : forall (k0 v b0 : Q),
  mixa_k_log_of k0 v b0 =
  fst (macnt_bsearch (mixa_test k0 v b0)
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
         0 (mixa_win v (1 - k0) b0)).
Proof.
  intros k0 v b0. unfold mixa_k_log_of.
  symmetry. apply macnt_bsearch_result.
Qed.

(** 主计数定理（A 路选择器的显式计数形）：Q 层选择器 mixa_k_log_of k0 v b0
    执行中的谓词求值次数 ≤ S(log₂(S K_win)) = log₂(K_win+1)+1，
    其中窗口上端 K_win = mixa_win v (1-k0) b0。语句无条件：
    不需 Qlt 0 k0 等四个正性前提（计数与正确性相互独立）。 *)
Theorem macnt_k_log_of_count : forall (k0 v b0 : Q),
  Nat.le (snd (macnt_bsearch (mixa_test k0 v b0)
                (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
                0 (mixa_win v (1 - k0) b0)))
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0)))).
Proof.
  intros k0 v b0.
  apply (macnt_bsearch_c_le (mixa_test k0 v b0)
           (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
           0 (mixa_win v (1 - k0) b0)).
Qed.

(** 与正确性合取的完整语句：在 mixa_sel_accounts 的四个 Q 正性前提下，
    mixa_k_log_of 的返回值通过判定、其下方全部不通过、且谓词求值次数
    ≤ S(log₂(S K_win))——两个正确性结论与计数上界一并成立。 *)
Theorem macnt_sel_accounts_count : forall k0 v b0 : Q,
  Qlt 0 k0 -> Qlt k0 (1#1) -> Qlt 0 v -> Qlt 0 b0 ->
  mixa_test k0 v b0 (mixa_k_log_of k0 v b0) = true /\
  (forall j : nat, Nat.lt j (mixa_k_log_of k0 v b0) ->
     mixa_test k0 v b0 j = false) /\
  Nat.le (snd (macnt_bsearch (mixa_test k0 v b0)
                (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0))))
                0 (mixa_win v (1 - k0) b0)))
         (Datatypes.S (Nat.log2 (Datatypes.S (mixa_win v (1 - k0) b0)))).
Proof.
  intros k0 v b0 Hk0 Hk1 Hv Hb.
  pose proof (mixa_sel_accounts k0 v b0 Hk0 Hk1 Hv Hb) as [Ht Hmin].
  pose proof (macnt_k_log_of_count k0 v b0) as Hc.
  split; [exact Ht | split; [exact Hmin | exact Hc]].
Qed.

(* 追印面：全部证明件预期零承认闭 *)
Print Assumptions macnt_bsearch_result.
Print Assumptions macnt_bsearch_c_le.
Print Assumptions macnt_win_count.
Print Assumptions macnt_k_log_of_exec.
Print Assumptions macnt_k_log_of_count.
Print Assumptions macnt_sel_accounts_count.
