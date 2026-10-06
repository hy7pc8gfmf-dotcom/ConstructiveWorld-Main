(* ============================================================ *)
(* NsepFindGeneric.v —— 判定器参数化的通用最小分离索引搜索。              *)
(*   使命：LW5SepComplexity 的有界线性搜索 lw5n_find 将分离判定器          *)
(*   lw5n_sep_dec 固定于函数体内（签名 Q -> nat -> nat -> nat）；本件把    *)
(*   判定器提升为显式参数 dec : Q -> nat -> bool，给出通用搜索             *)
(*   nsep_find（自 n 起逐阶试 dec，燃料尽返回预算端点 n）及定理包：        *)
(*   搜索上界 nsep_find_ub、命中特征 nsep_find_hit（停于分离阶且不越过    *)
(*   任一分离阶，结论以 Set 面 leiblw_Id 与 And := prod 承载）、最小性     *)
(*   nsep_find_min（停点之下无分离阶）；并给出预算化                       *)
(*   运行 nsep_first dec b q := nsep_find dec q 0 b 的 bound/hit/         *)
(*   least/minimal 四条推论。全部结论对任意 bool 分离判定器与任意预算      *)
(*   成立，与具体窗族解耦：pi 侧实例为 LW5SepComplexity 的                 *)
(*   lw5n_sep_dec := negb(lw5n_inwin)；sqrt(2) Newton 序列实例见 §3。     *)
(*   依赖：LW0LeibWindow（leiblw_Id/leiblw_id_intro/leiblw_id_eq/          *)
(*   leiblw_id_inv）、S01_BaseRing（And := A*B 的 Set 面合取）；           *)
(*   Stdlib：QArith/Qabs/ZArith/Arith/Bool/Lia/Extraction。                *)
(*   对标：LW5SepComplexity.v lw5n_find/lw5n_find_ub/lw5n_find_hit/        *)
(*   lw5n_find_min/lw5n_nsep_bound/lw5n_nsep_hit/lw5n_nsep_least/          *)
(*   lw5n_nsep_minimal——本件为该定理包的判定器参数化形式，逐条语句面      *)
(*   同形，仅以 dec 参量替代固定的 lw5n_sep_dec；sqrt(2) 实例与            *)
(*   UpReqSqrt3Irrational 的 is3 系 Newton 序列同构（常数 2 与 3 互替）。  *)
(*   构造性：零公理/零承认式/零经典逻辑；主结论面全 Set（leiblw_Id 与     *)
(*   And := prod），nat 序仅前提位置（结论位 nat 序为 nsep_find_ub/       *)
(*   nsep_first_bound/nsep_first_least 三件上界，如实注记）；nsep_find     *)
(*   为结构递归，提取面 Obj.magic = 0（§4 核查）；文末 Print               *)
(*   Assumptions 全 Closed。                                               *)
(*   编译配方：coqc.exe -native-compiler no -q -Q                         *)
(*   "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""   *)
(*   NsepFindGeneric.v（双 export COQLIB/ROCQLIB 至 9.1 lib/coq 后单发）。 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.

(* ============================================================ *)
(* §1 通用有界线性搜索                                            *)
(*    nsep_find 自 n 起逐阶试判定器 dec，命中即返回该阶；燃料尽返回      *)
(*    预算端点 n（返回端点不主张命中）。dec 为显式参数，本节全部结论      *)
(*    对任意 dec : Q -> nat -> bool 成立。                              *)
(* ============================================================ *)

Fixpoint nsep_find (dec : Q -> nat -> bool) (q : Q) (n fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | Datatypes.S f =>
      if dec q n then n else nsep_find dec q (Datatypes.S n) f
  end.

(** 搜索上界：nsep_find 不越过起点与燃料之和 n + fuel。 *)
Lemma nsep_find_ub : forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  (nsep_find dec q n fuel <= n + fuel)%nat.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n.
  - simpl. lia.
  - simpl. destruct (dec q n).
    + lia.
    + specialize (IH (Datatypes.S n)). lia.
Qed.

(** 命中特征：若区间 [n, n + fuel] 内某阶 n0 满足 dec q n0 = true，
    则 nsep_find 停于分离阶（第一支）且不越过 n0（第二支）。
    两支结论均为 Set 面：bool 判定等词取 leiblw_Id，合取取 S01_BaseRing
    的 And := prod。 *)
Lemma nsep_find_hit : forall (dec : Q -> nat -> bool) (q : Q) (fuel n n0 : nat),
  (n <= n0)%nat -> (n0 <= n + fuel)%nat ->
  leiblw_Id (dec q n0) true ->
  And (leiblw_Id (dec q (nsep_find dec q n fuel)) true)
      (leiblw_Id (Nat.leb (nsep_find dec q n fuel) n0) true).
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n n0 Hn1 Hn2 Hhit.
  - assert (Heq : n = n0) by lia. subst n0. simpl.
    split; [exact Hhit|].
    apply leiblw_id_eq. apply Nat.leb_le. lia.
  - simpl. destruct (dec q n) eqn:E.
    + split.
      * rewrite E. apply leiblw_id_intro.
      * apply leiblw_id_eq. apply Nat.leb_le. lia.
    + apply (IH (Datatypes.S n) n0).
      * destruct (Nat.eq_dec n n0) as [Heq|Hne].
        -- subst n0. apply leiblw_id_inv in Hhit. rewrite E in Hhit.
           discriminate Hhit.
        -- lia.
      * lia.
      * exact Hhit.
Qed.

(** 最小性：nsep_find 停点之下的每一阶 m 均不分离（dec q m = false，
    Set 面 leiblw_Id 承载）。 *)
Lemma nsep_find_min : forall (dec : Q -> nat -> bool) (q : Q) (fuel n m : nat),
  (n <= m)%nat -> (m < nsep_find dec q n fuel)%nat ->
  leiblw_Id (dec q m) false.
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n m Hn1 Hlt.
  - simpl in Hlt. lia.
  - simpl. destruct (dec q n) eqn:E.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt. lia.
    + simpl in Hlt. rewrite E in Hlt. cbn in Hlt.
      destruct (Nat.eq_dec n m) as [Heq|Hne].
      * subst m. rewrite E. apply leiblw_id_intro.
      * apply (IH (Datatypes.S n) m); lia.
Qed.

(* ============================================================ *)
(* §2 预算化运行与特征定理                                          *)
(*    nsep_first dec b q 为自 0 起以预算 b 运行的 nsep_find。四条        *)
(*    推论与 LW5SepComplexity 的 lw5n_nsep 四定理逐条同形，预算参数      *)
(*    b 显式：预算足用性（分离见证落入预算）属判定器实例方的职责，        *)
(*    不在本件主张。                                                     *)
(* ============================================================ *)

Definition nsep_first (dec : Q -> nat -> bool) (b : nat) (q : Q) : nat :=
  nsep_find dec q 0 b.

(** 运行上界：nsep_first 不越预算 b。 *)
Theorem nsep_first_bound : forall (dec : Q -> nat -> bool) (b : nat) (q : Q),
  (nsep_first dec b q <= b)%nat.
Proof.
  intros dec b q. unfold nsep_first.
  pose proof (nsep_find_ub dec q b 0) as H. lia.
Qed.

(** 命中定理：预算内存在分离阶则 nsep_first 停于分离阶。 *)
Theorem nsep_first_hit : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  leiblw_Id (dec q (nsep_first dec b q)) true.
Proof.
  intros dec b q n0 Hb Hhit. unfold nsep_first.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [H _].
  exact H.
Qed.

(** 不越定理：nsep_first 不越过预算内任一分离阶。 *)
Theorem nsep_first_least : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  (nsep_first dec b q <= n0)%nat.
Proof.
  intros dec b q n0 Hb Hhit.
  apply Nat.leb_le. apply leiblw_id_inv.
  destruct (nsep_find_hit dec q b 0 n0 (Nat.le_0_l n0) Hb Hhit) as [_ H].
  exact H.
Qed.

(** 最小性特征定理：预算内的最小分离阶被 nsep_first 逐字取到
    （存在分离阶 n0 且 [0, n0) 内无分离阶，则 nsep_first = n0 的
    Set 面 leiblw_Id 等词）。 *)
Theorem nsep_first_minimal : forall (dec : Q -> nat -> bool) (b : nat) (q : Q)
    (n0 : nat),
  (n0 <= b)%nat ->
  leiblw_Id (dec q n0) true ->
  (forall m : nat, (m < n0)%nat -> leiblw_Id (dec q m) false) ->
  leiblw_Id (nsep_first dec b q) n0.
Proof.
  intros dec b q n0 Hb Hn Hmin.
  assert (Hhit := nsep_first_hit dec b q n0 Hb Hn).
  assert (Hle := nsep_first_least dec b q n0 Hb Hn).
  destruct (Nat.eq_dec (nsep_first dec b q) n0) as [E|E].
  - rewrite E. apply leiblw_id_intro.
  - exfalso.
    assert (Hlt : (nsep_first dec b q < n0)%nat) by lia.
    specialize (Hmin _ Hlt).
    assert (Ht : dec q (nsep_first dec b q) = true)
      by (apply leiblw_id_inv; exact Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Qed.

(* ============================================================ *)
(* §3 实例：sqrt(2) Newton 序列分离判定器                            *)
(*    迭代 x_0 = 2，x_{n+1} = (x_n + 2/x_n)*(1/2)；平方误差             *)
(*    delta_n = x_n^2 - 2，窗宽 e_n = (1/2)*delta_n。判定器 ir2_sep_dec  *)
(*    在阶 n 处问 |q - x_n| 是否已逃出窗 e_n（判定面取 Qle_bool 的       *)
(*    否定，与 LW5SepComplexity 的 lw5n_sep_dec 出窗形同构）。            *)
(* ============================================================ *)

Fixpoint ir2_x (n : nat) : Q :=
  match n with
  | 0%nat => 2%Q
  | Datatypes.S m => (ir2_x m + 2%Q / ir2_x m) * (1 # 2)
  end.

Definition ir2_delta (n : nat) : Q := ir2_x n * ir2_x n - 2%Q.
Definition ir2_e (n : nat) : Q := (1 # 2) * ir2_delta n.

Definition ir2_sep_dec (q : Q) (n : nat) : bool :=
  negb (Qle_bool (Qabs ((q - ir2_x n)%Q)) (ir2_e n)).

(** 实例类型面：ir2_sep_dec 合于 nsep_find 的判定器参量形。 *)
Check (ir2_sep_dec : Q -> nat -> bool).
Check (nsep_find ir2_sep_dec : Q -> nat -> nat -> nat).

(* ============================================================ *)
(* §4 计算抽查＋提取＋假设审计                                        *)
(*    样例 q = 3/2：x_0 = 2，e_0 = 1，|3/2 - 2| = 1/2 不出窗，           *)
(*    故 dec(0) = false；x_2 = 17/12 与 e_2 = 1/288 处 |3/2 - 17/12|     *)
(*    = 1/12 > 1/288，故 dec(2) = true；最小命中阶为 2。                  *)
(* ============================================================ *)

Eval vm_compute in (ir2_sep_dec (3 # 2) 0, ir2_sep_dec (3 # 2) 2).
Eval vm_compute in (ir2_sep_dec (3 # 2) 3).
Eval vm_compute in (nsep_find ir2_sep_dec (3 # 2) 0 10).

Separate Extraction nsep_find nsep_first ir2_sep_dec ir2_x ir2_e ir2_delta.

Print Assumptions nsep_find_ub.
Print Assumptions nsep_find_hit.
Print Assumptions nsep_find_min.
Print Assumptions nsep_first_bound.
Print Assumptions nsep_first_hit.
Print Assumptions nsep_first_least.
Print Assumptions nsep_first_minimal.
