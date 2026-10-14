(* ============================================================ *)
(* abl_dmdnf2_oddlcm.v —— odd-lcm 分母承载件                      *)
(* 使命：以奇数最小公倍数 oddlcm(1..N) 为线性形式族整清分母承载：   *)
(*   (a) 定义面：od_prod(N)=∏奇≤N（双阶乘奇部）、oddlcm(N)=lcm奇≤N； *)
(*   (b) 见证接口面：任意奇数 2k+1 ≤ N 对 od_prod(N) 有整除见证      *)
(*       （sigT 乘子形）——截断段 m≥1 的奇分母 2n+2m+1 ≤ 2n+2M+1     *)
(*       全部一次清账（B1 件 b1_odd_div_dfact 只覆盖 2k+1 ≤ 2n+1，  *)
(*       本件把覆盖端推到 2n+2M+1）；                                *)
(*   (c) 增长界面：oddlcm N ≤ od_prod N ≤ fact N（Set 面 hl_le_t）。 *)
(* 诚实边界登记（禁虚报）：                                        *)
(*   - Hanson 3^N 档【不在池】：HansonLcm 件①诚实登记未达（无素数面   *)
(*     即无可达指数级界）、z2_dub3 Sylvester 桥余下三段未入栈——本件   *)
(*     增长界为积档弱界 od_prod ≤ fact（≈e^{N·lnN} 档），非 3^N 档；   *)
(*   - 紧档整除 D_{n,M} | 2^(n+M)·oddlcm(2n+2M+1)：独立复算 96 点    *)
(*     卡实但未成证——无 Hypothesis 位，不入证，留续作件；             *)
(*   - 量化裁定（独立复算权威）：c_new 三档全超门槛（真值载体 1.8876→2 *)
(*     / Hanson 引档 2.2201 / 实约简 3.0020 vs 1.568616/1.575536/   *)
(*     1.5868）→ 换核路线不成·三档归档；峰值律 m*≈n²/4 截断旋钮平方档。 *)
(* 构造性注记：全件 Qed，零 Axiom/Parameter、零承认、零 Abort、零经典  *)
(*   逻辑；见证语句面 sigT(nat)(fun q => Id ...) 与增长面 hl_le_t     *)
(*   皆 Set 承载（B1 件先例）；nat 层 Prop 面支撑引理仅作推理脚手架    *)
(*   （Ln2Escape/HansonLcm 先例）；非平凡：见证定理双参归纳＋奇偶分支  *)
(*   ＋等/不等分案，实质推导链；lia 仅辅助计算步（线性边料），主定理    *)
(*   结构为归纳+分案+显式见证；可提取：od_prod/oddlcm Fixpoint 可执行， *)
(*   Separate Extraction 零失名。                                    *)
(* 依赖：Stdlib Arith/Factorial/Lia＋HansonLcm＋S01_BaseRing（Id Set   *)
(*   承载·B1 件先例）。                                              *)
(* 编译配方：rocq c -native-compiler no -q -Q . "" abl_dmdnf2_oddlcm.v *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith Arith.Factorial Lia.
Require Import HansonLcm.
Require Import S01_BaseRing.

(* ============================================================ *)
(* §0 支撑脚手架：正奇数之奇性（计算+归纳，nat 层 Prop 面）              *)
(* ============================================================ *)

Lemma dnf2_odd_SS : forall n : nat, Nat.odd n = true ->
  Nat.odd (Datatypes.S (Datatypes.S n)) = true.
Proof.
  intros n H. exact H.  (* even 双步递归（Init/Nat.v: 0→true|1→false|S(S n')→even n'）: odd (S (S n)) ≡ negb (even n) ≡ odd n 定义等价 *)
Qed.

Lemma dnf2_odd_two_k1 : forall k : nat, Nat.odd (2 * k + 1) = true.
Proof.
  induction k as [| k IHk].
  - reflexivity.
  - replace (2 * Datatypes.S k + 1)%nat with (Datatypes.S (Datatypes.S (2 * k + 1))) by lia.
    apply dnf2_odd_SS. exact IHk.
Qed.

(* ============================================================ *)
(* §A 定义面：奇部双阶乘与奇部 lcm（可执行·透明）                     *)
(* ============================================================ *)

Fixpoint od_prod (N : nat) : nat :=
  match N with
  | Datatypes.O => 1
  | Datatypes.S N' => if Nat.odd (Datatypes.S N') then (Datatypes.S N') * od_prod N' else od_prod N'
  end.

Fixpoint oddlcm (N : nat) : nat :=
  match N with
  | Datatypes.O => 1
  | Datatypes.S N' => if Nat.odd (Datatypes.S N') then Nat.lcm (Datatypes.S N') (oddlcm N') else oddlcm N'
  end.

(* ============================================================ *)
(* §B 见证接口面（主定理）：奇数 2k+1 ≤ N 对 od_prod(N) 整除见证          *)
(*    ——DNF 缺口⑤刻消解形：截断段奇分母 2n+2m+1 ≤ 2n+2M+1 全清          *)
(* ============================================================ *)

Theorem dnf2_odd_div_odprod : forall (N k : nat), (2 * k + 1 <= N)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (od_prod N)).
Proof.
  induction N as [| N' IH]; intros k Hk.
  - lia.
  - cbn [od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + (* 奇档：S N' 入积 *)
      destruct (Nat.eq_dec (2 * k + 1) (Datatypes.S N')) as [Heq | Hne].
      * (* 2k+1 = S N'：见证 = od_prod N' *)
        exists (od_prod N').
        rewrite Heq. rewrite Nat.mul_comm. reflexivity.
      * (* 2k+1 ≠ S N' 且 ≤ S N' → ≤ N'：IH 逐层乘 S N' *)
        assert (Hle : (2 * k + 1 <= N')%nat) by lia.
        destruct (IH k Hle) as [q Hq].
        exists ((Datatypes.S N') * q)%nat.
        rewrite <- Nat.mul_assoc. rewrite Hq. apply id_refl.
    + (* 偶档：积不变；2k+1 = S N' 与偶性矛盾 *)
      destruct (Nat.eq_dec (2 * k + 1) (Datatypes.S N')) as [Heq | Hne].
      * rewrite <- Heq in E. rewrite (dnf2_odd_two_k1 k) in E. discriminate E.
      * apply IH. lia.
Qed.

(* 截断段直接使用面：n, M 双旋钮命名形（覆盖端 2n+2M+1） *)
Theorem dnf2_trunc_odd_clear : forall (n M k : nat), (2 * k + 1 <= 2 * n + 2 * M + 1)%nat ->
  sigT (fun q : nat => Id (q * (2 * k + 1)) (od_prod (2 * n + 2 * M + 1))).
Proof.
  intros n M k Hk.
  exact (dnf2_odd_div_odprod (2 * n + 2 * M + 1) k Hk).
Qed.

(* ============================================================ *)
(* §C 增长界面：oddlcm ≤ od_prod ≤ fact（Prop 脚手架 + Set 面 t 形）     *)
(* ============================================================ *)

Lemma dnf2_oddlcm_le_odprod : forall N : nat, oddlcm N <= od_prod N.
Proof.
  induction N as [| N' IH].
  - simpl. lia.
  - cbn [oddlcm od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + eapply Nat.le_trans.
      * apply hl_lcm_le_mul.
      * apply Nat.mul_le_mono_l. exact IH.
    + exact IH.
Qed.

Lemma dnf2_odprod_le_fact : forall N : nat, od_prod N <= fact N.
Proof.
  induction N as [| N' IH].
  - simpl. lia.
  - cbn [od_prod]. destruct (Nat.odd (Datatypes.S N')) eqn:E.
    + eapply Nat.le_trans.
      * apply Nat.mul_le_mono_l. exact IH.
      * cbn [fact]. lia.
    + eapply Nat.le_trans.
      * exact IH.
      * cbn [fact Nat.mul]. apply Nat.le_add_r.
Qed.

(* Set 面增长锚（hl_le_t 承载·QleT' 同构件） *)
Theorem dnf2_oddlcm_le_odprod_t : forall N : nat, hl_le_t (oddlcm N) (od_prod N).
Proof.
  intro N. exact (hl_le_to_le_t (oddlcm N) (od_prod N) (dnf2_oddlcm_le_odprod N)).
Qed.

Theorem dnf2_odprod_le_fact_t : forall N : nat, hl_le_t (od_prod N) (fact N).
Proof.
  intro N. exact (hl_le_to_le_t (od_prod N) (fact N) (dnf2_odprod_le_fact N)).
Qed.

(* ============================================================ *)
(* §D 执行锚（独立复算核对·可执行计算）                                    *)
(* ============================================================ *)

(* 大数档（N=23: odprod 316234143225 / oddlcm 334639305）一元 nat 不可计算，
   锚值由独立复算权威承载，Coq 侧不设 reflexivity 锚（诚实登记） *)
Lemma dnf2_anchor_odprod9 : Id (od_prod 9) 945.
Proof. reflexivity. Qed.

Lemma dnf2_anchor_oddlcm9 : Id (oddlcm 9) 315.
Proof. reflexivity. Qed.

Lemma dnf2_anchor_odprod11 : Id (od_prod 11) 10395.
Proof. reflexivity. Qed.

(* 截断段锚：n=1, M=4 → N=11 奇分母 11 的见证（独立复算 n=1 手工锚 887/6930 位） *)
Lemma dnf2_anchor_trunc11 :
  sigT (fun q : nat => Id (q * 11) (od_prod 11)).
Proof.
  exact (dnf2_odd_div_odprod 11 5 (le_n 11)).
Qed.

(* ============================================================ *)
(* §E 审计面                                                          *)
(* ============================================================ *)

Print Assumptions dnf2_odd_div_odprod.
Print Assumptions dnf2_trunc_odd_clear.
Print Assumptions dnf2_oddlcm_le_odprod_t.
Print Assumptions dnf2_odprod_le_fact_t.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log".
Separate Extraction oddlcm od_prod dnf2_trunc_odd_clear.
