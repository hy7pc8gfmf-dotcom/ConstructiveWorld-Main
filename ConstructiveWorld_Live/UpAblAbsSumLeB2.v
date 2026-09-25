(* ============================================================
   UpAblAbsSumLeB2 —— 使命行：abs_sum_le 族余项闭合件（同时性反例与抽象折叠）
(*                                                                *)
(* 使命：本件形式化两余项的构造性闭合： *)
(*   余项一＝全余量同时性反例——Q 层柯西证书：                            *)
(*     X_n := q0 + 1/(n+1)（Y:=real_zero，e:=real_const q0，0<q0）。     *)
(*     构造性给出六项：                                                 *)
(*     ① real_eq X (Y+e)——real_eq 定义的见证构造（与柯西证书同构：      *)
(*        阿基米德指标＋单位分数单调夹逼）；                            *)
(*     ② real_le X (Y+e)——经 eq 支 inr 注入（le 在场）；                *)
(*     ③ real_lt Y X——反向 strict 与②同时成立（共存反例本体）；          *)
(*     ④ real_lt X (Y+e) 被精确排除——全余量紧致：余量被 eq 支占满，      *)
(*        此见证下任何 le 证明必取 eq 支；                              *)
(*     ⑤ real_lt (Y+2e) X 被精确排除——与倍率 2 不可共存引理一致：        *)
(*        全余量见证下其前提不可达；                                    *)
(*     ⑥ ②与③的共存合取（And=集合积）＝同时性语句。                    *)
(*   余项二＝抽象折叠算子 sumL 的 B 形（list 折叠形的抽象接口版）：       *)
(*     |Σ sumL f| ≤_B Σ sumL|f|（cons 步逐点核应用                      *)
(*     real_abs_triangle_le_eps；加权沿用 uabS4_wlen 正性证书与         *)
(*     real_le_closure_b 闭合）；＋real_list_sum 实例（接口可满足性/    *)
(*     非空性）。SumOver 字段面到接口层 B 形的直接传输不可达，本件给出   *)
(*     折叠接口相对形（有限和折叠），接口假设本体保持原状。             *)
(* 依赖：CW_ConstructiveWorld_219、UpRealLeB、S08_RealMainlineDPO、      *)
(*   UpAblAbsSumLeB（uabS4_le_add_r/uabS4_wlen/uabS4_wlen_pos/          *)
(*   uabS4_cons_glue 直接应用）；stdlib List、QArith.Qring、Lia、Lqa。   *)
(* 对标：mathlib abs_sum_le_sum_abs（和的绝对值三角不等式）；本件为     *)
(*   Bishop 余量形 ≤_B 的构造性对应物。                                 *)
(* 构造性注记：全部语句 Set 层值（real_le/real_lt/real_eq/real_le_b/    *)
(*   QltT/And=集合积），语句面无裸命题；证明全构造（Or 逐支、sigT       *)
(*   见证直接构造）；单位分数 1/(n+1) 的非负/正性以显式 Z 序引理链      *)
(*   构造（正性见证 Pos2Z.pos_is_pos，不经一键算术自动战术）；全件      *)
(*   Qed 闭合，文尾 Print Assumptions 预期全 Closed。                   *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB.



(* ============================================================ *)
(* §0 库内接口核对（Check 逐项对照真实签名）                              *)
(* ============================================================ *)

Check real_lt.                    (* 类型为 sigT(eps, And(QltT, sigT(N,…)))：存在 eps 与 N 的逐 eps 界 *)
Check real_eq.                    (* 逐 eps 全称 *)
Check real_le.                    (* Or(lt, eq) 编码 *)
Check real_le_b.                  (* Bishop 形 ≤ *)
Check real_const_proj.            (* real_const 的逐点投影 *)
Check real_plus_proj.             (* real_plus 的逐点投影 *)
Check real_eq_of_zero_diff.       (* 由逐点差为零得 real_eq *)
Check QltT_to_Qlt. Check Qlt_to_QltT.
Check Qlt_alt. Check Qle_alt.
Check q_abs_lt_two_sided.         (* Q 层双侧绝对值不等式 *)
Check NatLe_lift. Check NatLe_drop. (* nat ≤ 与 NatLe 往返 *)
Check real_abs_triangle_le_eps.   (* 两点核逐 eps *)
Check real_le_closure_b.          (* 带加权正性证书 D 的 B 形闭合 *)
Check real_abs_zero_req.
Check real_list_sum.              (* list 折叠（X 全称） *)
Check uabS4_le_add_r. Check uabS4_wlen. Check uabS4_wlen_pos. Check uabS4_cons_glue.
Check real_eq_refl. Check real_eq_sym. Check real_mult_comm. Check real_mult_one.
Check RealSetoid.real_le_id_l. Check RealSetoid.real_le_id_r.
Check RealSetoid.real_eq_le. Check RealSetoid.real_eq_abs_compat.

(* ============================================================ *)
(* §1 余项一：Q 层柯西证书＋全余量同时性反例                               *)
(* ============================================================ *)

(* A.0 单位分数族 1/(n+1)：Q 层非负性＋单调性＋阿基米德性质（柯西证书核心） *)
Lemma uabS4b_null_nonneg : forall n : nat, Qle 0 (1#(Pos.of_succ_nat n)).
Proof.
  intros n. unfold Qle. cbn [Qnum Qden].
  (* Z 层化：Qle 展开为 (0 * Z.pos (Pos.of_succ_nat n) <= 1 * 1)%Z，     *)
  (* 两乘积显式归约后由 Z.lt_le_incl+Pos2Z.pos_is_pos 取正性见证        *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Z.lt_le_incl. apply Pos2Z.pos_is_pos.
Qed.

(* 正指标 Z 桥接（归纳）：Pos.of_succ_nat 的单调性与加一恒等式。
   （注：本库环境中 zify 对 Z.of_nat (Nat.succ n) 不适用，故走
   显式归纳＋Nat2Z/Pos2Z 桥接，不依赖该路径。） *)
Lemma uabS4b_pos_le : forall m k : nat, (k <= m)%nat ->
  Z.le (Z.pos (Pos.of_succ_nat k)) (Z.pos (Pos.of_succ_nat m)).
Proof.
  intros m k Hk. induction Hk as [| m' Hkm IH].
  - apply Z.le_refl.
  - cbn [Pos.of_succ_nat].
    rewrite Pos2Z.inj_succ.
    apply Z.le_trans with (Z.pos (Pos.of_succ_nat m')).
    + exact IH.
    + apply Z.le_succ_diag_r.
Qed.

Lemma uabS4b_pos_succ_Z : forall N : nat,
  Z.pos (Pos.of_succ_nat N) = (Z.of_nat N + 1)%Z.
Proof.
  intros N. rewrite Z.add_1_r. rewrite <- Znat.Nat2Z.inj_succ. reflexivity.
Qed.

Lemma uabS4b_null_pos : forall n : nat, Qlt 0 (1#(Pos.of_succ_nat n)).
Proof.
  intros n. unfold Qlt. cbn [Qnum Qden].
  (* Z 层化：Qlt 展开为 (0 * Z.pos (Pos.of_succ_nat n) < 1 * 1)%Z，      *)
  (* 两乘积显式归约后由正性见证 Pos2Z.pos_is_pos 直接闭合               *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Pos2Z.pos_is_pos.
Qed.

Lemma uabS4b_null_mono : forall m k : nat, (k <= m)%nat ->
  Qle (1#(Pos.of_succ_nat m)) (1#(Pos.of_succ_nat k)).
Proof.
  intros m k Hk. unfold Qle. simpl.
  exact (uabS4b_pos_le m k Hk).
Qed.

(* 阿基米德指标：N(q) := Z.to_nat(Qnum q)+Z.to_nat(QDen q)，使 1/(N+1) < q *)
Definition uabS4b_arch_N (q : Q) : nat :=
  Z.to_nat (Qnum q) + Z.to_nat (QDen q).

Lemma uabS4b_null_lt : forall q : Q, QltT 0 q ->
  QltT (1#(Pos.of_succ_nat (uabS4b_arch_N q))) q.
Proof.
  intros q Hq. apply Qlt_to_QltT. unfold Qlt. simpl.
  assert (Hz : (0 < Qnum q)%Z).
  { pose proof (QltT_to_Qlt 0 q Hq) as Hq0. unfold Qlt in Hq0. simpl in Hq0. lia. }
  assert (Hz0 : (0 <= Qnum q)%Z) by lia.
  assert (Hd0 : (0 <= QDen q)%Z) by (apply Z.lt_le_incl, Pos2Z.is_pos).
  assert (Harch : Z.of_nat (uabS4b_arch_N q)
                  = (Qnum q + QDen q)%Z).
  { unfold uabS4b_arch_N.
    rewrite Znat.Nat2Z.inj_add.
    rewrite (Znat.Z2Nat.id (Qnum q) Hz0).
    rewrite (Znat.Z2Nat.id (QDen q) Hd0).
    reflexivity. }
  rewrite uabS4b_pos_succ_Z.
  assert (H1 : (1 * (Z.of_nat (uabS4b_arch_N q) + 1)
                <= Qnum q * (Z.of_nat (uabS4b_arch_N q) + 1))%Z)
    by (apply Z.mul_le_mono_nonneg_r; [lia | lia]).
  assert (H2 : (QDen q < 1 * (Z.of_nat (uabS4b_arch_N q) + 1))%Z)
    by (rewrite Harch; lia).
  lia.
Qed.

(* A.1 反例实数 X：X_n := q0 + 1/(n+1)，柯西证书直接构造（存在 N 后逐点夹逼） *)
Definition uabS4b_Xseq (q0 : Q) : nat -> Q :=
  fun n => (q0 + (1#(Pos.of_succ_nat n)))%Q.

Lemma uabS4b_X_cauchy : forall q0 : Q, cauchy (uabS4b_Xseq q0).
Proof.
  intros q0 eps Heps.
  assert (Hc : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply uabS4b_null_lt; exact Heps).
  assert (Hcp : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply QltT_to_Qlt; exact Hc).
  exists (uabS4b_arch_N eps).
  intros m n Hm Hn.
  assert (Hm' : (uabS4b_arch_N eps <= m)%nat) by (apply NatLe_drop; exact Hm).
  assert (Hn' : (uabS4b_arch_N eps <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat m)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hm').
  assert (Hn1 : Qle (1#(Pos.of_succ_nat n)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hn').
  assert (Hm0 : Qle 0 (1#(Pos.of_succ_nat m))) by apply uabS4b_null_nonneg.
  assert (Hn0 : Qle 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_nonneg.
  apply Qlt_to_QltT.
  unfold uabS4b_Xseq.
  apply (q_abs_lt_two_sided _ eps (QltT_to_Qlt 0 eps Heps)).
  - lra.
  - lra.
Qed.

Definition uabS4b_X (q0 : Q) : Real :=
  existT _ (uabS4b_Xseq q0) (uabS4b_X_cauchy q0).

Lemma uabS4b_X_proj : forall (q0 : Q) (n : nat),
  projT1 (uabS4b_X q0) n == uabS4b_Xseq q0 n.
Proof. intros q0 n. reflexivity. Qed.

(* Y+e 逐点值（0+q0；重写桥接用 Qeq_refl 收束，不依赖环判） *)
Lemma uabS4b_Ye_proj : forall (q0 : Q) (n : nat),
  projT1 (real_plus real_zero (real_const q0)) n == (0 + q0)%Q.
Proof.
  intros q0 n.
  assert (Hp : projT1 (real_plus real_zero (real_const q0)) n
               == projT1 real_zero n + projT1 (real_const q0) n)
    by apply real_plus_proj.
  rewrite Hp.
  assert (Hz : projT1 real_zero n == 0) by apply Qeq_refl.
  rewrite Hz.
  rewrite (real_const_proj q0 n).
  apply Qeq_refl.
Qed.

(* A.2 ① eq 支真相等在场：real_eq X (Y+e)——X 与 Y+e 非逐点相等
   （差 1/(n+1) → 0），故走 real_eq 定义的见证构造（与 A.1 柯西证书
   同构：阿基米德指标＋单位分数单调夹逼），非 real_eq_of_zero_diff。 *)
Theorem uabS4b_full_margin_eq : forall q0 : Q, QltT 0 q0 ->
  real_eq (uabS4b_X q0) (real_plus real_zero (real_const q0)).
Proof.
  intros q0 Hq0. unfold real_eq. intros eps Heps.
  assert (Hc : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply uabS4b_null_lt; exact Heps).
  assert (Hcp : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N eps))) eps)
    by (apply QltT_to_Qlt; exact Hc).
  exists (uabS4b_arch_N eps). intros n Hn.
  assert (Hn' : (uabS4b_arch_N eps <= n)%nat) by (apply NatLe_drop; exact Hn).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat n)) (1#(Pos.of_succ_nat (uabS4b_arch_N eps))))
    by (apply uabS4b_null_mono; exact Hn').
  assert (Hm0 : Qle 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_nonneg.
  apply Qlt_to_QltT.
  rewrite (uabS4b_X_proj q0 n). rewrite (uabS4b_Ye_proj q0 n).
  unfold uabS4b_Xseq.
  apply (q_abs_lt_two_sided _ eps (QltT_to_Qlt 0 eps Heps)).
  - lra.
  - lra.
Qed.

(* A.3 ② le 在场（eq 支 inr 注入）：real_le X (Y+e) *)
Theorem uabS4b_full_margin_le : forall q0 : Q, QltT 0 q0 ->
  real_le (uabS4b_X q0) (real_plus real_zero (real_const q0)).
Proof.
  intros q0 Hq0. unfold real_le. apply inr.
  apply uabS4b_full_margin_eq. exact Hq0.
Qed.

(* A.4 ③ 反向 strict 在场：real_lt real_zero X（见证 eps:=q0，N:=0） *)
Theorem uabS4b_full_margin_rev_lt : forall q0 : Q, QltT 0 q0 ->
  real_lt real_zero (uabS4b_X q0).
Proof.
  intros q0 Hq0. unfold real_lt.
  exists q0. split.
  - exact Hq0.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    assert (Hz : projT1 real_zero n == 0) by apply Qeq_refl.
    rewrite Hz. rewrite (uabS4b_X_proj q0 n). unfold uabS4b_Xseq.
    assert (Hp : Qlt 0 (1#(Pos.of_succ_nat n))) by apply uabS4b_null_pos.
    lra.
Qed.

(* A.5 ④ 全余量紧致：real_lt X (Y+e) 被精确排除
   （余量被 eq 支占满——本见证下 le 的证明必取 eq 支，lt 支不可用） *)
Theorem uabS4b_full_margin_tight : forall q0 : Q, QltT 0 q0 ->
  real_lt (uabS4b_X q0) (real_plus real_zero (real_const q0)) -> Empty_set.
Proof.
  intros q0 Hq0 Hlt. unfold real_lt in Hlt.
  destruct Hlt as [eps Hpair]. destruct Hpair as [Hpos Hbound].
  destruct Hbound as [N Hall].
  exfalso.
  assert (Hle : (N <= N + uabS4b_arch_N q0)%nat) by lia.
  assert (HN : NatLe N (N + uabS4b_arch_N q0)%nat) by (apply NatLe_lift; exact Hle).
  assert (Hk : Qlt eps (projT1 (real_plus real_zero (real_const q0)) (N + uabS4b_arch_N q0)%nat
                        - projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat))
    by (apply QltT_to_Qlt; exact (Hall (N + uabS4b_arch_N q0)%nat HN)).
  assert (HV1 : projT1 (real_plus real_zero (real_const q0)) (N + uabS4b_arch_N q0)%nat
                == (0 + q0)%Q).
  { rewrite real_plus_proj.
    assert (Hz : projT1 real_zero (N + uabS4b_arch_N q0)%nat == 0) by apply Qeq_refl.
    rewrite Hz. rewrite (real_const_proj q0 (N + uabS4b_arch_N q0)%nat).
    apply Qeq_refl. }
  assert (HV2 : projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                == (q0 + (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))%Q)
    by exact (uabS4b_X_proj q0 (N + uabS4b_arch_N q0)%nat).
  assert (Hepos : Qlt 0 eps) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hn0 : Qle 0 (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))
    by apply uabS4b_null_nonneg.
  lra.
Qed.

(* A.6 ⑤ 倍率 2 前提不可达：real_lt (Y+2e) X 被精确排除
   （与 uabS4_lt_double_margin_le_half_contr（倍率 2 不可共存引理）一致：全余量见证下乘 2 余量越界） *)
Theorem uabS4b_full_margin_no_far : forall q0 : Q, QltT 0 q0 ->
  real_lt (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
          (uabS4b_X q0) -> Empty_set.
Proof.
  intros q0 Hq0 Hlt. unfold real_lt in Hlt.
  destruct Hlt as [eps Hpair]. destruct Hpair as [Hpos Hbound].
  destruct Hbound as [N Hall].
  exfalso.
  assert (Hnull : QltT (1#(Pos.of_succ_nat (uabS4b_arch_N q0))) q0)
    by (apply uabS4b_null_lt; exact Hq0).
  assert (Hle : (N <= N + uabS4b_arch_N q0)%nat) by lia.
  assert (HN : NatLe N (N + uabS4b_arch_N q0)%nat) by (apply NatLe_lift; exact Hle).
  assert (Hk : Qlt eps (projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                        - projT1 (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
                                  (N + uabS4b_arch_N q0)%nat))
    by (apply QltT_to_Qlt; exact (Hall (N + uabS4b_arch_N q0)%nat HN)).
  assert (HV1 : projT1 (uabS4b_X q0) (N + uabS4b_arch_N q0)%nat
                == (q0 + (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat)))%Q)
    by exact (uabS4b_X_proj q0 (N + uabS4b_arch_N q0)%nat).
  assert (HV2 : projT1 (real_plus real_zero (real_plus (real_const q0) (real_const q0)))
                       (N + uabS4b_arch_N q0)%nat
                == (0 + (q0 + q0))%Q).
  { rewrite real_plus_proj.
    assert (Hz : projT1 real_zero (N + uabS4b_arch_N q0)%nat == 0) by apply Qeq_refl.
    rewrite Hz.
    assert (Hp2 : projT1 (real_plus (real_const q0) (real_const q0))
                         (N + uabS4b_arch_N q0)%nat
                  == (q0 + q0)%Q).
    { rewrite real_plus_proj.
      rewrite (real_const_proj q0 (N + uabS4b_arch_N q0)%nat).
      apply Qeq_refl. }
    rewrite Hp2. apply Qeq_refl. }
  assert (Hepos : Qlt 0 eps) by (apply QltT_to_Qlt; exact Hpos).
  assert (Hm1 : Qle (1#(Pos.of_succ_nat (N + uabS4b_arch_N q0)%nat))
                    (1#(Pos.of_succ_nat (uabS4b_arch_N q0))))
    by (apply uabS4b_null_mono; lia).
  assert (Hnl : Qlt (1#(Pos.of_succ_nat (uabS4b_arch_N q0))) q0)
    by (apply QltT_to_Qlt; exact Hnull).
  lra.
Qed.

(* A.7 ⑥ 同时性语句：le（eq 支）与反向 strict 的共存合取
   （And=集合积，Set 层）——全余量同时性反例的构造性收束。 *)
Theorem uabS4b_full_margin_coexist : forall q0 : Q, QltT 0 q0 ->
  And (real_le (uabS4b_X q0) (real_plus real_zero (real_const q0)))
      (real_lt real_zero (uabS4b_X q0)).
Proof.
  intros q0 Hq0. split.
  - apply uabS4b_full_margin_le. exact Hq0.
  - apply uabS4b_full_margin_rev_lt. exact Hq0.
Qed.

(* ============================================================ *)
(* §2 余项二：抽象折叠算子 sumL 的 B 形（折叠接口相对形）                   *)
(* ============================================================ *)

Section AbstractSumSlot.

(* 抽象折叠算子：sumL 仅被要求尊重 nil/cons 两条 real_eq 接口方程
   （接口假设相对形如实陈述——Closed 约定指零公理而非零前提：
   本文件全件 Closed，以下两条为显式量化的相对前提）。 *)
Variable X : Type.
Variable sumL : (X -> Real) -> list X -> Real.
Variable sumL_nil_eq : forall f : X -> Real, real_eq (sumL f nil) real_zero.
Variable sumL_cons_eq : forall (f : X -> Real) (w : X) (rest : list X),
  real_eq (sumL f (w :: rest)) (real_plus (f w) (sumL f rest)).

(* B.1 加权归纳主体（逐 eps 形）：|Σ sumL f| ≤ Σ sumL|f| + W(l)·e。
   情形 l=[]：接口方程双向运输得 |0| ≡ 0 后正余量右吸收；
   归纳步 l 到 w::rest：两点核三角以整单位 e 引入＋尾段由归纳假设同权承担＋uabS4_cons_glue 合成，接口方程双向运输。 *)
Lemma uabS4b_slot_abs_sum_le_wt : forall (f : X -> Real) (l : list X) (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (sumL f l))
          (real_plus (sumL (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros f l. induction l as [| w rest IH]; intros e He.
  - (* 情形 l=[]：接口方程双向运输得 |0| ≤ 0 ≤ 0 + 1·e *)
    apply (uabS4_le_add_r (real_abs (sumL f nil))
             (sumL (fun x => real_abs (f x)) nil)
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs (sumL f nil)) (real_abs real_zero)
               (sumL (fun x => real_abs (f x)) nil)
               (RealSetoid.real_eq_abs_compat (sumL f nil) real_zero
                  (sumL_nil_eq f))).
      apply (RealSetoid.real_le_id_r (real_abs real_zero) real_zero
               (sumL (fun x => real_abs (f x)) nil)).
      * apply real_eq_sym.
        exact (sumL_nil_eq (fun x => real_abs (f x))).
      * apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero
                 real_abs_zero_req).
        exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - (* 归纳步 l 到 w::rest：eq 运输左端＋右端合成 *)
    apply (RealSetoid.real_le_id_l (real_abs (sumL f (w :: rest)))
             (real_abs (real_plus (f w) (sumL f rest)))
             (real_plus (sumL (fun x => real_abs (f x)) (w :: rest))
                        (real_mult (uabS4_wlen X (w :: rest)) e))
             (RealSetoid.real_eq_abs_compat _ _ (sumL_cons_eq f w rest))).
    apply (RealSetoid.real_le_id_r
             (real_abs (real_plus (f w) (sumL f rest)))
             (real_plus (real_plus (real_abs (f w))
                        (sumL (fun x => real_abs (f x)) rest))
                        (real_mult (real_plus (uabS4_wlen X rest) real_one) e))
             (real_plus (sumL (fun x => real_abs (f x)) (w :: rest))
                        (real_mult (uabS4_wlen X (w :: rest)) e))).
    + (* 右端 eq：sumL|f|(w::rest) ≡ |f w| + sumL|f| rest（接口方程） *)
      apply (RealSetoid.real_eq_plus_compat _ _ _ _).
      * apply real_eq_sym.
        exact (sumL_cons_eq (fun x => real_abs (f x)) w rest).
      * apply real_eq_refl.
    + (* 折叠一步：两点核三角整单位＋尾加权＝uabS4_cons_glue 直接应用 *)
      exact (uabS4_cons_glue (f w) (sumL f rest)
               (sumL (fun x => real_abs (f x)) rest) (uabS4_wlen X rest) e He
               (real_abs_triangle_le_eps (f w) (sumL f rest) e He) (IH e He)).
Qed.

(* B.2 B 形闭合（抽象折叠算子的 B 形）：|Σ sumL f| ≤_B Σ sumL|f|。
   real_le_closure_b 以 D := W(l) 显式正性证书闭合加权族。 *)
Theorem uabS4b_slot_abs_sum_le_B : forall (f : X -> Real) (l : list X),
  real_le_b (real_abs (sumL f l)) (sumL (fun x => real_abs (f x)) l).
Proof.
  intros f l.
  apply (real_le_closure_b _ _ (uabS4_wlen X l) (uabS4_wlen_pos X l)).
  intros e He. apply uabS4b_slot_abs_sum_le_wt. exact He.
Qed.

End AbstractSumSlot.

(* B.3 接口可满足性实例（非空性）：real_list_sum 逐条满足接口方程
   （nil/cons 皆定义性等式，由 real_eq_refl 直接给出）。 *)
Theorem uabS4b_slot_instance_list_nil : forall (X : Type) (f : X -> Real),
  real_eq (real_list_sum X f nil) real_zero.
Proof. intros X f. exact (real_eq_refl (real_list_sum X f nil)). Qed.

Theorem uabS4b_slot_instance_list_cons : forall (X : Type) (f : X -> Real)
                                                (w : X) (rest : list X),
  real_eq (real_list_sum X f (w :: rest))
          (real_plus (f w) (real_list_sum X f rest)).
Proof.
  intros X f w rest.
  exact (real_eq_refl (real_list_sum X f (w :: rest))).
Qed.

(* B.4 对照：抽象折叠算子的 B 形以 real_list_sum 实例化＝uabS4_abs_list_sum_le_B 同语句
   （list 折叠形＝抽象接口版的具象实例）。 *)
Theorem uabS4b_slot_list_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (uabS4b_slot_abs_sum_le_B X (real_list_sum X)
           (uabS4b_slot_instance_list_nil X) (uabS4b_slot_instance_list_cons X)
           f l).
Qed.

(* ============================================================ *)
(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设）             *)
(* ============================================================ *)

Print Assumptions uabS4b_null_lt.
Print Assumptions uabS4b_X_cauchy.
Print Assumptions uabS4b_full_margin_eq.
Print Assumptions uabS4b_full_margin_le.
Print Assumptions uabS4b_full_margin_rev_lt.
Print Assumptions uabS4b_full_margin_tight.
Print Assumptions uabS4b_full_margin_no_far.
Print Assumptions uabS4b_full_margin_coexist.
Print Assumptions uabS4b_slot_abs_sum_le_B.
Print Assumptions uabS4b_slot_list_le_B.
