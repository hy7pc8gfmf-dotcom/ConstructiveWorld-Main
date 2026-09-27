(* ==========================================================================)
   UpReqPadeConstUnify.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：cpf_qlt_eq_l、cpf_qlt_eq_r、cpf_qeq_qlt、cpf_qlt_add_r、cpf_qle_lt_add、cpf_qlt_le_add、cpf_pmix、cpf_sub_r0、cpf_qlt0_neq0。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
Require Import UpReqPadeExp.
Require Import UpReqPadeLower.
Require Import UpReqPadeQLeg.
Require Import UpReqPadeBetaPos.
Require Import UpReqPadeTailPos.
From Stdlib Require Import Extraction.

(* ================= §1 cpf_qlt_eq_l 族 ================= *)
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

Section CpfFinale.

(* ===== §0 Q 层连接引理（AA12 腿化：一跳 UpReqPadeQLeg 自建单调腿） ===== *)

(* Qeq 穿透墙桥：== 不可 rewrite 进 Qlt/QltT 目标（CS 卡），
   AA12 实测：四元合证曾 nia 拒拆两步组合；现双腿直达，零 nia。 *)
Lemma cpf_qlt_eq_l : forall a b c : Q, a == b -> Qlt a c -> Qlt b c.
Proof.
  intros a b c Hab Hlt.
  exact (pql_qlt_eq_l a b c Hab Hlt).
Qed.

Lemma cpf_qlt_eq_r : forall a b c : Q, a == b -> Qlt c a -> Qlt c b.
Proof.
  intros a b c Hab Hlt.
  exact (pql_qlt_eq_r a b c Hab Hlt).
Qed.

Lemma cpf_qeq_qlt : forall a b c d : Q,
  a == b -> c == d -> Qlt a c -> Qlt b d.
Proof.
  intros a b c d Hab Hcd Hlt.
  apply (cpf_qlt_eq_r c d _ Hcd). apply (cpf_qlt_eq_l a b c Hab Hlt).
Qed.

(* 三元算术小桥（AA12 腿化：一跳族 B 加法腿） *)
Lemma cpf_qlt_add_r : forall a b : Q, Qlt 0 b -> Qlt a (a + b)%Q.
Proof.
  intros a b Hb. exact (pql_qlt_add_r a b Hb).
Qed.

Lemma cpf_qle_lt_add : forall a b : Q, Qle 0 a -> Qlt 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb. exact (pql_qle_lt_add a b Ha Hb).
Qed.

Lemma cpf_qlt_le_add : forall a b : Q, Qlt 0 a -> Qle 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb. exact (pql_qlt_le_add a b Ha Hb).
Qed.

(* 减法形状桥（Qminus 展开形 ring 完成，DTPT-U17 卡同款） *)
Lemma cpf_pmix : forall A B : Q, (A - B + B)%Q == A.
Proof. intros A B. unfold Qminus. ring. Qed.

Lemma cpf_sub_r0 : forall A : Q, (A - 0)%Q == A.
Proof. intros A. unfold Qminus. ring. Qed.

Lemma cpf_qlt0_neq0 : forall q : Q, Qlt 0 q -> ~ q == 0.
Proof.
  intros q Hq Heq. apply (Qlt_not_eq 0 q Hq). exact (Qeq_sym q 0 Heq).
Qed.

(* 倒数消去（stdlib 9.0 无 Qmult_invl；Qmult_inv_r 特化形带 neq 前提，
   DTPT2 卡「消去形须自建」同款；assoc 走 transitivity 避 rewrite 方向歧义） *)
Lemma cpf_canc : forall A q : Q, Qlt 0 q -> (A * q) * (/ q) == A.
Proof.
  intros A q Hq. transitivity (A * (q * (/ q)))%Q.
  - apply (Qeq_sym _ _ (Qmult_assoc A q (/ q))).
  - setoid_rewrite (Qmult_inv_r q (cpf_qlt0_neq0 q Hq)).
    apply Qmult_1_r.
Qed.

(* ===== §1 保底件一：Q₂ 的完全平方构造性正性（对一切 x） ===== *)

(* q² ≥ 0 构造见证：destruct Q 全构造子 + Z 层逐支 lia *)
Lemma cpf_q_sq_nonneg : forall a : Q, Qle 0 (a * a)%Q.
Proof.
  intro a. destruct a as [n d]. unfold Qle, Qmult. simpl.
  destruct n; simpl; try lia.
Qed.

(* 完全平方核：(x−3)² + 3 ≥ 3 > 0 *)
Lemma cpf_sq3_pos : forall x : Q, Qlt 0 ((x + -3) * (x + -3) + 3)%Q.
Proof.
  intro x. apply cpf_qle_lt_add.
  - apply cpf_q_sq_nonneg.
  - unfold Qlt. simpl. lia.
Qed.

(* n=2 系数标记（vm_compute 闭式；字面点无 Nat.sub 截断坑） *)
Lemma cpf_c20 : pade_coeff 2 0%nat == 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma cpf_c21 : pade_coeff 2 1%nat == (1#2)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma cpf_c22 : pade_coeff 2 2%nat == (1#12)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 配方展开：Q₂(x) == ((x−3)²+3)/12（乘法形承载除法，Qdiv 不进 ring） *)
Lemma cpf_den2_complete_sq : forall x : Q,
  pade_den 2 x == ((x + -3) * (x + -3) + 3)%Q * (1#12)%Q.
Proof.
  intro x. unfold pade_den, sum_upto. simpl.
  rewrite cpf_c20, cpf_c21, cpf_c22. ring.
Qed.

(* 保底件一（主面）：Q₂(x) > 0 对一切 x——n=2 层段切割整体消失 *)
Theorem cpf_den2_pos_all : forall x : Q, QltT 0 (pade_den 2 x).
Proof.
  intro x. apply Qlt_to_QltT.
  apply (cpf_qeq_qlt 0%Q 0%Q _ _ (Qeq_refl 0%Q)
           (Qeq_sym _ _ (cpf_den2_complete_sq x))).
  apply Qmult_lt_0_compat.
  - apply cpf_sq3_pos.
  - unfold Qlt. simpl. lia.
Qed.

(* ===== §2 保底件二：P₂ 正性（x>0，系数全正见证） ===== *)

Lemma cpf_num2_expl : forall x : Q,
  pade_num 2 x == (1 + (1#2)%Q * x + (1#12)%Q * (x * x))%Q.
Proof.
  intro x. unfold pade_num, sum_upto. simpl.
  rewrite cpf_c20, cpf_c21, cpf_c22. ring.
Qed.

Theorem cpf_num2_pos : forall x : Q, QltT 0 x -> QltT 0 (pade_num 2 x).
Proof.
  intros x Hx. apply Qlt_to_QltT.
  apply (cpf_qeq_qlt 0%Q 0%Q _ _ (Qeq_refl 0%Q)
           (Qeq_sym _ _ (cpf_num2_expl x))).
  (* 0 < (1 + x/2) + x²/12：首段严格、尾段非负，两步合流 *)
  apply cpf_qlt_le_add.
  - apply cpf_qle_lt_add.
    + unfold Qle. simpl. lia.
    + apply Qmult_lt_0_compat.
      * unfold Qlt. simpl. lia.
      * apply QltT_to_Qlt. exact Hx.
  - apply Qmult_le_0_compat.
    + unfold Qle. simpl. lia.
    + apply cpf_q_sq_nonneg.
Qed.

(* ===== §3 幂正性与见证定义 ===== *)

Lemma cpf_q_pow_pos : forall (k : nat) (x : Q), Qlt 0 x -> Qlt 0 (q_pow x k).
Proof.
  intros k x Hx. induction k as [| m IH]; simpl.
  - unfold Qlt. simpl. lia.
  - apply Qmult_lt_0_compat; assumption.
Qed.

(* 正尾首项见证：w := x⁵/720 = x⁵·(1#720)（乘法形） *)
Definition cpf_witness_n2 (x : Q) : Q := q_pow x 5%nat * (1#720)%Q.

Lemma cpf_witness_pos : forall x : Q, QltT 0 x -> QltT 0 (cpf_witness_n2 x).
Proof.
  intros x Hx. apply Qlt_to_QltT. unfold cpf_witness_n2.
  apply Qmult_lt_0_compat.
  - apply (cpf_q_pow_pos 5%nat). apply QltT_to_Qlt. exact Hx.
  - unfold Qlt. simpl. lia.
Qed.

(* ===== §4 免除法传送引理（保底件三，real_lt sigT 见证组合形） ===== *)

(* Real 层减法 = plus + opp 组合形（S02 无 real_minus 原语；
   工单 §1.3 real_minus 面以本组合形承载，落盘件若异形走 wd 换桥） *)
Definition cpf_rminus (a b : Real) : Real := real_plus a (real_opp b).

Lemma cpf_rminus_proj : forall (a b : Real) (n : nat),
  projT1 (cpf_rminus a b) n == projT1 a n - projT1 b n.
Proof.
  intros a b n. unfold cpf_rminus.
  rewrite (real_plus_proj a (real_opp b) n), (real_opp_proj b n).
  reflexivity.
Qed.

Lemma cpf_real_zero_proj : forall n : nat, projT1 real_zero n == 0%Q.
Proof. reflexivity. Qed.

(* 常值正 ⟹ 0 < 常值 Real（见证 eps := c·½；eps<c 由 c>0 供） *)
Lemma cpf_const_pos_lt : forall c : Q, QltT 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc. assert (Hc' : Qlt 0 c) by (apply QltT_to_Qlt; exact Hc).
  unfold real_lt. exists (c * (1#2))%Q. split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + exact Hc'.
    + unfold Qlt. simpl. lia.
  - exists O%nat. intros n _.
    assert (Hd : projT1 (real_const c) n - projT1 real_zero n == c).
    { rewrite (real_const_proj c n), (cpf_real_zero_proj n). apply cpf_sub_r0. }
    apply Qlt_to_QltT.
    apply (cpf_qeq_qlt (c * (1#2))%Q (c * (1#2))%Q c
             (projT1 (real_const c) n - projT1 real_zero n)%Q
             (Qeq_refl _) (Qeq_sym _ _ Hd)).
    (* c·½ < c：换序桥 + Qmult_lt_compat_r（右因子 c 前置对齐 1*c） *)
    apply (cpf_qeq_qlt ((1#2)%Q * c)%Q (c * (1#2))%Q (1 * c)%Q c
             (Qmult_comm (1#2)%Q c) (Qmult_1_l c)).
    apply Qmult_lt_compat_r.
    + exact Hc'.
    + unfold Qlt. simpl. lia.
Qed.

(* 免除法传送：e·Q > P > 0 ∧ Q > 0 ⟹ e > 0（纯乘法消去，无 Real 除法）
   见证组合：eps := (eps₁+eps₂)·(1/Q)，N := max N₁ N₂，
   逐点 Q 链 eps₁<e·Q−P、eps₂<P 经 Qplus_lt_compat 合流 + 倒数消去。 *)
Theorem cpf_transport_no_div : forall (e P : Real) (q : Q),
  QltT 0 q ->
  real_lt P (real_mult e (real_const q)) ->
  real_lt real_zero P ->
  real_lt real_zero e.
Proof.
  intros e P q Hq Hlt1 Hlt2.
  destruct Hlt1 as [eps1 [Heps1 [N1 HN1]]].
  destruct Hlt2 as [eps2 [Heps2 [N2 HN2]]].
  assert (Hq' : Qlt 0 q) by (apply QltT_to_Qlt; exact Hq).
  assert (Hsum : Qlt 0 (eps1 + eps2)%Q).
  { apply (cpf_qeq_qlt (0 + 0)%Q 0%Q _ _ (Qplus_0_l 0%Q) (Qeq_refl _)).
    apply Qplus_lt_compat; apply QltT_to_Qlt; assumption. }
  exists ((eps1 + eps2) * (/ q))%Q. split.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + exact Hsum.
    + apply Qinv_lt_0_compat. exact Hq'.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Hn1 : NatLe N1 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
      - apply Nat.le_max_l.
      - apply NatLe_drop. exact Hn. }
    assert (Hn2 : NatLe N2 n).
    { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
      - apply Nat.le_max_r.
      - apply NatLe_drop. exact Hn. }
    assert (HM1 : projT1 (real_mult e (real_const q)) n - projT1 P n
                  == projT1 e n * q - projT1 P n).
    { rewrite (real_mult_proj e (real_const q) n), (real_const_proj q n).
      reflexivity. }
    assert (HPd : projT1 P n - projT1 real_zero n == projT1 P n).
    { rewrite (cpf_real_zero_proj n). apply cpf_sub_r0. }
    assert (HA1 : Qlt eps1 (projT1 e n * q - projT1 P n)%Q).
    { apply (cpf_qeq_qlt eps1 eps1 _ _ (Qeq_refl eps1) HM1).
      apply QltT_to_Qlt. exact (HN1 n Hn1). }
    assert (HA2 : Qlt eps2 (projT1 P n)%Q).
    { apply (cpf_qeq_qlt eps2 eps2 _ _ (Qeq_refl eps2) HPd).
      apply QltT_to_Qlt. exact (HN2 n Hn2). }
    assert (HA3 : Qlt (eps1 + eps2)%Q (projT1 e n * q)%Q).
    { apply (cpf_qeq_qlt _ _ _ _ (Qeq_refl _)
               (cpf_pmix (projT1 e n * q) (projT1 P n))).
      apply Qplus_lt_compat; [exact HA1 | exact HA2]. }
    assert (HA4 : Qlt ((eps1 + eps2) * (/ q)) (projT1 e n)%Q).
    { apply (cpf_qeq_qlt _ _ _ _ (Qeq_refl _) (cpf_canc (projT1 e n) q Hq')).
      apply Qmult_lt_compat_r.
      - apply Qinv_lt_0_compat. exact Hq'.
      - exact HA3. }
    assert (Hd : projT1 e n - projT1 real_zero n == projT1 e n).
    { rewrite (cpf_real_zero_proj n). apply cpf_sub_r0. }
    apply Qlt_to_QltT.
    apply (cpf_qeq_qlt _ _ _ _ (Qeq_refl _) (Qeq_sym _ _ Hd)).
    exact HA4.
Qed.

(* ===== §5 主件（闸门候③）：定量主定理组合形 ===== *)

(* 主件：x>0 的下界接口（显式参数，候③——UpReqPadeLower 落盘后以
   cpl_lower_even (k:=1) 实例化消去）⟹ P₂ < eˣ·Q₂（乘法形承载
   「eˣ ≥ P₂/Q₂ 且误差 ≥ x⁵/(720·Q₂)」：两侧同除正 Q₂ 即得，
   见证间隙 = x⁵/720）。 *)
Theorem cpf_exp_pos_pade2 : forall x : Q,
  QltT 0 x ->
  real_lt (real_const (cpf_witness_n2 x))
          (cpf_rminus (real_mult (cauchy_real_exp (real_const x))
                                 (real_const (pade_den 2 x)))
                      (real_const (pade_num 2 x))) ->
  real_lt (real_const (pade_num 2 x))
          (real_mult (cauchy_real_exp (real_const x))
                     (real_const (pade_den 2 x))).
Proof.
  intros x Hx Hlow. destruct Hlow as [eps [Heps [N HN]]].
  assert (Heps' : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  exists (cpf_witness_n2 x). split.
  - apply cpf_witness_pos. exact Hx.
  - exists N. intros n Hn.
    (* 接口逐点实形桥：eps < e·Q₂ − P₂ − w *)
    assert (HM : projT1 (cpf_rminus (real_mult (cauchy_real_exp (real_const x))
                                            (real_const (pade_den 2 x)))
                                    (real_const (pade_num 2 x))) n
                 - projT1 (real_const (cpf_witness_n2 x)) n
                 == projT1 (cauchy_real_exp (real_const x)) n * pade_den 2 x
                    - pade_num 2 x - cpf_witness_n2 x).
    { rewrite (cpf_rminus_proj _ _ n), (real_mult_proj _ _ n),
              (real_const_proj (pade_den 2 x) n),
              (real_const_proj (pade_num 2 x) n),
              (real_const_proj (cpf_witness_n2 x) n).
      reflexivity. }
    assert (HA : Qlt eps
      (projT1 (cauchy_real_exp (real_const x)) n * pade_den 2 x
        - pade_num 2 x - cpf_witness_n2 x)%Q).
    { apply (cpf_qeq_qlt eps eps _ _ (Qeq_refl eps) HM).
      apply QltT_to_Qlt. exact (HN n Hn). }
    (* 严格加法：eps < M−w ⟹ eps+w < (M−w)+w == M（Qplus_lt_l 翻面） *)
    assert (HB : Qlt (eps + cpf_witness_n2 x)
                   (projT1 (cauchy_real_exp (real_const x)) n
                      * pade_den 2 x - pade_num 2 x)%Q).
    { apply (cpf_qeq_qlt _ _ _ _ (Qeq_refl _)
               (cpf_pmix (projT1 (cauchy_real_exp (real_const x)) n
                            * pade_den 2 x - pade_num 2 x)%Q
                         (cpf_witness_n2 x))).
      apply (proj2 (Qplus_lt_l eps
        (projT1 (cauchy_real_exp (real_const x)) n * pade_den 2 x
          - pade_num 2 x - cpf_witness_n2 x)%Q (cpf_witness_n2 x))).
      exact HA. }
    assert (HC : Qlt (cpf_witness_n2 x)
                   (projT1 (cauchy_real_exp (real_const x)) n
                      * pade_den 2 x - pade_num 2 x)%Q).
    { apply (Qlt_trans _ (cpf_witness_n2 x + eps)%Q).
      - exact (cpf_qlt_add_r (cpf_witness_n2 x) eps Heps').
      - apply (cpf_qlt_eq_l (eps + cpf_witness_n2 x)%Q
                 (cpf_witness_n2 x + eps)%Q _
                 (Qplus_comm eps (cpf_witness_n2 x))).
        exact HB. }
    (* 目标面桥：P₂ < e·Q₂ *)
    assert (Hfin : projT1 (real_mult (cauchy_real_exp (real_const x))
                                     (real_const (pade_den 2 x))) n
                   - projT1 (real_const (pade_num 2 x)) n
                   == projT1 (cauchy_real_exp (real_const x)) n * pade_den 2 x
                      - pade_num 2 x).
    { rewrite (real_mult_proj _ _ n), (real_const_proj (pade_den 2 x) n),
              (real_const_proj (pade_num 2 x) n).
      reflexivity. }
    apply Qlt_to_QltT.
    apply (cpf_qeq_qlt _ _ _ _ (Qeq_refl _) (Qeq_sym _ _ Hfin)).
    exact HC.
Qed.

(* 链件（组合出 0<eˣ）：den2_pos + 主件 + num2_pos 经免除法传送闭合 *)
Theorem cpf_exp_pos_chain_n2 : forall x : Q,
  QltT 0 x ->
  real_lt (real_const (cpf_witness_n2 x))
          (cpf_rminus (real_mult (cauchy_real_exp (real_const x))
                                 (real_const (pade_den 2 x)))
                      (real_const (pade_num 2 x))) ->
  real_lt real_zero (cauchy_real_exp (real_const x)).
Proof.
  intros x Hx Hlow.
  apply (cpf_transport_no_div (cauchy_real_exp (real_const x))
                              (real_const (pade_num 2 x)) (pade_den 2 x)).
  - exact (cpf_den2_pos_all x).
  - exact (cpf_exp_pos_pade2 x Hx Hlow).
  - apply cpf_const_pos_lt. exact (cpf_num2_pos x Hx).
Qed.


(* S1 实际语句面 = 本文件 §5 主件的结论面（P₂ < eˣ·Q₂ 直达，非 M 面
   接口形）——故最终组装零中转：cpl_lower_even 显式应用免除法传送。
   §5 cpf_exp_pos_pade2 保留为接口参数形（M 面下界接口的独立推导路径，
   与直组装共存不合并，）分工段）。 *)
Theorem cpf_exp_pos_final_n2 : forall x : Q,
  QltT 0 x ->
  real_lt real_zero (cauchy_real_exp (real_const x)).
Proof.
  intros x Hx.
  apply (cpf_transport_no_div (cauchy_real_exp (real_const x))
                              (real_const (pade_num 2 x)) (pade_den 2 x)).
  - exact (cpf_den2_pos_all x).
  - exact (cpl_lower_even x Hx).
  - apply cpf_const_pos_lt. exact (cpf_num2_pos x Hx).
Qed.

End CpfFinale.

(* ===== 出口假设审计（G3 面：全 Closed；Psatz 闭包公理见头注公理面） ===== *)
Print Assumptions cpf_den2_pos_all.
Print Assumptions cpf_num2_pos.
Print Assumptions cpf_transport_no_div.
Print Assumptions cpf_exp_pos_pade2.
Print Assumptions cpf_exp_pos_chain_n2.
Print Assumptions cpf_exp_pos_final_n2.
(* ================= §2 psx_sign 族 ================= *)
(* ================= §1 psx_sign 族 ================= *)
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* ===== S1 定义面 ===== *)

(* (−1)^n 符号交替（Fixpoint 双步回绕：1,−1,1,−1,…，Set 层） *)
Fixpoint psx_sign (n : nat) : Q :=
  match n with
  | Datatypes.O => 1%Q
  | Datatypes.S Datatypes.O => (-1)%Q
  | Datatypes.S (Datatypes.S n') => psx_sign n'
  end.

(* 正因子部：1/(2n)!——pbp_sign_transfer 的 posf 槽实例 *)
Definition psx_posf (n : nat) : Q := 1%Q / q_fact (2 * n).

(* 首项系数（TailPos 定值面实形）：ptp_beta n 0 / (2n)! *)
Definition psx_coef (n : nat) : Q := ptp_beta n 0 / q_fact (2 * n).

(* 带号首项系数：(−1)^n · coef n——偶 n 正/奇 n 负 *)
Definition psx_signed (n : nat) : Q := psx_sign n * psx_coef n.

(* ===== S2 符号小引擎 ===== *)

(* 奇偶配对归纳（双步回绕一次性给全 ±1 面） *)
Lemma psx_sign_pair : forall n : nat,
  psx_sign (2 * n) == 1%Q /\ psx_sign (2 * n + 1) == (-1)%Q.
Proof.
  induction n as [| n IH].
  - split; reflexivity.
  - destruct IH as [IH1 IH2]. split.
    + replace ((2 * Datatypes.S n)%nat)
        with (Datatypes.S (Datatypes.S (2 * n))) by lia.
      exact IH1.
    + replace ((2 * Datatypes.S n + 1)%nat)
        with (Datatypes.S (Datatypes.S (2 * n + 1))) by lia.
      exact IH2.
Qed.

Lemma psx_sign_double : forall k : nat, psx_sign (2 * k) == 1%Q.
Proof. intro k. destruct (psx_sign_pair k) as [Hp _]. exact Hp. Qed.

Lemma psx_sign_odd : forall k : nat, psx_sign (2 * k + 1) == (-1)%Q.
Proof. intro k. destruct (psx_sign_pair k) as [_ Ho]. exact Ho. Qed.

(* 符号平方归一（主件去号完成用） *)
Lemma psx_sign_sq : forall n : nat, psx_sign n * psx_sign n == 1%Q.
Proof.
  intro n.
  assert (H : forall m : nat,
            psx_sign m * psx_sign m == 1%Q /\
            psx_sign (Datatypes.S m) * psx_sign (Datatypes.S m) == 1%Q).
  { induction m as [| m IH].
    - split; simpl; ring.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + simpl. exact IH1. }
  apply H.
Qed.

(* 正性引擎：posf 恒正（1/(2n)! 严格正，Qlt 面组装） *)
Lemma psx_posf_pos : forall n : nat, QltT 0 (psx_posf n).
Proof.
  intro n. apply Qlt_to_QltT. unfold psx_posf, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (H01 : Qlt 0%Q 1%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
    exact H01.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 双库桥：pbp_beta 与 ptp_beta 闭式逐字同构（透明 Definition 转换面） *)
Lemma psx_beta_bridge : forall n m : nat, ptp_beta n m == pbp_beta n m.
Proof. intros n m. exact (Qeq_refl (ptp_beta n m)). Qed.

(* 系数积形：coef n = ptp_beta n 0 · posf n（喂传送接口的积形） *)
Lemma psx_coef_prod : forall n : nat, psx_coef n == ptp_beta n 0 * psx_posf n.
Proof.
  intro n. unfold psx_coef, psx_posf, Qdiv.
  rewrite Qmult_1_l. reflexivity.
Qed.

(* ===== S3 主件：符号传送落地（pbp_sign_transfer 接口实例化） ===== *)

Theorem psx_sign_instantiated : forall (lead : Q) (n : nat),
  lead == psx_sign n * psx_coef n ->
  QltT 0 (psx_sign n * lead).
Proof.
  intros lead n Heq.
  apply (pbp_sign_transfer (psx_sign n * lead) (psx_posf n) n 0).
  - (* 去号完成：(−1)^n·lead = (−1)^n·((−1)^n·coef) = coef = β·posf *)
    rewrite Heq.
    rewrite Qmult_assoc.
    rewrite psx_sign_sq.
    rewrite Qmult_1_l.
    rewrite psx_coef_prod.
    rewrite psx_beta_bridge.
    reflexivity.
  - apply psx_posf_pos.
Qed.

(* TailPos 侧独立正性件：ptp_beta_pos 全称面显式应用首系数 *)
Corollary psx_coef_pos : forall n : nat, QltT 0 (psx_coef n).
Proof.
  intro n. apply Qlt_to_QltT. unfold psx_coef, Qdiv.
  apply Qmult_lt_0_compat.
  - apply QltT_to_Qlt. apply ptp_beta_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* 定值对表（TailPos 定值件直取）：coef 1 = 1/12，coef 2 = 1/720 *)
Lemma psx_coef_vals :
  psx_coef 1%nat == (1#12)%Q /\ psx_coef 2%nat == (1#720)%Q.
Proof. split; [exact ptp_beta_n1_first | exact ptp_beta_n2_first]. Qed.

(* ===== S4 对偶显式：偶 n 首系数正 / 奇 n 首系数负 ===== *)

(* 偶支：带号首项系数严格正（(−1)^(2k) = +1 直实例化；
   QltT 无 Qeq-Proper 实例——换号一律走 pbp_qlt0_eq_r 传桥，
   rewrite 只在 Qeq 目标内进行） *)
Corollary psx_even_pos : forall k : nat, QltT 0 (psx_signed (2 * k)).
Proof.
  intro k.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r
           (psx_sign (2 * k) * psx_signed (2 * k)) (psx_signed (2 * k))).
  - unfold psx_signed. rewrite psx_sign_double. ring.
  - apply QltT_to_Qlt.
    apply (psx_sign_instantiated (psx_signed (2 * k)) (2 * k)).
    unfold psx_signed. reflexivity.
Qed.

(* 奇支对偶：带号首项系数负（其相反数去号后严格正）——
   a = psx_sign·psx_signed（去号形）与 b = −psx_signed 恒等；
   传送件实例取 lead := psx_signed（奇号下其前提为真形） *)
Corollary psx_odd_neg : forall k : nat, QltT 0 (- psx_signed (2 * k + 1)).
Proof.
  intro k.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r
           (psx_sign (2 * k + 1) * psx_signed (2 * k + 1))
           (- psx_signed (2 * k + 1))).
  - unfold psx_signed. rewrite psx_sign_odd. ring.
  - apply QltT_to_Qlt.
    apply (psx_sign_instantiated (psx_signed (2 * k + 1)) (2 * k + 1)).
    unfold psx_signed. reflexivity.
Qed.


Print Assumptions psx_sign_instantiated.
Print Assumptions psx_coef_pos.
Print Assumptions psx_even_pos.
Print Assumptions psx_odd_neg.
Print Assumptions psx_coef_vals.

Separate Extraction psx_sign_instantiated psx_signed psx_coef psx_posf
  psx_sign psx_coef_pos psx_coef_vals.
(* ================= §2 pcu_c0 族 ================= *)
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== S1 定义面 ===== *)

(* 残差首系数闭式：c₀(n) = (n!)²/((2n)!(2n+1)!)
   （= β(n,0)/(2n)!，其中 β(n,m) = n!·(n+m)!/(2n+m+1)! 即
   ptp_beta/pbp_beta 双库同式闭式）。 *)
Definition pcu_c0 (n : nat) : Q :=
  q_fact n * q_fact n / (q_fact (2 * n) * q_fact (2 * n + 1)).

(* ===== S2 闭式评估（定值件） ===== *)

Lemma pcu_c0_val_n1 : pcu_c0 1 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma pcu_c0_val_n2 : pcu_c0 2 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma pcu_c0_val_n3 : pcu_c0 3 == (1#100800).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== S3 一般闭式定理（G2 主件，全称 n） ===== *)

(* Qinv 乘法分配（stdlib Qinv_mult_distr 一行实装，检验已证结论；
   q_fact (2*n) 类变元项非 constructor 形，conversion/reflexivity
   直击不可（实测），故经此桥。 *)
Lemma pcu_Qinv_mult : forall p q : Q, Qinv (p * q) == Qinv p * Qinv q.
Proof. intro p. intro q. apply Qinv_mult_distr. Qed.

(* 主桥：c₀(n) = β(n,0)/(2n)!。展开 ptp_beta 定义（q_fact (n+0)、
   (2n+0+1) 归一走 Nat.add_0_r），除法链 Qdiv 定义性展开后 Qinv
   乘法分配（pcu_Qinv_mult）+ ring 闭合。 *)
Lemma pcu_c0_eq_ptp : forall n : nat,
  pcu_c0 n == ptp_beta n 0 / q_fact (2 * n).
Proof.
  intro n.
  unfold pcu_c0, ptp_beta.
  repeat rewrite Nat.add_0_r.
  unfold Qdiv.
  assert (Hinv : Qinv (q_fact (2 * n) * q_fact (2 * n + 1)) ==
                 Qinv (q_fact (2 * n)) * Qinv (q_fact (2 * n + 1)))
    by (apply pcu_Qinv_mult).
  rewrite Hinv. ring.
Qed.

(* 对称形（站点桥的通用形） *)
Lemma pcu_site_ptp_gen : forall n : nat,
  ptp_beta n 0 / q_fact (2 * n) == pcu_c0 n.
Proof. intro n. symmetry. apply pcu_c0_eq_ptp. Qed.

(* BetaPos 桥（双库同式：psx_beta_bridge 一行承桥） *)
Lemma pcu_c0_eq_pbp : forall n : nat,
  pcu_c0 n == pbp_beta n 0 / q_fact (2 * n).
Proof.
  intro n.
  rewrite (pcu_c0_eq_ptp n).
  rewrite psx_beta_bridge.
  reflexivity.
Qed.


Lemma pcu_c0_pos : forall n : nat, QltT 0 (pcu_c0 n).
Proof.
  intro n. apply Qlt_to_QltT. unfold pcu_c0, Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* 成对件（Set 面 sigT 依值对——BetaPos pbp_beta_pos_sigT 同款承载；
   Qeq 属 Prop 不与 Set 混 /\——分面纪律）：β(n,0) 正性（pbp_beta_pos
   在盘）为见证位，c₀ 正性（今构）为承载位；闭式桥见上 pcu_c0_eq_pbp
   ——「正性已证（BetaPos）、闭式今统（本件）」三件成对。 *)
Corollary pcu_first_coef_pair : forall n : nat,
  sigT (fun _ : QltT 0 (pbp_beta n 0) => QltT 0 (pcu_c0 n)).
Proof.
  intro n.
  exact (existT (fun _ : QltT 0 (pbp_beta n 0) => QltT 0 (pcu_c0 n))
                (pbp_beta_pos n 0) (pcu_c0_pos n)).
Qed.

(* ===== S5 站点桥（每站点一处定义性实例） ===== *)

(* 位点④：TailPos 首系数定值件语句面（n=2 实例；2*2=4 转换级统一） *)
Lemma pcu_site_ptp_first : ptp_beta 2 0 / q_fact 4 == pcu_c0 2.
Proof. apply (pcu_site_ptp_gen 2). Qed.

(* n=1 孪生实例 *)
Lemma pcu_site_ptp_first1 : ptp_beta 1 0 / q_fact 2 == pcu_c0 1.
Proof. apply (pcu_site_ptp_gen 1). Qed.

(* 位点③：SignXfer 首系数定义面（psx_coef n := ptp_beta n 0/q_fact(2n)） *)
Lemma pcu_site_psx_coef2 : psx_coef 2 == pcu_c0 2.
Proof. unfold psx_coef. apply (pcu_site_ptp_gen 2). Qed.

Lemma pcu_site_psx_coef1 : psx_coef 1 == pcu_c0 1.
Proof. unfold psx_coef. apply (pcu_site_ptp_gen 1). Qed.

(* 位点①：Finale 主件见证（乘法形 x⁵·(1#720)）真形直使用 *)
Lemma pcu_site_cpf : forall x : Q,
  cpf_witness_n2 x == q_pow x 5%nat * pcu_c0 2.
Proof.
  intro x. unfold cpf_witness_n2. rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* 位点②：Lower 下界见证（除法形 y⁵/720——Qdiv 展开后同乘法形） *)
Lemma pcu_site_cpl : forall y : Q,
  q_pow y 5%nat / 720 == q_pow y 5%nat * pcu_c0 2.
Proof.
  intro y. rewrite pcu_c0_val_n2. unfold Qdiv. reflexivity.
Qed.

(* 位点⑤：TailPos n=2 残差多项式恒等式统一形（首项 = c₀·y⁵，全称 y） *)
Lemma pcu_n2_poly_unified : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == pcu_c0 2 * q_pow y 5%nat
     + (1#1440) * q_pow y 6%nat + (1#8640) * q_pow y 8%nat.
Proof.
  intro y. rewrite (ptp_n2_poly y). rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* ===== S7 数值锚链 ===== *)

(* 闭式与 Lower 数值锚核验桥：½⁵·c₀(2) == ½⁵/720 *)
Lemma pcu_sent_cpl_agree :
  q_pow (1#2) 5%nat * pcu_c0 2 == q_pow (1#2) 5%nat / 720.
Proof.
  rewrite (pcu_c0_val_n2). reflexivity.
Qed.

(* 合流：½⁵·c₀(2) = ½⁵/720 = 1/23040（位点② cpl_sent_witness_half 供货） *)
Lemma pcu_sent_unified : q_pow (1#2) 5%nat * pcu_c0 2 == (1#23040).
Proof.
  apply (Qeq_trans _ (q_pow (1#2) 5%nat / 720) _).
  - apply pcu_sent_cpl_agree.
  - exact cpl_sent_witness_half.
Qed.

(* 位点⑥：TailPos 数值锚统一形（残差在 y=½ 精确值，首项 = c₀·½⁵） *)
Lemma pcu_sentinel_n2_half_unified :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == pcu_c0 2 * (1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof.
  rewrite (ptp_sentinel_n2_half). rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* ===== S6 主件（G1：跨模块统一账） ===== *)

(* n=2 主账：四文件六位点常数的定义性展开全部 Qeq 统一到闭式 pcu_c0 2，
   而闭式评估 pcu_c0 2 == 1/720（S2）——1/720 撞车 = 同一闭式的化身。 *)
Theorem pcu_beta2_unify :
  pcu_c0 2 == (1#720) /\
  ptp_beta 2 0 / q_fact 4 == pcu_c0 2 /\
  psx_coef 2 == pcu_c0 2 /\
  (forall x : Q, cpf_witness_n2 x == q_pow x 5%nat * pcu_c0 2) /\
  (forall y : Q, q_pow y 5%nat / 720 == q_pow y 5%nat * pcu_c0 2) /\
  (forall y : Q,
     exp_partial 6 y * pade_den 2 y - pade_num 2 y
     == pcu_c0 2 * q_pow y 5%nat
        + (1#1440) * q_pow y 6%nat + (1#8640) * q_pow y 8%nat) /\
  q_pow (1#2) 5%nat * pcu_c0 2 == (1#23040).
Proof.
  (* 注意：repeat split 会经 delta+eq_refl 把闭式可转换的 Qeq 合取项
     （前三项两边皆封闭且同值）直接收掉，bullet 错位——apply conj
     不做转换穿透，目标数恒定（实测）。 *)
  repeat apply conj.
  - apply pcu_c0_val_n2.
  - apply pcu_site_ptp_first.
  - apply pcu_site_psx_coef2.
  - intro x. apply pcu_site_cpf.
  - intro y. apply pcu_site_cpl.
  - intro y. apply pcu_n2_poly_unified.
  - exact pcu_sent_unified.
Qed.

(* n=1 孪生账：1/12（y³ 位首系数；奇号带负由 psx_sign 承担，幅值同闭式） *)
Theorem pcu_beta1_unify :
  pcu_c0 1 == (1#12) /\
  ptp_beta 1 0 / q_fact 2 == pcu_c0 1 /\
  psx_coef 1 == pcu_c0 1.
Proof.
  repeat apply conj.
  - apply pcu_c0_val_n1.
  - apply pcu_site_ptp_first1.
  - apply pcu_site_psx_coef1.
Qed.

(* ===== 审计与提取 ===== *)

Print Assumptions pcu_c0_val_n2.
Print Assumptions pcu_c0_eq_ptp.
Print Assumptions pcu_c0_eq_pbp.
Print Assumptions pcu_c0_pos.
Print Assumptions pcu_first_coef_pair.
Print Assumptions pcu_beta2_unify.
Print Assumptions pcu_beta1_unify.
Print Assumptions pcu_sent_unified.
Print Assumptions pcu_sentinel_n2_half_unified.

Separate Extraction pcu_c0 pcu_beta2_unify pcu_beta1_unify pcu_sent_unified.
