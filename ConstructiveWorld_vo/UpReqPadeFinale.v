(* ============================================================ *)
(* UpReqPadeFinale.v *)
(* *)
(* 目的： 路径 C 总装预备段（n=2 旗舰完成）。 *)
(* 主件： cpf_witness_n2 与 cpf_exp_pos_pade2 旗舰；免除法传送 cpf_transport_no_div。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeLower、UpReqPadeQLeg。 *)
(* 备注： 免除法纪律：库内 Real 层无除法面，全部以乘积面构造；显式假设随登记段申报。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeFinale.v —— 席C-F：C 路总装预备（n=2 旗舰完成）          *)
(*   保底件一 cpf_den2_pos_all / 保底件二 cpf_num2_pos /            *)
(*   免除法传送 cpf_transport_no_div / 主件 cpf_exp_pos_pade2       *)
(*   + 链件 cpf_exp_pos_chain_n2（组合出 0<eˣ）                     *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 闸门裁决（候③）：UpReqPadeLower.vo 开工时不在盘（ls 双证：       *)

(*   按闸门协议主件以下界件为【显式接口参数】（语句形与工单 §1.3     *)
(*   cpl_lower_even 同面，落盘后可直接 exact 实例化消费），显式假设  *)
(*   是先例非承认件（出口 Print Assumptions 全 Closed）。            *)
(*                                                                 *)
(* 完全平方构造性面（保底件一）：                                   *)
(*   Q₂(x) = 1 − x/2 + x²/12 = (x²−6x+12)/12 = ((x−3)²+3)/12 > 0    *)
(*   对一切 x（q²≥0 构造见证：destruct Q 全构造子 + Z 层 lia，       *)
(*   无经典 case、无三分律实例化）。此件使段切割在 n=2 层面整体      *)
(*   消失——(1,2) 归约、全域分段均不再需要；与 S2 席切片④不冲突：     *)
(*   ④服务符号化 n 升级，本件是 n=2 配方实例（分工见合规自查报告）。      *)
(*                                                                 *)
(* 免除法纪律（E395/DTPT2 卡）：库内 Real 层无除法面（S02 普查       *)
(*   real_div/real_inv 0 命中），一切「P/Q 比较」以纯乘法形承载：    *)
(*   「e ≥ P/Q、误差 ≥ w/Q」⟺「e·Q ≥ P + w」（Q>0 传送）。          *)
(*   Q 层见证也用乘法形（w := x⁵·(1#720)，Qdiv 不进 ring）。         *)
(*                                                                 *)
(* 公理面声明：AA12 腿化后本件零 Require Psatz（原 nia 桥件五处      *)
(*   一跳 UpReqPadeQLeg 自建 Q 单调腿，Psatz 环境闭包公理三件随之     *)
(*   断根）；本件出口 Print Assumptions 预期全 Closed。语句面 Prop    *)
(*   泄露 0：结论面全 QltT/real_lt(sigT,Set)，唯 Prop 语句面是       *)
(*   Q 层桥件 cpf_qeq_qlt 等（S02 QltT_to_Qlt 同款桥件定位）。        *)
(*                                                                 *)
(* 数值哨兵（TCS1 侦察报告 §②）：E₆·Q₂−P₂ == y⁵/720+y⁶/1440+        *)
(*   y⁸/8640（系数全非负）；主件见证 w := x⁵/720 即正尾首项          *)
(*   c₀ = (2!)²/(4!·5!) = 1/720。诚实注记：真误差 e−P₂/Q₂ 严格       *)
(*   大于 x⁵/(720·Q₂)（正尾余项），「误差 ≤」面不成立，本件取下界    *)
(*   面（工单 §四.9 尾界教训只约束上界侧；下界见证首项足额）。        *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp.
Require Import UpReqPadeLower.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

Section CpfFinale.

(* ===== §0 Q 层桥件（AA12 腿化：一跳 UpReqPadeQLeg 自建单调腿） ===== *)

(* Qeq 穿透墙桥：== 不可 rewrite 进 Qlt/QltT 目标（CS 卡），
   以桥件承载换形。桥件语句面 Prop——S02 QltT_to_Qlt 同款定位。
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

(* n=2 系数哨兵（vm_compute 闭式；字面点无 Nat.sub 截断坑） *)
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

(* ===== §5 主件（闸门候③）：定量旗舰组合形 ===== *)

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

(* ===== §6 最终组装（③落盘开闸 20260914 06:03）：直消费 cpl_lower_even ===== *)

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
