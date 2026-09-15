(* ============================================================ *)
(* UpReqPadeDenPos12.v *)
(* *)
(* 目的： 路径 C 分母正性的 (1,2) 段。 *)
(* 主件： pdq_den_pos_12_strict：(1,2) 段分母严格正。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeQLeg。 *)
(* 备注： 项衰减 pdq_term_decay_2 为构造核；g1 < g0 递减为显式腿。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeDenPos12.v —— 席CS2④：路径 C 分母正性 (1,2) 段          *)
(*                         （pdq_：x∈(1,2) ⟹ Q_n(x) ≥ 0 且 > 0）     *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 任务定位（切片④）：pdp_den_pos（UpReqPadeDenPos.v:480）已证       *)
(*   0 ≤ x ≤ 1 档；本件补 (1,2) 档，消费同一 altsum 引擎             *)
(*   （UpReqAltSumPos），把递减面从 x ≤ 1 升到 x < 2。               *)
(*                                                                 *)
(* 路线裁决（派单路线 1/x 对称归约 = 作废，证据两条）：               *)
(*   ① 代数反例（n=1）：Q_1(x)=1−x/2，而 x·Q_1(1/x)=x−1/2，          *)
(*      两者无恒等关系；一般 n 的系数 c_{n,k} 与反向系数 c_{n,n−k}    *)
(*      含 (n+j)!/(2n−j)! 型因子，j≠n/2 时不等，倒数点无恒等式。      *)
(*   ② 库内唯一点间关系 pade_den_sym（UpReqPadeExp.v:116）把 Q_n(x)  *)
(*      归到 P_n(−x)，变元 −x∈(−2,−1) 不落入任何已证正域（P_n 正     *)
(*      系数正性只对正变元有效），对合非倒数，归约链断裂。           *)
(*   改走路线（引擎原生域）：UpReqAltSumPos.v 头注明示引擎设计域即    *)
(*   「0 ≤ x < 2 时各项 c_k·x^k 非负递减 ⟹ den ≥ 0」，pdp 只实例化   *)
(*   了 x ≤ 1 档（pdp_term_decay 用 x≤1 于乘法单调步）。本件新建      *)
(*   比率下界 pdq_R_ge_2：c_k/c_{k+1} = pdp_R n k ≥ 2（k<n），       *)
(*   由 x < 2 ≤ pdp_R n k 得逐项递减，一跳消费引擎。                 *)
(*   核心代数：(k+1)(2n−k) ≥ 2(n−k) ⟺ k(2n−k+2) ≥ 0，k=0 取等        *)
(*   （此时 pdp_R n 0 = 2 恰为端点），AA12 腿 pql_nat_ratio_mono2。   *)
(*                                                                 *)
(* 消费面（全部已绿件 Require，零改写）：                            *)
(*   UpReqPadeExp：pade_coeff_0_one；                                *)
(*   UpReqPadeSign：pds_c11（n=1 闭式系数哨兵）；                    *)
(*   UpReqPadeDenPos：pdp_g/pdp_R/pdp_ZS1_nz/pdp_qmult_le_compat_l/  *)
(*     pdp_coeff_pos_any/pdp_coeff_ratio/pdp_g_nonneg/pdp_g_decay_hi/ *)
(*     pdp_den_altsum（pdq_R_ge_2 全程镜像 pdp_R_ge_1 骨架）；        *)
(*   UpReqAltSumPos：altsum_nonneg_leT/altsum_pos_strict/            *)
(*     altsum_QleT_to_QleT'/altsum_acc_T/altsum_acc_F/               *)
(*     altsum_acc_0_eq/qeq_ltT；                                    *)
(*   S02（经 ）：QltT/QltT_to_Qlt/Qlt_to_QltT/Qle_to_QleT'/     *)
(*     QleT'_to_Qle/qleT'_trans/qeq_leT'/qltT_leT'；                 *)
(*   S03（经 ）：q_pow_nonneg/q_fact_succ/q_fact_pos/q_neq_of_lt; *)
(*   stdlib：Qmult_le_compat_l/Qmult_le_compat_r/Qmult_lt_compat_r/  *)
(*     Qlt_trans/Qlt_le_trans/Qmult_1_r/Qmult_comm/Qeq_sym/          *)
(*     Qmult_inv_r/Qinv_lt_0_compat/Qlt_not_eq/ring/lia（AA12 腿化后   *)
(*     零 nia，Psatz 面断根）。                                     *)
(*                                                                 *)
(* 红线自查：语句面全 Set 层（QltT=Id-of-bool、QleT'=Id-of-bool、     *)
(*   QleT=Or 形均 S02 Set 值）；Prop 序 Qlt/Qle 仅在证明体内作桥      *)
(*   （UpReqPadeSign 方法注记①同款）；零外加假设，公理面由           *)
(*   Print Assumptions 闭合审计；全 Qed；前缀 pdq_ 双树防撞。         *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp UpReqPadeDenPos UpReqPadeSign UpReqAltSumPos.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 件 1：比率下界 pdp_R n k ≥ 2（k < n）——本件核心新数学。           *)
(*   镜像 pdp_R_ge_1 骨架：2 = inv(a)·(2·a) ≤ inv(a)·(b·c) = pdp_R，  *)
(*   其中 2·a ≤ b·c 由 Z 层腿件（pql_nat_ratio_mono2，k(2n−k+2) ≥ 0）。*)
(* ============================================================ *)
Lemma pdq_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2%Q (pdp_R n k).
Proof.
  intros n k Hk.
  assert (Hlit : QleT' ((2 # 1) *
                          (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q
                       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
                         (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (pql_nat_ratio_mono2 n k Hk). lia. }
  assert (Hinvpos : QleT' 0%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt. cbn [Qnum Qden]. lia. }
  assert (Ez : Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
               (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) == 1%Q).
  { apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))
      ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      1%Q).
    - ring.
    - apply Qmult_inv_r. apply pdp_ZS1_nz. }
  apply (qleT'_trans 2%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
    (pdp_R n k)).
  - apply qeq_leT'. apply Qeq_sym.
    apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       ((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      (((2 # 1) *
        (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
         (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))))
      2%Q).
    + ring.
    + rewrite Ez. ring.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. unfold pdp_R. ring.
Qed.

(* ============================================================ *)
(* 件 2：递减面升档——x ≤ 2 时逐项递减（镜像 pdp_term_decay，          *)
(*   把「x≤1 乘法单调步」换成「x ≤ 2 ≤ c_k/c_{k+1} 比率步」）。        *)
(* ============================================================ *)
Lemma pdq_term_decay_2 : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0%Q x -> QleT' x 2%Q ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx0 Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  change (q_pow x (Datatypes.S k)) with (x * q_pow x k).
  assert (HstepT : QleT' (pade_coeff n (Datatypes.S k) * x) (pade_coeff n k)).
  { apply (qleT'_trans (pade_coeff n (Datatypes.S k) * x)
                       (pade_coeff n (Datatypes.S k) * pdp_R n k)
                       (pade_coeff n k)).
    - apply pdp_qmult_le_compat_l.
      + apply (qleT'_trans x 2%Q (pdp_R n k)).
        * exact Hx2.
        * apply pdq_R_ge_2. exact Hk.
      + apply qltT_leT'. apply pdp_coeff_pos_any.
    - apply qeq_leT'. apply Qeq_sym. apply pdp_coeff_ratio. exact Hk. }
  apply (qleT'_trans
           (pade_coeff n (Datatypes.S k) * (x * q_pow x k))
           ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
           (pade_coeff n k * q_pow x k)).
  - apply qeq_leT'. ring.
  - apply pdp_qmult_le_compat_r.
    + exact HstepT.
    + apply Qle_to_QleT'. apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx0.
Qed.

(* ============================================================ *)
(* 件 3（S2 主件·非严格）：1 < x < 2 ⟹ 0 ≤ Q_n(x)。                  *)
(*   语句面照 pdp_den_pos 实形档（结论 QleT'）；骨架同 pdp_den_pos，  *)
(*   仅递减假设位换 pdq_term_decay_2。                                 *)
(* ============================================================ *)
Theorem pdq_den_pos_12 : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QleT' 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx0 : QleT 0%Q x).
  { left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
    - unfold Qlt. reflexivity.
    - apply QltT_to_Qlt. exact Hlo. }
  assert (Hxa : QleT' 0%Q x) by (apply altsum_QleT_to_QleT'; exact Hx0).
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by apply pdp_den_altsum.
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply pdq_term_decay_2;
          [apply Nat.leb_le in E; lia | exact Hxa | exact Hx2].
      * apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; lia].
  - apply qeq_leT'. apply Qeq_sym. exact Hb.
Qed.

(* ============================================================ *)
(* 件 4：严格版支撑（首对严格 + 引擎 altsum_pos_strict 直供）。        *)
(* ============================================================ *)

(* 件 4a：g(0) = 1（c_{n,0}=1、x^0=1，全 n 成立） *)
Lemma pdq_g0_one : forall (n : nat) (x : Q), pdp_g n x 0%nat == 1%Q.
Proof.
  intros n x. unfold pdp_g.
  assert (E0 : (0 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  rewrite E0. cbn [q_pow].
  rewrite (pade_coeff_0_one n). ring.
Qed.

(* 件 4b：首对严格 g(1) < g(0)——不显式算 c_{n,1}，经比率恒等式        *)
(*   c_0 == c_1·R_0 与 x < 2 ≤ R_0、c_1 > 0 传递。                   *)
Lemma pdq_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT 1%Q x -> QltT x 2%Q ->
  QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hlo Hhi.
  assert (Hk : (0 < n)%nat) by lia.
  assert (E0 : (0 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E0. cbn [q_pow].
  apply Qlt_to_QltT.
  repeat rewrite Qmult_1_r.
  rewrite (pdp_coeff_ratio n 0%nat Hk).
  assert (Hc : x * pade_coeff n (Datatypes.S 0)
               < pdp_R n 0 * pade_coeff n (Datatypes.S 0)).
  { apply (Qmult_lt_compat_r x (pdp_R n 0) (pade_coeff n (Datatypes.S 0))).
    - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    - apply (Qlt_le_trans x 2%Q (pdp_R n 0)).
      + apply QltT_to_Qlt. exact Hhi.
      + apply QleT'_to_Qle. apply pdq_R_ge_2. exact Hk. }
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) x).
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) (pdp_R n 0)).
  exact Hc.
Qed.

(* 件 4c：n=1 闭形 den_1(x) == 1 − x/2（pds_c11 哨兵系数显式应用） *)
Lemma pdq_den1_form : forall x : Q,
  pade_den 1%nat x == 1%Q + Qopp ((1#2)%Q * x).
Proof.
  intros x. rewrite (pdp_den_altsum 1%nat x).
  unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F.
  rewrite (altsum_acc_0_eq true (pdp_g 1%nat x) 2%nat).
  assert (E0 : (0 <=? 1)%nat = true) by (apply Nat.leb_le; lia).
  assert (E1 : (1 <=? 1)%nat = true) by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E0, E1. cbn [q_pow].
  rewrite (pade_coeff_0_one 1%nat). rewrite pds_c11. ring.
Qed.

(* 件 4c'：n=0 闭形 den_0(x) == 1（与变元无关） *)
Lemma pdq_den0_one : forall x : Q, pade_den 0%nat x == 1%Q.
Proof.
  intros x. rewrite (pdp_den_altsum 0%nat x).
  unfold altsum. rewrite altsum_acc_T.
  rewrite (altsum_acc_0_eq false (pdp_g 0%nat x) 1%nat).
  rewrite (pdq_g0_one 0%nat x). ring.
Qed.

(* 件 4d：半线性事实内联于件 5 的 n=1 分支（Prop 序仅证内作桥，        *)
(*   不设独立语句面——纪律：语句面不落 Qlt Prop 形）。                  *)

(* ============================================================ *)
(* 件 5（S2 主件·严格）：1 < x < 2 ⟹ 0 < Q_n(x)（全 n）。             *)
(*   n≥2 走引擎 altsum_pos_strict（首对严格 + 非负尾）；n=0 恒一、      *)
(*   n=1 闭式 1 − x/2 > 0。                                          *)
(* ============================================================ *)
Theorem pdq_den_pos_12_strict : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QltT 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  destruct n as [|[|m]].
  - apply Qlt_to_QltT. rewrite pdq_den0_one. unfold Qlt. reflexivity.
  - apply Qlt_to_QltT. rewrite pdq_den1_form.
    apply QltT_to_Qlt in Hhi.
    destruct x as [nx dx].
    unfold Qlt in *. cbn [Qnum Qden Qcompare Qmult Qopp Qplus] in *. lia.
  - assert (Hxa : QleT' 0%Q x).
    { apply altsum_QleT_to_QleT'.
      left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
      - unfold Qlt. reflexivity.
      - apply QltT_to_Qlt. exact Hlo. }
    assert (Hdec : forall k : nat,
              QleT' (pdp_g (Datatypes.S (Datatypes.S m)) x (Datatypes.S k))
                    (pdp_g (Datatypes.S (Datatypes.S m)) x k)).
    { intro k.
      destruct (Nat.leb (Datatypes.S k) (Datatypes.S (Datatypes.S m))) eqn:E.
      - apply pdq_term_decay_2;
          [apply Nat.leb_le in E; lia | exact Hxa | exact Hx2].
      - apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; lia]. }
    apply (qeq_ltT
             (altsum (pdp_g (Datatypes.S (Datatypes.S m)) x)
                     (Datatypes.S (Datatypes.S (Datatypes.S m))))
             (pade_den (Datatypes.S (Datatypes.S m)) x)).
    + apply Qeq_sym. apply pdp_den_altsum.
    + apply altsum_pos_strict.
      * intro k. apply pdp_g_nonneg. exact Hxa.
      * exact Hdec.
      * apply pdq_g1_lt_g0; [lia | exact Hlo | exact Hhi].
      * lia.
Qed.

Print Assumptions pdq_den_pos_12.
Print Assumptions pdq_den_pos_12_strict.
