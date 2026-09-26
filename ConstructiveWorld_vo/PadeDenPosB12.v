(* ============================================================ *)
(* PadeDenPosB12.v —— 席CWA：Padé [n/n] 分母正性 x∈(1,2] 段闭合        *)
(*                    （UpReqPadeDenPos 挂账 b，E-STAGING-CWA 任务 2）  *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 使命（台账原文 UpReqPadeDenPos.v:33-34 挂账 b）：                   *)
(*   「x ∈ (1,2) 段：系数比极小值实为 2（k=0 处），衰减对 x <= 2        *)
(*   成立（分母真零点在 x = 2），但 x ∈ (1,2] 段递减装配需比式消元      *)
(*   （乘 Qinv 正因子），待下轮。」——本件以递减装配真证闭合。           *)
(*                                                                 *)
(* 数学内容：                                                       *)
(*   系数比 R(n,k) = (2n-k)(k+1)/(n-k)（k < n，pdp_R 定义）。          *)
(*   关键强化：R(n,k) ≥ 2（并非仅 ≥ 1）——Z 层恒等式                   *)
(*     (2n-k)(k+1) - 2(n-k) = k(2n-k+1) ≥ 0（0 ≤ k < n），            *)
(*   极小值在 k=0 处取 2，与台账「系数比极小值实为 2」对账。            *)
(*   递减装配（比式消元）：x ≤ 2 ≤ R(n,k) ⟹                          *)
(*     c_{k+1}·x^{k+1} = (c_{k+1}·x)·x^k ≤ (c_{k+1}·R)·x^k           *)
(*       = c_k·x^k（中间步乘正因子 c_{k+1} 保序——即比式消元；          *)
(*   证据形态取 pdp_coeff_ratio 的 Qeq 恒等式 c_k == c_{k+1}·R，       *)
(*   免除真除法，右端消元以 Qeq 对账完成）。                           *)
(*   随后沿用 PC2 引擎出口 altsum_nonneg_leT（非负递减有限交错和       *)
(*   非负）经 pdp_den_altsum 桥回 pade_den，n=0/1/2/… 全通项覆盖。     *)
(*   主件结论域 [0,2] 全段（含 (1,2] 挂账段；x=2 处 n=1 分母取 0，     *)
(*   故出口为非负 QleT' 而非严格正，与「真零点在 x = 2」对账）。        *)
(*                                                                 *)
(* 红线自审：                                                       *)
(*   —— 禁词全零（scan_redline.py 全文件计）；全 Qed 真证，零降级占位；  *)
(*   —— 语句面全 Set 层（QleT'/QltT/QleT），无 Qlt/Qle/exists/and/or    *)
(*      Prop 命题出场，无 -> False；(k < n)%nat 为 nat 层指标前提       *)
(*      （UpReqPadeDenPos 同款通例）；Prop 序仅证内转译。               *)
(*   —— 非平凡：Z 层 nia 二次比式 + 乘正因子比式消元装配 + PC2 引擎      *)
(*      放电，非平凡交付。                                            *)
(*   —— G3 提取探针 Obj.magic=0（Recursive Extraction 主定理族）。     *)
(*                                                                 *)
(* 编译配方（cpu_guard 温控包装；依赖 UpReqPadeExp/UpReqAltSumPos/      *)
(* UpReqPadeDenPos .vo 已先经同配方在 Live/build 就位）：              *)
(*   bash Live/tools/cpu_guard.sh -c \                               *)
(*     "cd Live/build && rocq c -Q . \"\" PadeDenPosB12.v"           *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== 件 1：系数比下界强化 2 ≤ R(n,k)（挂账 b 的代数核） =====
   (2n-k)(k+1) ≥ 2(n-k) ⟺ k(2n-k+1) ≥ 0（Z 层 nia；
   nat 截断减法经 S(·) 归一，zify + 显式 Z 上下文双保险）。 *)

Lemma pdpb_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2 (pdp_R n k).
Proof.
  intros n k Hk.
  assert (ZK : (0 <= Z.of_nat k)%Z) by lia.
  assert (ZKN : (Z.of_nat k < Z.of_nat n)%Z) by lia.
  assert (Hlit : QleT' ((2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q)
    (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
      (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul]. nia. }
  assert (Hinvpos : QleT' 0
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
     (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
    (pdp_R n k)).
  - apply qeq_leT'.
    apply (Qeq_trans 2%Q
      ((Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
        (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) * 2%Q)%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q).
    + apply Qeq_sym.
      rewrite Ez. ring.
    + ring.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (2%Q * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. unfold pdp_R. ring.
Qed.

(* ===== 件 2：x ∈ (1,2] 段相邻递减（比式消元装配） =====
   c_{k+1}·x^{k+1} ≤ c_k·x^k：链
     c_{k+1}·x^{S k} == (c_{k+1}·x)·x^k           （q_pow_succ + ring）
     ≤ (c_{k+1}·R(n,k))·x^k                       （x ≤ 2 ≤ R，乘正因子保序）
     == c_k·x^k                                   （pdp_coeff_ratio 比式消元） *)

Lemma pdpb_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QleT' x 2 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  apply Qle_to_QleT'.
  assert (Hxk : Qle 0 (q_pow x k))
    by (apply q_pow_nonneg; apply QleT'_to_Qle; exact Hx).
  assert (HxR : QleT' x (pdp_R n k)).
  { apply (qleT'_trans x 2%Q (pdp_R n k)).
    - exact Hx2.
    - apply pdpb_R_ge_2. exact Hk. }
  assert (Hcx : QleT' (pade_coeff n (Datatypes.S k) * x)
                      (pade_coeff n (Datatypes.S k) * pdp_R n k)).
  { apply pdp_qmult_le_compat_l.
    - exact HxR.
    - apply qltT_leT'. apply pdp_coeff_pos_any. }
  apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                   ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
                   (pade_coeff n k * q_pow x k)).
  - apply qeq_imp_qle. rewrite (q_pow_succ x k). ring.
  - apply (Qle_trans ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
                     ((pade_coeff n (Datatypes.S k) * pdp_R n k) * q_pow x k)
                     (pade_coeff n k * q_pow x k)).
    + apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. exact Hcx.
      * exact Hxk.
    + apply qeq_imp_qle. rewrite (pdp_coeff_ratio n k Hk). reflexivity.
Qed.

(* ===== 件 3：S2 主件——0 ≤ x ≤ 2 ⟹ 0 ≤ 分母（覆盖挂账 (1,2] 段） ===== *)

Theorem pdpb_den_pos_le2 : forall (n : nat) (x : Q),
  QleT' 0 x -> QleT' x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hxa Hxb.
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdpb_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hxa.
        -- exact Hxb.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hxa.
        -- apply Nat.leb_gt in E. lia.
  - apply qeq_leT'. apply Qeq_sym. apply pdp_den_altsum.
Qed.

(* ===== 件 4：Or 形适配（与 pdp_den_pos 语句面同构） ===== *)

Theorem pdpb_den_pos_le2_T : forall (n : nat) (x : Q),
  QleT 0 x -> QleT x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx2.
  apply pdpb_den_pos_le2.
  - apply altsum_QleT_to_QleT'. exact Hx0.
  - apply altsum_QleT_to_QleT'. exact Hx2.
Qed.

(* ===== 件 5：台账书面形——x ∈ (1,2] 段挂账 b 正式闭合 ===== *)

Theorem pdpb_den_pos_b12 : forall (n : nat) (x : Q),
  QltT 1 x -> QleT x 2 -> QleT' 0 (pade_den n x).
Proof.
  intros n x H1 H2.
  apply pdpb_den_pos_le2.
  - apply Qle_to_QleT'.
    apply (Qle_trans 0%Q 1%Q x).
    + unfold Qle. simpl. lia.
    + apply Qlt_le_weak. apply QltT_to_Qlt. exact H1.
  - apply altsum_QleT_to_QleT'. exact H2.
Qed.

(* ===== 件 6：vm_compute 端到端对账（含 x=2 真零点边界） ===== *)
(* den_1(x) = 1 - x/2（x=2 处取 0，非负出口在此贴零）；
   den_2(2) = 1/3 > 0；den_3(2) = 1 - 1 + 2/5 - 1/15 = 1/3 > 0。 *)

Lemma pdpb_den1_two : QleT' 0 (pade_den 1%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den1_three_halves : QltT 0 (pade_den 1%nat (3 # 2)).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den2_two : QltT 0 (pade_den 2%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdpb_den3_two : QltT 0 (pade_den 3%nat 2%Q).
Proof. vm_compute. reflexivity. Qed.

(* ===== G4：主定理假设全 Closed（证据在编译日志） ===== *)

Print Assumptions pdpb_R_ge_2.
Print Assumptions pdpb_term_decay.
Print Assumptions pdpb_den_pos_le2.
Print Assumptions pdpb_den_pos_le2_T.
Print Assumptions pdpb_den_pos_b12.
