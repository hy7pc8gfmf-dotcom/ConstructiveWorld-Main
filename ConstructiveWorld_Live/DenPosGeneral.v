(* ============================================================ *)
(* DenPosGeneral.v                                               *)
(*                                                               *)
(* 目的：补齐 Pade 分母多项式 pade_den n x 在低段 0 ≤ x < 2、       *)
(*       一般 n ≥ 1 上的严格正性（通用 n 版 den_pos 严格档）。      *)
(* 主件：dpg_den_pos_strict : forall (n : nat) (x : Q),            *)
(*       (1 <= n)%nat -> QleT' 0 x -> QltT x 2%Q ->                *)
(*       QltT 0 (pade_den n x)。                                   *)
(* 依赖：CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeDenPos、   *)
(*       UpReqAltSumPos、PadeDenPosB12；                            *)
(*       Stdlib QArith.QArith、Arith.Arith、Lia、Psatz、Setoid。     *)
(* 备注：库内既有覆盖为非负档 pdp_den_pos（UpReqPadeDenPos.v:480，    *)
(*       [0,1] QleT' 面）、弱前提版 pdpb_den_pos_le2                *)
(*       （PadeDenPosB12.v:141，[0,2] QleT' 面）与 (1,2) 严格段      *)
(*       pdq_den_pos_12_strict，均不含低段 [0,2) × 一般 n ≥ 1 的     *)
(*       严格档——本件补齐。证明骨架同 pdpb_den_pos_le2：             *)
(*       pdpb_R_ge_2 强化（x < 2 ≤ R_{n,k} 递减一跳）+ pdp_g 逐项    *)
(*       非负与尾段递减 + altsum_pos_strict 引擎 + qeq_ltT 换面；    *)
(*       首对严格由 dpg_g1_lt_g0 给出（将 pdq_g1_lt_g0 从 (1,2)      *)
(*       段泛化至 [0,2)）。伴件：dpg_den_pos_strict_T（QleT 前提     *)
(*       形）、dpg_den_pos_strict_le1（[0,1] 段推论）、              *)
(*       dpg_den2_one / dpg_den3_quarter（低段严格 vm_compute       *)
(*       哨兵，对照 pdp_den2_one / pdp_den3_one 仅 QleT' 面）。      *)
(*       全件 Qed；无外加假设（出口件 Print Assumptions 全           *)
(*       Closed）；语句面全 Set 层 QltT / QleT' / Qle（Prop 序       *)
(*       仅证内作桥）。                                            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp UpReqPadeDenPos UpReqAltSumPos.
Require Import PadeDenPosB12.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.
From Stdlib Require Import Setoid.

(* ===== 件 1：首对严格——x < 2 ≤ R_{n,0} ⟹ g(1) < g(0)（全 n≥1） ===== *)
(*   pdq_g1_lt_g0（DenPos12:183）前提含 QltT 1 x，仅覆盖 (1,2) 段；     *)
(*   本件泛化至 [0,2) 全段——低段 [0,1] 严格档缺口正卡在此件。           *)

Lemma dpg_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT x 2%Q ->
  QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hhi.
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
      + apply QleT'_to_Qle. apply pdpb_R_ge_2. exact Hk. }
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) x).
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) (pdp_R n 0)).
  exact Hc.
Qed.

(* ===== 件 2（主件·严格，库内缺口补齐）：0 ≤ x < 2 ∧ n≥1 ⟹ 0 < Q_n(x) *)
(*   骨架同 pdpb_den_pos_le2（B12:141），递减一步沿用 pdpb_term_decay  *)
(*   （x≤2 面），首对一步换用件 1，引擎 altsum_pos_strict 直供 QltT。   *)

Theorem dpg_den_pos_strict : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT' 0 x -> QltT x 2%Q -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hhi.
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by apply pdp_den_altsum.
  apply (qeq_ltT (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply Qeq_sym. exact Hb.
  - apply altsum_pos_strict.
    + intro k. apply pdp_g_nonneg. exact Hx.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdpb_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hx.
        -- apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hhi.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hx.
        -- apply Nat.leb_gt in E. lia.
    + apply (dpg_g1_lt_g0 n x Hn Hhi).
    + lia.
Qed.

(* ===== 件 3：Or 形假设面适配（pdpb_den_pos_le2_T 同位） ===== *)

Theorem dpg_den_pos_strict_T : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT 0 x -> QltT x 2%Q -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hhi.
  apply dpg_den_pos_strict.
  - exact Hn.
  - apply altsum_QleT_to_QleT'. exact Hx.
  - exact Hhi.
Qed.

(* ===== 件 4：[0,1] 主段严格版直系推论（与 pdp_den_pos 语句面          *)
(*   同前提位、结论面升 QltT——「0<=x 段」的严格兑现）                  ===== *)

Corollary dpg_den_pos_strict_le1 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QleT 0 x -> QleT x 1 -> QltT 0 (pade_den n x).
Proof.
  intros n x Hn Hx Hx1.
  apply dpg_den_pos_strict_T.
  - exact Hn.
  - exact Hx.
  - (* 目标取 QltT x 2（严格）形；QleT' x 1 与 1<2 经 Qle_lt_trans 严格化 *)
    apply Qlt_to_QltT.
    apply (Qle_lt_trans x 1 2).
    + apply QleT'_to_Qle. apply altsum_QleT_to_QleT'. exact Hx1.
    + unfold Qlt. simpl. lia.
Qed.

(* ===== 件 5：低段严格 vm_compute 哨兵（对照：pdp_den2_one/            *)
(*   pdp_den3_one @UpReqPadeDenPos.v:517/520 仅 QleT' 面） ===== *)

Lemma dpg_den2_one : QltT 0 (pade_den 2%nat 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma dpg_den3_quarter : QltT 0 (pade_den 3%nat (1#4)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ===== 出口件假设审计：全 Closed（证据在编译日志） ===== *)

Print Assumptions dpg_den_pos_strict.
Print Assumptions dpg_den_pos_strict_T.
Print Assumptions dpg_den_pos_strict_le1.
