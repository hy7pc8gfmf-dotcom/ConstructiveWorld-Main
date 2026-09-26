(* ==========================================================================)
   DenPosGeneral.v — Padé 分母严格正性件
   使命: dpg_den_pos_strict 及其指标平移形 dpg_den_pos_strict_T、推论 dpg_den_pos_strict_le1：Padé 逼近分母 Q̃ 的严格正性（g0<g1 归纳核）；附 vm_compute 数值锚 dpg_den2_one/dpg_den3_quarter。
   依赖: CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeDenPos、UpReqAltSumPos、PadeDenPosB12；Stdlib QArith、Arith、Lia、Setoid。
   对标: Padé 逼近论中分母多项式的正性引理（Beukers/Apéry 型无理性证明的标准组件）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
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

(* ===== 件 5：低段严格 vm_compute 守卫（对照：pdp_den2_one/            *)
(*   pdp_den3_one @UpReqPadeDenPos.v:517/520 仅 QleT' 面） ===== *)

Lemma dpg_den2_one : QltT 0 (pade_den 2%nat 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma dpg_den3_quarter : QltT 0 (pade_den 3%nat (1#4)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ===== 出口件假设审计：全 Closed（证据在编译日志） ===== *)

Print Assumptions dpg_den_pos_strict.
Print Assumptions dpg_den_pos_strict_T.
Print Assumptions dpg_den_pos_strict_le1.
