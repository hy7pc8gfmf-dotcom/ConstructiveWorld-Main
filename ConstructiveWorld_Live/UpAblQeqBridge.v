(* ============================================================ *)
(* UpAblQeqBridge.v —— Q 层 Qeq 右换形位＋Qmult_inv 桥件（P3 席·20260920）  *)
(*                                                                *)
(* 席位：P3（Qeq 右换形/Qmult_inv 桥件补建席，N10 报告后续槽①）            *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   交付语句面：主件 qbg_arch_geom_direct 全 Set 层（sigT/NatLe/QleT'，    *)
(*   与 S03:383 q_arch_geom 逐字同形）；qbg_Qinv_pos/qbg_ltT_eq_compat_r    *)
(*   亦 Set 面。qbg_mult_inv/qbg_lt_eq_compat_r/qbg_div_pos 为 Qeq/Qlt      *)
(*   序面辅助桥件（同 S02 库内序面辅助件体例，供四坐标局部链复用），         *)
(*   全部构造证明，不落 Set 层语句。                                       *)
(*                                                                *)
(* 桥位来源（N10 定谳表槽②·阻断机理逐条对应）：                            *)
(*   阻断一：Qinv 三支符号 match 阻断定义性换形（Qinv x 之分子符号         *)
(*     分支使 Qmake 互换拒绝转换）——桥件 A1 qbg_mult_inv 以 Qdiv 展开      *)
(*     ＋Qmult_1_l 升格命名（S02:1725 内联舞步的成品化），正性门 B2         *)
(*     以之绕开 match 手拆；                                              *)
(*   阻断二：S02 qltT_eq_compat_l 仅左向——桥件 A2/A3 补右向换形位          *)
(*     （Qlt Prop 基座＋QltT Set 基座对偶）。                              *)
(* 见证配方（N10 定谳表槽②）：五同形 q_arch_geom 位                       *)
(*   S10:1675/1722/6424/11088/12009 直配——                                *)
(*   N := uabS4b_arch_N (Qinv (2B))（Qfloor 指标，uabS4b_null_lt 证书），  *)
(*   调和反演 Qinv_lt_contravar proj2，退化支（B ≤ 0）N := 0 平凡承接。    *)
(*   标样取五坐标中最浅位 S10:1675（sc_sin_partial_cauchy_bounded）；      *)
(*   其余四位（:1722/6424/11088/12009）同形照此模板。                     *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全 Export 薄壳）＋              *)
(*   UpAblAbsSumLeB2（S4B Qfloor 谱系件）。只读零改动；                    *)
(*   未入 order.txt/_CoqProject（新独立件）。                              *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* Part 0 · 冻结现态打表（签名漂移即响亮失败）                              *)
(* ============================================================ *)

Check QltT. Check QleT'.
Check QltT_to_Qlt. Check Qlt_to_QltT. Check Qle_to_QleT'.
Check qltT_eq_compat_l. Check qeq_le.
Check Qlt_le_dec. Check Qlt_le_weak. Check Qlt_le_trans.
Check Qinv. Check Qinv_lt_contravar. Check Qmult_1_l.
Check Qmult_lt_0_compat. Check Qmult_le_compat_r. Check Q2_pos. Check Q2_nonneg.
Check Qle_of_nat.
Check uabS4b_arch_N. Check uabS4b_null_lt.
Check q_arch_geom.

(* ============================================================ *)
(* Part A · 两桥件（N10 定谳「缺 Qeq 右换形件与 Qmult_inv 桥件」逐条补位）   *)
(* ============================================================ *)

(* A1 · Qmult_inv 桥件：Qinv–Qdiv 关系成品（Qdiv x y := x·Qinv y 折叠， *)
(*      Qmult_1_l 升格命名；绕开 Qinv 符号 match 的定义性换形阻断）        *)
Lemma qbg_mult_inv : forall x : Q, Qinv x == 1 / x.
Proof.
  intro x. unfold Qdiv. symmetry. apply Qmult_1_l.
Qed.

(* A2 · Qeq 右换形位（Qlt 基座）：右支 Qeq 换形自由过 Qlt                *)
Lemma qbg_lt_eq_compat_r : forall a x y : Q, x == y -> a < x -> a < y.
Proof.
  intros a x y Hxy Hlt. rewrite <- Hxy. exact Hlt.
Qed.

(* A3 · Qeq 右换形位（QltT Set 基座）：与 S02 qltT_eq_compat_l 左向件对偶 *)
Lemma qbg_ltT_eq_compat_r : forall a x y : Q, x == y -> QltT a x -> QltT a y.
Proof.
  intros a x y Hxy H.
  apply Qlt_to_QltT.
  apply (qbg_lt_eq_compat_r a x y Hxy).
  apply QltT_to_Qlt. exact H.
Qed.

(* ============================================================ *)
(* Part B · Qinv 正性门（Qdiv 面→Qinv 面过桥；Set 层出口）                 *)
(* ============================================================ *)

(* B1 · Qdiv 正性：0 < c ⟹ 0 < 1/c（S02 q_arch_inv_pos 舞步去 nat 化）   *)
Lemma qbg_div_pos : forall c : Q, Qlt 0 c -> Qlt 0 (1 / c).
Proof.
  intro c. intro Hc.
  apply Qlt_shift_div_l; [ | ].
  - exact Hc.
  - setoid_replace (0 * c) with 0%Q by ring.
    reflexivity.
Qed.

(* B2 · Qinv 正性门（Set 面）：0 <T x ⟹ 0 <T Qinv x——Qfloor 证书入口    *)
Lemma qbg_Qinv_pos : forall x : Q, QltT 0 x -> QltT 0 (Qinv x).
Proof.
  intros x Hx.
  apply Qlt_to_QltT.
  rewrite (qbg_mult_inv x).
  apply qbg_div_pos. apply QltT_to_Qlt. exact Hx.
Qed.

(* ============================================================ *)
(* 主件 · 五同形 q_arch_geom 位直配 Corollary（槽②样板：S10:1675 位）      *)
(* ============================================================ *)
(* 语句面与 S03:383 q_arch_geom 逐字同形（sigT/NatLe/QleT' 全 Set 层）。   *)
(* 见证替换：Qarchimedean 不透明指标 → Qfloor 指标                         *)
(*   N := uabS4b_arch_N (Qinv (2B))；证书链：uabS4b_null_lt（B2 门供给     *)
(*   Qinv 正性）→ 1#(Pos.of_succ_nat N) < Qinv 2B →（A1 桥＋A2 右换形入    *)
(*   Qdiv 面）→ 1/(N+1) < 1/2B → Qinv_lt_contravar proj2 调和反演          *)
(*   → 2B < (N+1)#1 →（Qle_of_nat 单调）→ 2B ≤ (t+1)#1。                  *)
Corollary qbg_arch_geom_direct : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (Qlt_le_dec 0 B) as [Hpos | Hle].
  - (* 非退化支 0 < B：Qfloor 调和反演直配 *)
    assert (Htwo : Qlt 0 ((1 + 1)%Q * B)).
    { apply (Qmult_lt_0_compat (1 + 1)%Q B); [apply Q2_pos | exact Hpos]. }
    assert (HtwoT : QltT 0 ((1 + 1)%Q * B)) by (apply Qlt_to_QltT; exact Htwo).
    assert (Hinvpos : QltT 0 (Qinv ((1 + 1)%Q * B)))
      by (apply qbg_Qinv_pos; exact HtwoT).
    pose proof (uabS4b_null_lt (Qinv ((1 + 1)%Q * B)) Hinvpos) as Hfloor.
    pose proof (QltT_to_Qlt _ _ Hfloor) as HfloorP.
    assert (Hc1 : Qlt 0 (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1))
      by (unfold Qlt; simpl; lia).
    assert (Hkey : Qlt ((1 + 1)%Q * B)
                     (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1)).
    { apply (proj2 (Qinv_lt_contravar ((1 + 1)%Q * B)
              (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1)
              Htwo Hc1)).
      (* 证书 LHS 1#(Pos.of_succ_nat N) 与 /((N+1)#1) 定义性同形               *)
      (* （Qinv 规范形转换：Zpos(QDen x)#p ≡ 1#p），零换形直配收口；           *)
      (* Qdiv 面换形已由 A1 桥在 B2 门内消费                                   *)
      exact HfloorP. }
    exists (uabS4b_arch_N (Qinv ((1 + 1)%Q * B))).
    intros t Ht.
    apply Qle_to_QleT'.
    apply Qlt_le_weak.
    apply (Qlt_le_trans _ (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1) _).
    + exact Hkey.
    + apply Qle_of_nat. apply NatLe_drop in Ht. lia.
  - (* 退化支 B ≤ 0：N := 0 平凡承接（N10 定谳表并轨支） *)
    exists 0%nat.
    intros t Ht.
    apply Qle_to_QleT'.
    (* 两跳：(1+1)·B ≤ 0 且 0 ≤ (t+1)#1 *)
    apply (Qle_trans _ 0 _).
    + (* (1+1)·B ≤ 0：经 B·(1+1) ≤ 0·(1+1) == 0（Qmult 换序 ring＋右乘单调） *)
      apply (Qle_trans _ (0 * (1 + 1)%Q) _).
      * setoid_replace (Qmult (1 + 1)%Q B) with (B * (1 + 1)%Q) by ring.
        apply (Qmult_le_compat_r B 0 (1 + 1)%Q).
        -- exact Hle.
        -- apply Q2_nonneg.
      * apply qeq_le. ring.
    + (* 0 ≤ (t+1)#1：S02 同款 unfold-simpl-lia 舞步 *)
      unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* 证据采集（G2 打印面）                                                   *)
(* ============================================================ *)

Print Assumptions qbg_mult_inv.
Print Assumptions qbg_lt_eq_compat_r.
Print Assumptions qbg_ltT_eq_compat_r.
Print Assumptions qbg_div_pos.
Print Assumptions qbg_Qinv_pos.
Print Assumptions qbg_arch_geom_direct.
