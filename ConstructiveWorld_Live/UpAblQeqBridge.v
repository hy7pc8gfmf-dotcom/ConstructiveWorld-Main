(* ============================================================ *)
(* ToyR 玩具证替换件 —— T267 台账席 战役包AB（tier2 十八批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   qbg_ltT_eq_compat_r（原 L70，5 句玩具证）                            *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblQeqBridge.v —— Q 层 Qeq 右换形＋Qmult_inv 桥接引理件              *)
(*                                                                *)
(* 使命：补齐 Q 层 Qeq 右换形与 Qmult_inv 两类桥接引理，并为五处同形      *)
(*   q_arch_geom 调用点提供无 Qarchimedean 的直接供给。                   *)
(* 构造性注记：主件 qbg_arch_geom_direct 全 Set 层（sigT/NatLe/QleT'，    *)
(*   与 S03_QExp 之 q_arch_geom 逐字同形）；qbg_Qinv_pos/                 *)
(*   qbg_ltT_eq_compat_r 亦 Set 面。qbg_mult_inv/qbg_lt_eq_compat_r/      *)
(*   qbg_div_pos 为 Qeq/Qlt 序面辅助引理（同 S02 库内序面辅助件           *)
(*   体例，供下游局部链复用），全部构造证明，不落 Set 层语句；             *)
(*   零承认；全件 Qed 闭合。                                              *)
(*                                                                *)
(* 动机（两处阻断，逐条对应）：                                            *)
(*   阻断一：Qinv 的三支符号 match 阻断定义性换形（Qinv x 的分子          *)
(*     符号分支使 Qmake 互换拒绝转换）——桥接引理 A1 qbg_mult_inv          *)
(*     以 Qdiv 展开＋Qmult_1_l 具名（将 S02 的内联步骤命名），            *)
(*     正性引理 B2 以之绕开 match 的逐支展开；                            *)
(*   阻断二：S02 qltT_eq_compat_l 仅左向——桥接引理 A2/A3 补               *)
(*     右向换形（Qlt Prop 基座＋QltT Set 基座对偶）。                     *)
(*                                                                *)
(* 见证构造：五处同形 q_arch_geom 调用点的供给——                          *)
(*   N := uabS4b_arch_N (Qinv (2B))（Qfloor 指标，以 uabS4b_null_lt       *)
(*   为前提），调和反演 Qinv_lt_contravar proj2；退化支（B ≤ 0）          *)
(*   N := 0 平凡承接。标样取最浅调用点 sc_sin_partial_cauchy_bounded，    *)
(*   其余四处同形照此模板。                                               *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全部 Export）＋                *)
(*   UpAblAbsSumLeB2（S4B Qfloor 谱系件）。                               *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.

(* ============================================================ *)
(* §0 · 库内符号核验（签名不符即编译失败）                                  *)
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
(* §A · 两桥接引理（补 Qeq 右换形与 Qmult_inv 之缺）                        *)
(* ============================================================ *)

(* A1 · Qmult_inv 桥接引理：Qinv–Qdiv 关系具名（Qdiv x y := x·Qinv y 展开， *)
(*      Qmult_1_l 具名；绕开 Qinv 符号 match 的定义性换形阻断）            *)
Lemma qbg_mult_inv : forall x : Q, Qinv x == 1 / x.
Proof.
  intro x. unfold Qdiv. symmetry. apply Qmult_1_l.
Qed.

(* A2 · Qeq 右换形（Qlt 基座）：右支 Qeq 换形在 Qlt 中自由通过            *)
Lemma qbg_lt_eq_compat_r : forall a x y : Q, x == y -> a < x -> a < y.
Proof.
  intros a x y Hxy Hlt. rewrite <- Hxy. exact Hlt.
Qed.

(* A3 · Qeq 右换形（QltT Set 基座）：与 S02 qltT_eq_compat_l 左向件对偶   *)
Lemma qbg_ltT_eq_compat_r : forall a x y : Q, x == y -> QltT a x -> QltT a y.
Proof.
  intros a x y Hxy H.
  apply Qlt_to_QltT.
  apply (qbg_lt_eq_compat_r a x y Hxy).
  apply QltT_to_Qlt.
  exact H.
Qed.

(* ============================================================ *)
(* §B · Qinv 正性引理（Qdiv 面→Qinv 面转换；Set 层出口）                   *)
(* ============================================================ *)

(* B1 · Qdiv 正性：0 < c ⟹ 0 < 1/c（S02 q_arch_inv_pos 步骤去 nat 化）   *)
Lemma qbg_div_pos : forall c : Q, Qlt 0 c -> Qlt 0 (1 / c).
Proof.
  intro c. intro Hc.
  apply Qlt_shift_div_l; [ | ].
  - exact Hc.
  - setoid_replace (0 * c) with 0%Q by ring.
    reflexivity.
Qed.

(* B2 · Qinv 正性引理（Set 面）：0 <T x ⟹ 0 <T Qinv x——Qfloor 供给入口    *)
Lemma qbg_Qinv_pos : forall x : Q, QltT 0 x -> QltT 0 (Qinv x).
Proof.
  intros x Hx.
  apply Qlt_to_QltT.
  rewrite (qbg_mult_inv x).
  apply qbg_div_pos. apply QltT_to_Qlt. exact Hx.
Qed.

(* ============================================================ *)
(* 主件 · 五同形 q_arch_geom 调用点供给 Corollary（样板：sc_sin_partial_cauchy_bounded） *)
(* ============================================================ *)
(* 语句面与 S03_QExp 之 q_arch_geom 逐字同形（sigT/NatLe/QleT' 全 Set 层）。 *)
(* 见证替换：Qarchimedean 不透明指标 → Qfloor 指标                         *)
(*   N := uabS4b_arch_N (Qinv (2B))；前提链：uabS4b_null_lt（B2 引理供给   *)
(*   Qinv 正性）→ 1#(Pos.of_succ_nat N) < Qinv 2B →（A1 引理＋A2 右换形入  *)
(*   Qdiv 面）→ 1/(N+1) < 1/2B → Qinv_lt_contravar proj2 调和反演          *)
(*   → 2B < (N+1)#1 →（Qle_of_nat 单调）→ 2B ≤ (t+1)#1。                  *)
Corollary qbg_arch_geom_direct : forall B : Q,
  sigT (fun N : nat => forall t : nat, NatLe N t ->
    QleT' (Qmult (1 + 1)%Q B) (Z.of_nat (t + 1) # 1)).
Proof.
  intro B.
  destruct (Qlt_le_dec 0 B) as [Hpos | Hle].
  - (* 情形 0 < B：Qfloor 调和反演供给 *)
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
      (* 前提左端 1#(Pos.of_succ_nat N) 与 1/((N+1)#1) 定义性同形              *)
      (* （Qinv 规范形转换：Zpos(QDen x)#p ≡ 1#p），零换形直接收尾；           *)
      (* Qdiv 面换形已由 A1 引理在 B2 引理中完成                               *)
      exact HfloorP. }
    exists (uabS4b_arch_N (Qinv ((1 + 1)%Q * B))).
    intros t Ht.
    apply Qle_to_QleT'.
    apply Qlt_le_weak.
    apply (Qlt_le_trans _ (Z.of_nat (Datatypes.S (uabS4b_arch_N (Qinv ((1 + 1)%Q * B)))) # 1) _).
    + exact Hkey.
    + apply Qle_of_nat. apply NatLe_drop in Ht. lia.
  - (* 情形 B ≤ 0：N := 0 平凡承接 *)
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
    + (* 0 ≤ (t+1)#1：与 S02 同款的 unfold-simpl-lia 步骤 *)
      unfold Qle. simpl. lia.
Qed.

(* ============================================================ *)
(* 假设审计：以下各件 Print Assumptions 均为 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions qbg_mult_inv.
Print Assumptions qbg_lt_eq_compat_r.
Print Assumptions qbg_ltT_eq_compat_r.
Print Assumptions qbg_div_pos.
Print Assumptions qbg_Qinv_pos.
Print Assumptions qbg_arch_geom_direct.
