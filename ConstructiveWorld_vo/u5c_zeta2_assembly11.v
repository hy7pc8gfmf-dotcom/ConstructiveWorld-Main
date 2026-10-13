(* ===================================================================== *)
(*  u5c_zeta2_assembly11.v —— ζ(2) 供给链全链装配·θ=1/11 档重铸件           *)
(* ===================================================================== *)
(*  使命：装配面 1/11 重铸位三（上游件＝abl_zeta2_pool u5c_zeta2_assembly.v  *)
(*    1/10 档绿正本，池内 born 重铸）。按 ln2 装配五层结构合拢 ζ(2) 供给链   *)
(*    （1/11 档）：产出终态语句 u5c_zeta2_assembly：残位四证书（阈值 NatLe、 *)
(*    逐点封顶证书 Hpw、裂项步档 Hws、Hanson 熵上界 M2′）给定 ⟹ 存在分母 d  *)
(*    （Hanson lcm 的 Q 嵌入）使四层供给面成立：0 ≤ d、d ≤ 3^(m+1)、         *)
(*    Σ ≤ (1/4)(1/11)^m、d²·Σ < 1（整性分离见证）。消解分工：①阈值肢＝      *)
(*    NatLe 承载；②d ≤ 3^(m+1) 肢＝gapB 链+幂桥；③Σ ≤ (1/4)(1/11)^m 肢＝   *)
(*    a2_tail11 DOCK 终句 zb2_ib_sep2_closed 五参实例化（Hpw/Hws 双前提     *)
(*    与 a1_sign11 终形逐字同源·一份证书两处使用）；④d²·Σ<1 肢＝锐化件     *)
(*    dmw2_dc_sep_small 使用（m≥5 档·锐化前提 II′=(1/4)(1/11)^m 显式在句    *)
(*    ——本肢自 zb2_dc_sep_small（m≥8 档·1/10）改接锐化档）。                *)
(*    改档账：(1#10) → (1#11)（supply_chain ③肢/budget_slot/weld_cascade    *)
(*    与 assembly_slot 的 Hpw 前提形）；预算槽终态 zb2_ia_C1+(1#11)≤1#4     *)
(*    （C1=1/11·2/11≤1/4·独立复算✓）；分离面改档 zb2_dc_sep_small →        *)
(*    dmw2_dc_sep_small（签名零改动；装配 8≤m 严格强于 m≥5 判定档，窗位     *)
(*    不变）；依赖改档 abl_z2_decay→abl_dmw2_sharpen_decay、a1_sign/       *)
(*    a2_tail→11 档件；阈值肢/Hpw 窗位 8≤m 维持上游件值。                  *)
(*  依赖：缓存根 S01_BaseRing、S02_CauchyComplete、S03_QExp、HansonLcm；     *)
(*    abl_z2_itg_carrier、abl_z2_valbridge（z2v_C）；u5c_zeta2_gapB；       *)
(*    abl_dmw2_sharpen_decay；u5c_zeta2_a1_sign11、u5c_zeta2_a2_tail11；    *)
(*    Stdlib QArith/ZArith/Arith/Lia/Setoid。                               *)
(*  对标：Beukers 1979 级数估计（同上游件）；锐化依据＝θ=1/11 证书           *)
(*    （竞争判定 m≥5）；装配层阈值 8≤m 维持。                               *)
(*  构造性：语句面全 Set 层；Hpw/Hws 以显式命名前提在句（PA 仍 Closed）；    *)
(*    主件证体＝残面四证书解构＋双桥换向＋sigT 见证填充＋逐位焊装；          *)
(*    零承认、零全局假设、零经典逻辑；文尾 Separate Extraction 与            *)
(*    Print Assumptions 全列取证。                                          *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_zeta2_assembly11.v      *)
(*    （cpu_guard v3 包裹·串行≤1）；PA 8/8 Closed；提取 Obj.magic=0。        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm.
Require Import abl_z2_itg_carrier.
Require Import abl_dmw2_sharpen_decay.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_a1_sign11.
Require Import u5c_zeta2_a2_tail11.
Require Import u5c_zeta2_gapB.

(* gapB 件尾曾就地关闭 Q_scope（混域记法坑卡）——本件装配面统一重开，
   Q 层语句全局书写、nat 处局部 %nat 标注 *)
Open Scope Q_scope.

(* ============================================================ *)
(* §0 载体层：分离分母嵌入与 ζ(2) 供给链四层面                              *)
(* ============================================================ *)

(* 分离分母 d 的规范嵌入：Hanson lcm(1..S m) 的 Q 像
   （与 gapB 终句 z2d_lcm_le_3pow 结论左端逐字同体） *)
Definition u5c_z2_dmod (m : nat) : Q :=
  (Z.of_nat (hl_lcm_upto (Datatypes.S m)) # 1)%Q.

(* ζ(2) 供给链四层面（Set 层）：存在分母 d 使
   ① 0 ≤ d；② d ≤ 3^(m+1)（整性供给·前提 I）；③ 部分和尾界
   Σ_{k≤M} term(S m,k) ≤ (1/4)(1/11)^m（前提 II·全称 M）；
   ④ d²·Σ < 1（整性分离见证）。 *)
Definition u5c_z2_supply_chain (m M : nat) : Set :=
  sigT (fun d : Q =>
    And (QleT' 0 d)
      (And (QleT' d (q_pow 3 (Datatypes.S m)))
        (And (QleT' (zb2_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 11) m))
             (QltT (d * d * zb2_Isum (Datatypes.S m) M) 1)))).

(* ============================================================ *)
(* §1 头肢换算件（q_pow↔nat 幂桥 + 前提 I 供给链）                          *)
(* ============================================================ *)

(* 幂桥：q_pow 对底数 3 的求值与 nat 幂的 Q 像逐档相等
   （Z2S02 回执 §三指派的装配切片份额·对 k 归纳） *)
Lemma u5c_z2_qpow3_eq : forall k : nat,
  q_pow 3 k == (Z.of_nat (3 ^ k) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
    rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 头肢①：分母嵌入非负（gapB 基础面为 Qle 形，经 Qle_to_QleT' 桥升 Set） *)
Theorem u5c_z2_head_d_ge0 : forall m : nat, QleT' 0 (u5c_z2_dmod m).
Proof.
  intro m. unfold u5c_z2_dmod.
  apply Qle_to_QleT'. exact (zb2gb_natQ_ge0 (hl_lcm_upto (Datatypes.S m))).
Qed.

(* 头肢②（前提 I 供给）：Hanson 熵上界证书 ⟹ d ≤ 3^(m+1)。
   换算链＝gapB 终句 z2d_lcm_le_3pow + 幂桥右端换形（Z2S02 §三入口指针
   的「Z.of_nat # 1 ↔ q_pow 3 桥接」档兑现）。 *)
Theorem u5c_z2_head_d_bound : forall m : nat,
  (z2v_C (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QleT' (u5c_z2_dmod m) (q_pow 3 (Datatypes.S m)).
Proof.
  intros m HC.
  assert (H1 : (1 <= Datatypes.S m)%nat) by lia.
  pose proof (z2d_lcm_le_3pow (Datatypes.S m) H1 HC) as Hq.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((Z.of_nat (3 ^ Datatypes.S m) # 1)%Q) _).
  - exact (QleT'_to_Qle _ _ Hq).
  - rewrite u5c_z2_qpow3_eq. apply Qle_refl.
Qed.

(* ============================================================ *)
(* §1·甲 预算挂钩件（a1/a2 合计预算面 Set 形登记·单发使用）                  *)
(* ============================================================ *)

Definition u5c_z2_budget_slot : Set := QleT' (zb2_ia_C1 + (1 # 11)) (1 # 4).

Theorem u5c_z2_budget_limb : u5c_z2_budget_slot.
Proof. apply Qle_to_QleT'. exact zb2_ib_C2_delivered. Qed.

(* ============================================================ *)
(* §2 焊缝级联件（前提 I×前提 II 同注 → 分离主件使用）                       *)
(*    焊一：a2_tail DOCK 终句五参实例化（m/M/8≤m/Hpw/Hws）得前提 II；       *)
(*    焊二：gapB 链 + 幂桥得前提 I；两前提齐注则 decay 塔件                 *)
(*    zb2_dc_sep_small 逐字导出 d²·Σ < 1。                                *)
(* ============================================================ *)

Theorem u5c_z2_weld_cascade : forall (m M : nat),
  (8 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb2_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 11) * q_pow (1 # 11) m)) ->
  (forall J' : nat, zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J') ->
  (z2v_C (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QltT (u5c_z2_dmod m * u5c_z2_dmod m * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M Hm Hpw Hws HC.
  pose proof (zb2_ib_sep2_closed m M Hm Hpw Hws) as HII.
  pose proof (u5c_z2_head_d_bound m HC) as HI.
  assert (Hm5 : (5 <= m)%nat) by lia.
  exact (dmw2_dc_sep_small m M (u5c_z2_dmod m) Hm5 (u5c_z2_head_d_ge0 m) HI HII).
Qed.

(* ============================================================ *)
(* §3 残位诚面（四证书显式参数位·Set 承载升级版）                           *)
(*    阈值与 M2′ 以 NatLe（S01 基座 Set 序面）承载；Hpw 沿 a1/a2 终形       *)
(*    逐字；Hws 较上游绿件升级为 QeqT Set 承载（内容逐字同源）。             *)
(* ============================================================ *)

Definition u5c_z2_assembly_slot (m M : nat) : Set :=
  And (NatLe 8 m)
    (And (forall j : nat, (j <= m * m + 2 * m)%nat ->
            QleT' (zb2_term (Datatypes.S m) j
                   * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
                  ((1 # 11) * q_pow (1 # 11) m))
      (And (forall J' : nat,
              QeqT (zb2_ia_Wsum (Datatypes.S J'))
                   (zb2_ia_Wsum J' + zb2_ia_W J'))
        (NatLe (z2v_C (Datatypes.S m)) (3 ^ (Datatypes.S m))))).

(* ============================================================ *)
(* §4 全链装配主件（使命语句）：残位四证书给定 ⟹ ζ(2) 供给链 inhabited      *)
(*    证体＝残面四证书解构＋NatLe/qeqT 双桥换向＋sigT 见证（d:=嵌入）       *)
(*    ＋头肢两件/焊一/焊四级联逐位填充。                                    *)
(* ============================================================ *)

Theorem u5c_zeta2_assembly : forall (m M : nat),
  u5c_z2_assembly_slot m M -> u5c_z2_supply_chain m M.
Proof.
  intros m M Hs.
  unfold u5c_z2_assembly_slot in Hs.
  destruct Hs as [Hm8 [Hpw [Hws HM2]]].
  pose proof (NatLe_drop _ _ Hm8) as Hm.
  pose proof (NatLe_drop _ _ HM2) as HC.
  assert (Hws' : forall J' : nat,
            zb2_ia_Wsum (Datatypes.S J') == zb2_ia_Wsum J' + zb2_ia_W J').
  { intro J'. apply qeqT_imp_qeq. apply Hws. }
  exists (u5c_z2_dmod m).
  split.
  - (* ① 0 ≤ d：头肢① *)
    exact (u5c_z2_head_d_ge0 m).
  - split.
    + (* ② d ≤ 3^(m+1)：焊二（gapB 链 + 幂桥换形） *)
      exact (u5c_z2_head_d_bound m HC).
    + split.
      * (* ③ 尾界 Σ ≤ (1/4)(1/11)^m：焊一（DOCK 终句五参实例化） *)
        exact (zb2_ib_sep2_closed m M Hm Hpw Hws').
      * (* ④ d²·Σ < 1：焊缝级联（sep_small 使用） *)
        exact (u5c_z2_weld_cascade m M Hm Hpw Hws' HC).
Defined.

(* ============================================================ *)
(* §5 提取与假设审计（零全局假设复核）                                      *)
(* ============================================================ *)

Separate Extraction u5c_zeta2_assembly u5c_z2_weld_cascade u5c_z2_head_d_bound.

Print Assumptions u5c_z2_dmod.
Print Assumptions u5c_z2_supply_chain.
Print Assumptions u5c_z2_qpow3_eq.
Print Assumptions u5c_z2_head_d_ge0.
Print Assumptions u5c_z2_head_d_bound.
Print Assumptions u5c_z2_budget_limb.
Print Assumptions u5c_z2_weld_cascade.
Print Assumptions u5c_zeta2_assembly.
