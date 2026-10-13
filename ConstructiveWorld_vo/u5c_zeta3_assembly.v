(* ===================================================================== *)
(*  u5c_zeta3_assembly.v —— ζ(3) 供给链全链装配与见证化（ζ3Bridge 主件）     *)
(* ===================================================================== *)
(*  使命：按 ζ(2) 装配五层结构（载体层/头肢换算层/焊缝级联层/残位诚面/       *)
(*    全链装配主件）合拢 ζ(3) 供给链：缺口三件（zb3 尾界机 abl_z3_tail、     *)
(*    立方竞争与分离面 abl_z3_decay、三重积分承载机 abl_z3_itg_carrier）     *)
(*    与逐点控制面（abl_z3_pointwise）逐一对接，产出 ζ(3) 供给链 inhabited   *)
(*    终态语句：残位三证书（阈值 NatLe、逐点封顶证书 Hpw、裂项步档 Hws）     *)
(*    与 Hanson 证书给定 ⟹ 存在分母 d（Hanson lcm 的 Q 嵌入）使四层供给面   *)
(*    成立：0 ≤ d、d ≤ 3^(m+1)、Σ ≤ (1/4)(1/40)^m、d³·Σ < 1（立方整性       *)
(*    分离见证）。消解分工：①阈值肢＝NatLe 承载；②d ≤ 3^(m+1) 肢＝gapB     *)
(*    链消解（z2d_lcm_le_3pow + q_pow↔nat 幂桥）；③Σ ≤ (1/4)(1/40)^m 肢    *)
(*    ＝尾界机 zb3_ib_sep3_closed 消解（Hpw/Hws 双前提与残位诚面逐字同源     *)
(*    ·一份证书两处使用）；④d³·Σ<1 肢＝decay 件 zb3_dc_sep3_small 使用     *)
(*    （焊缝级联：前提 I×前提 II 同注）。                                   *)
(*  依赖：缓存根 S01_BaseRing（Id/And/NatLe 及双向桥）S02_CauchyComplete    *)
(*    （QleT'/QeqT/QltT 双向桥）S03_QExp（q_pow）HansonLcm（hl_lcm_upto）；  *)
(*    abl_z3_itg_carrier（zb3_term/zb3_Isum）abl_z3_decay                   *)
(*    （zb3_dc_sep3_small）abl_z3_tail（zb3_ib_sep3_closed/zb3_ia_W 族）    *)
(*    abl_z2_valbridge（z2v_C）u5c_zeta2_gapB（z2d_lcm_le_3pow）；          *)
(*    Stdlib：QArith ZArith Arith Lia。                                    *)
(*  构造性：语句面全 Set 层（sigT/And/NatLe/QleT'/QeqT/QltT）；主件证体＝   *)
(*    残面证书解构＋NatLe/qeqT 双桥换向＋sigT 见证填充（d := Hanson lcm     *)
(*    嵌入，Defined 透明供提取）＋头肢两件与焊缝级联件逐位填充；             *)
(*    零承认、零全局假设、零经典逻辑；文尾 Separate Extraction 与            *)
(*    Print Assumptions 全列取证。                                          *)
(*  对标：Beukers 1979 ζ(3) 级数估计（同 abl_z3_tail）；诚实面：残余接口   *)
(*    位三处（与装配前一致，均语句显式参数位，不因装配新增）。              *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_zeta3_assembly.v        *)
(*    （cpu_guard v3 包裹·串行≤1）；PA 10/10 Closed；提取 Obj.magic=0。      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import HansonLcm.
Require Import abl_z2_valbridge.
Require Import u5c_zeta2_gapB.
Require Import abl_z3_itg_carrier.
Require Import abl_z3_decay.
Require Import abl_z3_tail.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 载体层：分离分母嵌入与 ζ(3) 供给链四层面                              *)
(* ============================================================ *)

(* 分离分母 d 的规范嵌入：Hanson lcm(1..S m) 的 Q 像 *)
Definition u5c_z3_dmod (m : nat) : Q :=
  (Z.of_nat (hl_lcm_upto (Datatypes.S m)) # 1)%Q.

(* ζ(3) 供给链四层面（Set 层）：存在分母 d 使
   ① 0 ≤ d；② d ≤ 3^(m+1)（整性供给·前提 I）；③ 部分和尾界
   Σ_{k≤M} term(S m,k) ≤ (1/4)(1/40)^m（前提 II·全称 M）；
   ④ d³·Σ < 1（立方整性分离见证）。 *)
Definition u5c_z3_supply_chain (m M : nat) : Set :=
  sigT (fun d : Q =>
    And (QleT' 0 d)
      (And (QleT' d (q_pow 3 (Datatypes.S m)))
        (And (QleT' (zb3_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 40) m))
             (QltT (d * d * d * zb3_Isum (Datatypes.S m) M) 1)))).

(* ============================================================ *)
(* §1 头肢换算件（q_pow↔nat 幂桥 + 前提 I 供给链）                          *)
(* ============================================================ *)

(* 幂桥：q_pow 对底数 3 的求值与 nat 幂的 Q 像逐档相等 *)
Lemma u5c_z3_qpow3_eq : forall k : nat,
  q_pow 3 k == (Z.of_nat (3 ^ k) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow Nat.pow]. rewrite IH.
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
    rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* 头肢①：分母嵌入非负 *)
Theorem u5c_z3_head_d_ge0 : forall m : nat, QleT' 0 (u5c_z3_dmod m).
Proof.
  intro m. unfold u5c_z3_dmod.
  apply Qle_to_QleT'. exact (zb2gb_natQ_ge0 (hl_lcm_upto (Datatypes.S m))).
Qed.

(* 头肢②（前提 I 供给）：Hanson 证书 ⟹ d ≤ 3^(m+1)。 *)
Theorem u5c_z3_head_d_bound : forall m : nat,
  (z2v_C (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QleT' (u5c_z3_dmod m) (q_pow 3 (Datatypes.S m)).
Proof.
  intros m HC.
  assert (H1 : (1 <= Datatypes.S m)%nat) by lia.
  pose proof (z2d_lcm_le_3pow (Datatypes.S m) H1 HC) as Hq.
  apply Qle_to_QleT'.
  apply (Qle_trans _ ((Z.of_nat (3 ^ Datatypes.S m) # 1)%Q) _).
  - exact (QleT'_to_Qle _ _ Hq).
  - rewrite u5c_z3_qpow3_eq. apply Qle_refl.
Qed.

(* ============================================================ *)
(* §2 焊缝级联件（前提 I×前提 II 同注 → 分离主件使用）                       *)
(*    焊一：尾界机终句三参实例化（m/M/5≤m/Hpw/Hws）得前提 II；              *)
(*    焊二：gapB 链 + 幂桥得前提 I；两前提齐注则 decay 塔件                 *)
(*    zb3_dc_sep3_small 逐字导出 d³·Σ < 1。                              *)
(* ============================================================ *)

Theorem u5c_z3_weld_cascade : forall (m M : nat),
  (5 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb3_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 8) * q_pow (1 # 40) m)) ->
  (forall J' : nat, zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J') ->
  (z2v_C (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat ->
  QltT (u5c_z3_dmod m * u5c_z3_dmod m * u5c_z3_dmod m
        * zb3_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M Hm Hpw Hws HC.
  pose proof (zb3_ib_sep3_closed m M Hm Hpw Hws) as HII.
  pose proof (u5c_z3_head_d_bound m HC) as HI.
  exact (zb3_dc_sep3_small m M (u5c_z3_dmod m) Hm
           (u5c_z3_head_d_ge0 m) HI HII).
Qed.

(* ============================================================ *)
(* §3 残位诚面（三证书＋Hanson 证书·显式参数位·Set 承载）                    *)
(* ============================================================ *)

Definition u5c_z3_assembly_slot (m M : nat) : Set :=
  And (NatLe 5 m)
    (And (forall j : nat, (j <= m * m + 2 * m)%nat ->
            QleT' (zb3_term (Datatypes.S m) j
                   * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
                  ((1 # 8) * q_pow (1 # 40) m))
      (And (forall J' : nat,
              QeqT (zb3_ia_Wsum (Datatypes.S J'))
                   (zb3_ia_Wsum J' + zb3_ia_W J'))
        (NatLe (z2v_C (Datatypes.S m)) (3 ^ (Datatypes.S m))))).

(* ============================================================ *)
(* §4 全链装配主件（使命语句）：残位证书给定 ⟹ ζ(3) 供给链 inhabited        *)
(*    证体＝残面证书解构＋NatLe/qeqT 双桥换向＋sigT 见证填充（d:=嵌入）      *)
(*    ＋头肢两件/焊一/焊四级联逐位填充。                                    *)
(* ============================================================ *)

Theorem u5c_zeta3_assembly : forall (m M : nat),
  u5c_z3_assembly_slot m M -> u5c_z3_supply_chain m M.
Proof.
  intros m M Hs.
  unfold u5c_z3_assembly_slot in Hs.
  destruct Hs as [Hm5 [Hpw [Hws HM2]]].
  pose proof (NatLe_drop _ _ Hm5) as Hm.
  pose proof (NatLe_drop _ _ HM2) as HC.
  assert (Hws' : forall J' : nat,
            zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J').
  { intro J'. apply qeqT_imp_qeq. apply Hws. }
  assert (HII : QleT' (zb3_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 40) m))
    by exact (zb3_ib_sep3_closed m M Hm Hpw Hws').
  exists (u5c_z3_dmod m).
  split.
  - (* ① 0 ≤ d：头肢① *)
    exact (u5c_z3_head_d_ge0 m).
  - split.
    + (* ② d ≤ 3^(m+1)：焊二（gapB 链 + 幂桥换形） *)
      exact (u5c_z3_head_d_bound m HC).
    + split.
      * (* ③ 尾界 Σ ≤ (1/4)(1/40)^m：焊一（尾界机三参实例化） *)
        exact HII.
      * (* ④ d³·Σ < 1：焊缝级联（sep3_small 使用） *)
        exact (zb3_dc_sep3_small m M (u5c_z3_dmod m) Hm
                 (u5c_z3_head_d_ge0 m) (u5c_z3_head_d_bound m HC) HII).
Defined.

(* ============================================================ *)
(* §5 数值锚（计算链判定件·辅助面豁免）                                    *)
(* ============================================================ *)

(* 分母锚：dmod 0 = lcm(1) = 1、dmod 2 = lcm(1,2,3) = 6 *)
Lemma u5c_z3_dmod_0_anchor : u5c_z3_dmod 0 == (1 # 1).
Proof. vm_compute. reflexivity. Qed.

Lemma u5c_z3_dmod_2_anchor : u5c_z3_dmod 2 == (6 # 1).
Proof. vm_compute. reflexivity. Qed.

(* 供给链示例锚：阈值与权重在 m = 5 处的数值面（(1/8)(1/40)^5 与
   (1/4)(1/40)^5 的 Qcompare 判定） *)
Lemma u5c_z3_weight_5_anchor : QltT ((1 # 8) * q_pow (1 # 40) 5)
                                    ((1 # 4) * q_pow (1 # 40) 5).
Proof. exact (id_refl (A:=bool) (x:=Qlt_bool _ _)). Qed.

(* ============================================================ *)
(* §6 提取与假设审计（零全局假设复核）                                     *)
(* ============================================================ *)

Separate Extraction u5c_zeta3_assembly u5c_z3_dmod u5c_z3_head_d_bound
  zb3_term zb3_Isum zb3_ia_W.

Print Assumptions u5c_z3_dmod.
Print Assumptions u5c_z3_supply_chain.
Print Assumptions u5c_z3_qpow3_eq.
Print Assumptions u5c_z3_head_d_ge0.
Print Assumptions u5c_z3_head_d_bound.
Print Assumptions u5c_z3_weld_cascade.
Print Assumptions u5c_zeta3_assembly.
Print Assumptions u5c_z3_dmod_0_anchor.
Print Assumptions u5c_z3_dmod_2_anchor.
Print Assumptions u5c_z3_weight_5_anchor.
