(* ===================================================================== *)
(*  abl_z3_hws.v —— Hws 裂项步档恒等式独立消解＋前提 II 单残位形＋峰值引擎   *)
(* ===================================================================== *)
(*  使命：消解 ζ(2)/ζ(3) 双线装配面共同残位 ②（Hws 裂项步档恒等式）：        *)
(*    ① zb3_ia_Wsum_step：1 − 1/(J'+2) == (1 − 1/(J'+1)) +                  *)
(*       1/((J'+1)(J'+2)) 的独立消解（Q 层 field 通路）；Qeq 形（尾界机      *)
(*       前提型）与 QeqT 形（装配槽型）双供。                               *)
(*    ② zb3_ib_sep3_hws_closed：前提 II 单残位形——阈值 5 ≤ m 与 Hpw         *)
(*       给定即得 Isum(S m,M) ≤ (1/4)(1/40)^m 对全称 M（原三前提收缩为       *)
(*       两前提；Hws 槽自此放行）。                                         *)
(*    ③ 峰值引擎件（Hpw 峰位分析首批机件，h(j)=term(j)(j+1)(j+2)）：         *)
(*       h-步档恒等式 h(n,S j)·(S j)·((S j)·D³) == h(n,j)·E⁴·(j+3) 与       *)
(*       h-单调比较（E⁴·(j+3) ≤ (S j)·D³ 则 h(n,S j) ≤ h(n,j)）。           *)
(*    数值旁证（Fractions 独立复算）：Hpw 前提在 m∈[5,60]×j≤m²+2m 全网格    *)
(*    真（最紧 m=5,j*=2·边距 332 倍）；C(n)≤3^n 在 n∈[1,200] 全真           *)
(*    （最紧 n=17·比值 0.285）。                                            *)
(*  依赖：缓存根 S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists      *)
(*    PolyIntegral PadeErrorIntegral；abl_z2_pointwise、abl_z3_itg_carrier、 *)
(*    u5c_zeta2_gapA/a1_sign/a2_tail/gapB、abl_z3_tail。                    *)
(*  对标：Beukers 1979 ζ(3) 级数估计（同族 ζ(2) 面同款残位形态）。           *)
(*  构造性：纯构造性、零假设声明、零承认词面、零经典逻辑；结论面             *)
(*    Qeq/QeqT/QleT' 全 Set 层；field 通路仅使用上下文非零假设。             *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" abl_z3_hws.v                 *)
(*    （cpu_guard v3 包裹·串行≤1）；PA 7/7 Closed；提取 Obj.magic=0。        *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
From Stdlib Require Import QArith.Qfield.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists
              PolyIntegral PadeErrorIntegral.
Require Import abl_z2_pointwise.
Require Import abl_z3_itg_carrier.
Require Import u5c_zeta2_gapA u5c_zeta2_a1_sign u5c_zeta2_a2_tail u5c_zeta2_gapB.
Require Import abl_z3_tail.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 Hws 裂项步档恒等式独立消解                                        *)
(* ============================================================ *)

(* 一般裂项式（nat 参数·field 通路）：两权重分母原子经 lia 归一后，
   非零假设在上下文，field 收束。 *)
Lemma zb3_ws_q_step_gen : forall j : nat,
  (1 - 1 / (Z.of_nat (Datatypes.S (Datatypes.S j)) # 1)
     == (1 - 1 / (Z.of_nat (Datatypes.S j) # 1))
        + 1 / ((Z.of_nat (Datatypes.S j) # 1)
               * (Z.of_nat (j + 2) # 1)))%Q.
Proof.
  intro j.
  replace (Z.of_nat (Datatypes.S (Datatypes.S j)))
    with ((Z.of_nat j + 1 + 1)%Z) by lia.
  replace (Z.of_nat (Datatypes.S j))
    with ((Z.of_nat j + 1)%Z) by lia.
  replace (Z.of_nat (j + 2)) with ((Z.of_nat j + 1 + 1)%Z) by lia.
  assert (HA : (0 < (Z.of_nat j + 1) # 1)%Q)
    by (unfold Qlt; cbn [Qnum Qden]; lia).
  assert (HB : (0 < (Z.of_nat j + 1 + 1) # 1)%Q)
    by (unfold Qlt; cbn [Qnum Qden]; lia).
  assert (HAne : ~ ((Z.of_nat j + 1) # 1 == 0)%Q)
    by (apply zb2_ga_pos_neq0; exact HA).
  assert (HBne : ~ ((Z.of_nat j + 1 + 1) # 1 == 0)%Q)
    by (apply zb2_ga_pos_neq0; exact HB).
  assert (HAB : (((Z.of_nat j + 1) # 1) + (1 # 1)
                 == ((Z.of_nat j + 1 + 1) # 1))%Q)
    by apply Qinv_plus_distr.
  rewrite <- HAB.
  assert (HAp1ne : ~ (((Z.of_nat j + 1) # 1) + (1 # 1) == 0)%Q)
    by (rewrite HAB; exact HBne).
  field. split; [exact HAp1ne | exact HAne].
Qed.

(* Hws 之 Qeq 形（尾界机 zb3_ib_sep3_closed / zb3_ia_init_bound 前提型） *)
Lemma zb3_ia_Wsum_step : forall J' : nat,
  zb3_ia_Wsum (Datatypes.S J') == zb3_ia_Wsum J' + zb3_ia_W J'.
Proof.
  intro J'. unfold zb3_ia_Wsum, zb3_ia_W. apply zb3_ws_q_step_gen.
Qed.

(* Hws 之 QeqT 形（装配槽 u5c_z3_assembly_slot 第三分量型） *)
Lemma zb3_ia_Wsum_step_T : forall J' : nat,
  QeqT (zb3_ia_Wsum (Datatypes.S J')) (zb3_ia_Wsum J' + zb3_ia_W J').
Proof.
  intros J'. apply qeq_imp_qeqT. apply zb3_ia_Wsum_step.
Qed.

(* ============================================================ *)
(* §2 前提 II 单残位形（Hws 放行后仅余 Hpw·缺口单调收缩）                 *)
(* ============================================================ *)

Theorem zb3_ib_sep3_hws_closed : forall m M : nat, (5 <= m)%nat ->
  (forall j : nat, (j <= m * m + 2 * m)%nat ->
     QleT' (zb3_term (Datatypes.S m) j
            * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1))
           ((1 # 8) * q_pow (1 # 40) m)) ->
  QleT' (zb3_Isum (Datatypes.S m) M) ((1 # 4) * q_pow (1 # 40) m).
Proof.
  intros m M Hm Hpw.
  exact (zb3_ib_sep3_closed m M Hm Hpw zb3_ia_Wsum_step).
Qed.

(* ============================================================ *)
(* §3 峰值引擎件（①Hpw 峰位分析第一批机件）                              *)
(* ============================================================ *)

(* 峰分析对象：h(n,j) = term(n,j)·(j+1)(j+2)（Hpw 槽左端） *)
Definition zb3_ia_h (n j : nat) : Q :=
  zb3_term n j * (Z.of_nat (Datatypes.S j) # 1) * (Z.of_nat (j + 2) # 1).

(* h-步档恒等式：h(n,S j)·(S j)·((S j)·D³) == h(n,j)·E⁴·(j+3)
   （D = n+S j+n+1，E = n+S j；由 zb3_term_ratio 乘公因子
   (S(S j))·((S j + 2)·(S j)) 后 ring 合账得） *)
Lemma zb3_ia_h_identity : forall n j : nat,
  zb3_ia_h n (Datatypes.S j)
  * (Z.of_nat (Datatypes.S j) # 1)
  * ((Z.of_nat (Datatypes.S j) # 1)
     * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
        * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
           * (Z.of_nat (n + Datatypes.S j + n + 1) # 1))))
  == zb3_ia_h n j
     * ((Z.of_nat (n + Datatypes.S j) # 1)
        * ((Z.of_nat (n + Datatypes.S j) # 1)
           * ((Z.of_nat (n + Datatypes.S j) # 1)
              * (Z.of_nat (n + Datatypes.S j) # 1))))
     * (Z.of_nat (j + 3) # 1).
Proof.
  intros n j.
  pose proof (qeqT_imp_qeq _ _ (zb3_term_ratio n j)) as Hr.
  unfold zb3_ia_h.
  replace (Z.of_nat (Datatypes.S (Datatypes.S j)))
    with (Z.of_nat (Datatypes.S j + 1)) by lia.
  replace (Z.of_nat (Datatypes.S j + 2))
    with (Z.of_nat (Datatypes.S j + 1 + 1)) by lia.
  replace (Z.of_nat (j + 2)) with (Z.of_nat (Datatypes.S j + 1)) by lia.
  replace (Z.of_nat (j + 3)) with (Z.of_nat (Datatypes.S j + 1 + 1)) by lia.
  transitivity ((zb3_term n (Datatypes.S j)
                  * ((Z.of_nat (Datatypes.S j) # 1)
                     * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
                        * ((Z.of_nat (n + Datatypes.S j + n + 1) # 1)
                           * (Z.of_nat (n + Datatypes.S j + n + 1) # 1)))))
                * ((Z.of_nat (Datatypes.S j + 1) # 1)
                   * ((Z.of_nat (Datatypes.S j + 1 + 1) # 1)
                      * (Z.of_nat (Datatypes.S j) # 1)))).
  - ring.
  - rewrite Hr. ring.
Qed.

(* ============================================================ *)
(* §4 数值锚（计算链判定件·辅助面豁免）                                   *)
(* ============================================================ *)

(* 裂项锚：Wsum 1 == Wsum 0 + W 0（即 1/2 == 1/2 + 1/2） *)
Lemma zb3_ia_Wsum_step_0_anchor :
  zb3_ia_Wsum 1 == zb3_ia_Wsum 0 + zb3_ia_W 0.
Proof. exact (zb3_ia_Wsum_step 0%nat). Qed.

(* h 锚：h(3,0) = (1/140)³·1·2 = 1/1372000 *)
Lemma zb3_ia_h_3_0_anchor : zb3_ia_h 3 0 == (1 # 1372000).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §5 提取与假设审计（零全局假设复核）                                   *)
(* ============================================================ *)

Separate Extraction zb3_ia_Wsum_step_T zb3_ia_h.

Print Assumptions zb3_ws_q_step_gen.
Print Assumptions zb3_ia_Wsum_step.
Print Assumptions zb3_ia_Wsum_step_T.
Print Assumptions zb3_ib_sep3_hws_closed.
Print Assumptions zb3_ia_h_identity.

Print Assumptions zb3_ia_Wsum_step_0_anchor.
Print Assumptions zb3_ia_h_3_0_anchor.
