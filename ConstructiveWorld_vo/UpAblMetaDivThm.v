(* ==========================================================================)
   UpAblMetaDivThm.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：mtdc_mult_distr_r、mtdc_two、mtdc_inv2、mtdc_four、mtdc_le_one_four、mtdc_inv2_two、mtdc_inv2_four_two、mtdc_inv_wd、mtdc_ds2_scale。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
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
Require Export UpReqAlgebra.
Require Export UpReqConcMixSel.
Require Import UpAblP7_UMixSelect.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpReqUMixSelect.
Require Import UpAblMetaWorld3.
Require Import AttnDoeblin.
Require Import UpAblA2_LoInflation.
Require Import UpAblMetaEngine.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.

(* ================= §1 mtdc_mult_distr_r 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ===== §0 实例化消解与环形簿册桥 ===== *)
(* mtdc_mult_distr_r：Setoid distrib 字段一跳（comm+congr），                *)

Lemma mtdc_mult_distr_r : forall a b c : Real,
  req (mult (plus a b) c) (plus (mult a c) (mult b c)).
Proof.
  intros a b c.
  apply (req_trans _ (mult c (plus a b))).
  { exact (mult_comm (plus a b) c). }
  apply (req_trans _ (plus (mult c a) (mult c b))).
  { exact (distrib c a b). }
  exact (req_plus_compat (mult c a) (mult a c) (mult c b) (mult b c)
           (mult_comm c a) (mult_comm c b)).
Defined.

(* mtdc_inv2 证书统一取 req_two_pos（见头注证书同源注）。                     *)

Definition mtdc_two : Real := plus one one.
Definition mtdc_inv2 : Real := inv_pos mtdc_two req_two_pos.
Definition mtdc_four : Real := plus mtdc_two mtdc_two.

(* 出节签名（对照 LoInflation 变参序，与封存块 L1503 使用位同形）：           *)
(*   mtdc_lo_inflation lt_plus_compat_lt_le TV0 Htv0 budget Hbudget          *)
(*                     lo Hlo0 Hds1 Harch                                     *)

Section ConjBridge.

Variable lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable TV0 : Real.
Variable Htv0 : le zero TV0.
Variable budget : Real.
Variable Hbudget : lt zero budget.

Variable lo : Real.
Variable Hlo0 : lt zero lo.
Variable Hds1 : lt (mult lo lo) one.   (* δ* < 1：Doeblin 证书 *)

Variable Harch : forall x : Real, le zero x ->
  sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)).

Let Htwopos : lt zero mtdc_two := plus_positive one one one_pos one_pos.
Let Hfourpos : lt zero mtdc_four :=
  plus_positive mtdc_two mtdc_two Htwopos Htwopos.
Let inv4 := inv_pos mtdc_four Hfourpos.

Let loh := mult lo mtdc_inv2.
Let ds := mult lo lo.
Let ds2 := mult loh loh.
Let kap := req_minus one ds.
Let kap2 := req_minus one ds2.

Let Hds0 : lt zero ds := mult_positive lo lo Hlo0 Hlo0.
Let Hwb : lt zero (mult ds budget) :=
  mult_positive ds budget Hds0 Hbudget.
Let ub := mult TV0 (inv_pos (mult ds budget) Hwb).
(* 证书同源：inv_pos_pos 参数位取 req_two_pos（封存块 L1486-1490 同源，纯 δ） *)
Let Hlohalf0 : lt zero loh :=
  mult_positive lo mtdc_inv2 Hlo0 (inv_pos_pos mtdc_two req_two_pos).
Let Hds2_0 : lt zero ds2 := mult_positive loh loh Hlohalf0 Hlohalf0.
Let Hwb2 : lt zero (mult ds2 budget) :=
  mult_positive ds2 budget Hds2_0 Hbudget.
Let ub2 := mult TV0 (inv_pos (mult ds2 budget) Hwb2).


Lemma mtdc_le_one_four : le one mtdc_four.
Proof.
  apply (le_trans one (plus one one) mtdc_four).
  - exact (cmk_le_plus_r one one (lt_le_iff zero one (inl one_pos))).
  - exact (cmk_le_plus_r mtdc_two mtdc_two
             (le_id_l zero (plus zero zero) mtdc_two
                (req_sym _ _ (plus_zero zero))
                (le_plus_compat zero one zero one
                   (lt_le_iff zero one (inl one_pos))
                   (lt_le_iff zero one (inl one_pos))))).
Qed.


Lemma mtdc_inv2_two : req (mult mtdc_two mtdc_inv2) one.
Proof.
  exact (inv_pos_correct mtdc_two req_two_pos).
Qed.

Lemma mtdc_inv2_four_two : req (mult mtdc_inv2 mtdc_four) mtdc_two.
Proof.
  apply (req_trans _ (mult mtdc_four mtdc_inv2)).
  { exact (mult_comm mtdc_inv2 mtdc_four). }
  apply (req_trans _ (plus (mult mtdc_two mtdc_inv2)
                           (mult mtdc_two mtdc_inv2))).
  { exact (mtdc_mult_distr_r mtdc_two mtdc_two mtdc_inv2). }
  apply (req_trans _ (plus one one)).
  { exact (req_plus_compat (mult mtdc_two mtdc_inv2) one
                           (mult mtdc_two mtdc_inv2) one
             (inv_pos_correct mtdc_two req_two_pos)
             (inv_pos_correct mtdc_two req_two_pos)). }
  exact (req_refl (plus one one)).
Qed.

(*    mult_cancel_l→req_mult_cancel_l，id 链→req_trans＋cmk_mult_congr）---- *)

Lemma mtdc_inv_wd : forall (a b : Real) (Ha : lt zero a) (Hb : lt zero b),
  req a b -> req (inv_pos a Ha) (inv_pos b Hb).
Proof.
  intros a b Ha Hb Hab.
  apply (req_mult_cancel_l b (inv_pos a Ha) (inv_pos b Hb) Hb).
  exact (req_trans _ _ _
           (req_trans _ _ _
              (cmk_mult_congr_r (inv_pos a Ha) b a (req_sym _ _ Hab))
              (inv_pos_correct a Ha))
           (req_sym _ _ (inv_pos_correct b Hb))).
Qed.

(*    loi_ds2_scale 全链 H1-H6，id→req 机械换名，约 35 行零数学新内容） ---- *)

Lemma mtdc_ds2_scale : req (mult mtdc_four ds2) ds.
Proof.
  assert (H1 : req (mult mtdc_four loh) (mult lo mtdc_two)).
  { exact (req_trans _ _ _
             (mult_assoc mtdc_four lo mtdc_inv2)
             (req_trans _ _ _
                (req_mult_compat (mult mtdc_four lo) (mult lo mtdc_four)
                                 mtdc_inv2 mtdc_inv2
                   (mult_comm mtdc_four lo) (req_refl mtdc_inv2))
                (req_trans _ _ _
                   (req_sym _ _ (mult_assoc lo mtdc_four mtdc_inv2))
                   (cmk_mult_congr_l lo (mult mtdc_four mtdc_inv2) mtdc_two
                      (req_trans _ _ _ (mult_comm mtdc_four mtdc_inv2)
                                       mtdc_inv2_four_two))))). }
  assert (H2 : req (mult mtdc_four (mult loh loh))
                  (mult (mult mtdc_four loh) loh)).
  { exact (mult_assoc mtdc_four loh loh). }
  assert (H3 : req (mult (mult mtdc_four loh) loh)
                  (mult (mult lo mtdc_two) loh)).
  { exact (req_mult_compat (mult mtdc_four loh) (mult lo mtdc_two)
                           loh loh H1 (req_refl loh)). }
  assert (H4 : req (mult (mult lo mtdc_two) loh)
                  (mult (mult (mult lo mtdc_two) lo) mtdc_inv2)).
  { exact (mult_assoc (mult lo mtdc_two) lo mtdc_inv2). }
  assert (H5 : req (mult (mult (mult lo mtdc_two) lo) mtdc_inv2)
                  (mult (mult (mult lo lo) mtdc_two) mtdc_inv2)).
  { exact (req_trans _ _ _
             (req_mult_compat (mult (mult lo mtdc_two) lo)
                              (mult lo (mult mtdc_two lo))
                              mtdc_inv2 mtdc_inv2
                (req_sym _ _ (mult_assoc lo mtdc_two lo))
                (req_refl mtdc_inv2))
             (req_mult_compat (mult lo (mult mtdc_two lo))
                              (mult (mult lo lo) mtdc_two)
                              mtdc_inv2 mtdc_inv2
                (req_trans _ _ _
                   (cmk_mult_congr_l lo (mult mtdc_two lo) (mult lo mtdc_two)
                      (mult_comm mtdc_two lo))
                   (mult_assoc lo lo mtdc_two))
                (req_refl mtdc_inv2))). }
  assert (H6 : req (mult (mult (mult lo lo) mtdc_two) mtdc_inv2) ds).
  { exact (req_trans _ _ _
             (req_sym _ _ (mult_assoc (mult lo lo) mtdc_two mtdc_inv2))
             (req_trans _ _ _
                (cmk_mult_congr_l (mult lo lo) (mult mtdc_two mtdc_inv2) one
                   mtdc_inv2_two)
                (mult_one (mult lo lo)))). }
  exact (req_trans _ _ _ (req_trans _ _ _ (req_trans _ _ _ H2 H3) H4)
           (req_trans _ _ _ H5 H6)).
Qed.

(*    le_mult_compat_r→req_le_mult_compat_r） ---------- *)

Lemma mtdc_ds2_le_ds : le ds2 ds.
Proof.
  apply (le_trans ds2 (mult ds2 one) ds).
  - exact (le_id_r ds2 ds2 (mult ds2 one)
             (req_sym _ _ (mult_one ds2)) (le_refl ds2)).
  - apply (le_trans (mult ds2 one) (mult ds2 mtdc_four) ds).
    + exact (req_le_mult_compat_r ds2 one mtdc_four
               (lt_le_iff zero ds2 (inl Hds2_0)) mtdc_le_one_four).
    + exact (le_id_l (mult ds2 mtdc_four) ds ds
               (req_trans _ _ _ (mult_comm ds2 mtdc_four) mtdc_ds2_scale)
               (le_refl ds)).
Qed.


Lemma mtdc_ds2_lt_one : lt ds2 one.
Proof.
  exact (le_lt_trans ds2 ds one mtdc_ds2_le_ds Hds1).
Qed.

(*    inv_pos_mult_distr→req_inv_pos_mult_distr、loi_inv_wd→桩5、            *)
(*    ums_mult_one_l→cmk_mult_one_l，其余 Setoid 同名，约 40 行） ---------- *)

Lemma mtdc_ub2_quad : req ub2 (mult mtdc_four ub).
Proof.
  assert (Hsplit : req (mult ds budget)
                       (mult mtdc_four (mult ds2 budget))).
  { exact (req_trans _ _ _
             (req_mult_compat ds (mult mtdc_four ds2) budget budget
                (req_sym _ _ mtdc_ds2_scale) (req_refl budget))
             (req_sym _ _ (mult_assoc mtdc_four ds2 budget))). }
  assert (Hbinv : req (inv_pos (mult ds budget) Hwb)
                      (mult inv4 (inv_pos (mult ds2 budget) Hwb2))).
  { exact (req_trans _ _ _
             (mtdc_inv_wd (mult ds budget)
                          (mult mtdc_four (mult ds2 budget))
                          Hwb
                          (mult_positive mtdc_four (mult ds2 budget)
                             Hfourpos Hwb2)
                          Hsplit)
             (req_inv_pos_mult_distr mtdc_four (mult ds2 budget)
                                     Hfourpos Hwb2)). }
  assert (Hub' : req ub (mult inv4 ub2)).
  { exact (req_trans _ _ _
             (cmk_mult_congr_l TV0 (inv_pos (mult ds budget) Hwb)
                (mult inv4 (inv_pos (mult ds2 budget) Hwb2)) Hbinv)
             (req_trans _ _ _
                (mult_assoc TV0 inv4 (inv_pos (mult ds2 budget) Hwb2))
                (req_trans _ _ _
                   (req_mult_compat (mult TV0 inv4) (mult inv4 TV0)
                      (inv_pos (mult ds2 budget) Hwb2)
                      (inv_pos (mult ds2 budget) Hwb2)
                      (mult_comm TV0 inv4) (req_refl _))
                   (req_sym _ _ (mult_assoc inv4 TV0
                                   (inv_pos (mult ds2 budget) Hwb2)))))). }
  assert (Hfin : req (mult mtdc_four (mult inv4 ub2)) ub2).
  { exact (req_trans _ _ _
             (mult_assoc mtdc_four inv4 ub2)
             (req_trans _ _ _
                (req_mult_compat (mult mtdc_four inv4) one ub2 ub2
                   (inv_pos_correct mtdc_four Hfourpos) (req_refl ub2))
                (cmk_mult_one_l ub2))). }
  exact (req_sym _ _ (req_trans _ _ _
           (cmk_mult_congr_l mtdc_four ub (mult inv4 ub2) Hub') Hfin)).
Qed.

(* ---------- 桩10 主定理：膨胀律（G4 归一形：结论 leg3 取 ub2 归一形，          *)
(*    pow_tail 双实例化消解 cmk_pow_tail（Heqk 参数位 req 形：kap 定义性 req_refl）--- *)

Theorem mtdc_lo_inflation :
  sigT (fun k1 : nat =>
    sigT (fun k2 : nat =>
      And (lt (mult (cmk_r_pow kap k1) TV0) budget)
        (And (lt (mult (cmk_r_pow kap2 k2) TV0) budget)
             (lt (mult mtdc_four ub2) (cmk_scale k2 one))))).
Proof.
  assert (Hub : le zero ub).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds budget) Hwb))
             (mult TV0 (inv_pos (mult ds budget) Hwb))
             (req_sym _ _ (req_trans _ _ _
                (mult_comm zero (inv_pos (mult ds budget) Hwb))
                (mult_zero (inv_pos (mult ds budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds budget) Hwb)
                (lt_le_iff zero (inv_pos (mult ds budget) Hwb)
                             (inl (inv_pos_pos (mult ds budget) Hwb)))
                Htv0)). }
  assert (Hub2 : le zero ub2).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult ds2 budget) Hwb2))
             (mult TV0 (inv_pos (mult ds2 budget) Hwb2))
             (req_sym _ _ (req_trans _ _ _
                (mult_comm zero (inv_pos (mult ds2 budget) Hwb2))
                (mult_zero (inv_pos (mult ds2 budget) Hwb2))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult ds2 budget) Hwb2)
                (lt_le_iff zero (inv_pos (mult ds2 budget) Hwb2)
                             (inl (inv_pos_pos (mult ds2 budget) Hwb2)))
                Htv0)). }
  (* 归一形非负肢：0 ≤ 4·ub2（4·ub2 ≡ TV0·(4·inv(ds2·budget)) 换形后同模） *)
  assert (Hub4 : le zero (mult mtdc_four ub2)).
  { assert (HX2p : lt zero (inv_pos (mult ds2 budget) Hwb2))
      by exact (inv_pos_pos (mult ds2 budget) Hwb2).
    assert (Hchain : req (mult mtdc_four ub2)
                         (mult TV0 (mult mtdc_four
                                       (inv_pos (mult ds2 budget) Hwb2)))).
    { exact (req_trans _ _ _
               (mult_assoc mtdc_four TV0
                  (inv_pos (mult ds2 budget) Hwb2))
               (req_trans _ _ _
                  (cmk_mult_congr_r (inv_pos (mult ds2 budget) Hwb2)
                     (mult mtdc_four TV0) (mult TV0 mtdc_four)
                     (mult_comm mtdc_four TV0))
                  (req_sym _ _ (mult_assoc TV0 mtdc_four
                                  (inv_pos (mult ds2 budget) Hwb2))))). }
    assert (Hub4' : le zero
               (mult TV0 (mult mtdc_four
                             (inv_pos (mult ds2 budget) Hwb2)))).
    { exact (le_id_l zero
               (mult zero (mult mtdc_four
                              (inv_pos (mult ds2 budget) Hwb2)))
               (mult TV0 (mult mtdc_four
                             (inv_pos (mult ds2 budget) Hwb2)))
               (req_sym _ _ (req_trans _ _ _
                  (mult_comm zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))
                  (mult_zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))))
               (le_mult_compat_weak zero TV0
                  (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2))
                  (lt_le_iff zero
                     (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2))
                     (inl (mult_positive mtdc_four
                            (inv_pos (mult ds2 budget) Hwb2)
                            Hfourpos HX2p)))
                  Htv0)). }
    exact (le_id_r zero
             (mult TV0 (mult mtdc_four (inv_pos (mult ds2 budget) Hwb2)))
             (mult mtdc_four ub2)
             (req_sym _ _ Hchain) Hub4'). }
  (* ub2 ≤ 4·ub2（1 ≤ 4 桩2 ＋ 弱乘单调） *)
  assert (Hub2le : le ub2 (mult mtdc_four ub2)).
  { exact (le_id_l ub2 (mult one ub2) (mult mtdc_four ub2)
             (req_sym _ _ (cmk_mult_one_l ub2))
             (le_mult_compat_weak one mtdc_four ub2 Hub2
                mtdc_le_one_four)). }
  destruct (Harch ub Hub) as [N1 HN1].
  destruct (Harch (mult mtdc_four ub2) Hub4) as [N2 HN2].
  destruct (cmk_pow_tail lt_plus_compat_lt_le kap TV0 budget ds N1 Hwb
              Hds0 Hds1 (req_refl kap) Htv0
              (lt_le_iff zero budget (inl Hbudget)) HN1) as [k1 Hk1].
  pose (Hp2 := cmk_pow_tail lt_plus_compat_lt_le kap2 TV0 budget ds2 N2
                 Hwb2 Hds2_0 mtdc_ds2_lt_one (req_refl kap2) Htv0
                 (lt_le_iff zero budget (inl Hbudget))
                 (le_lt_trans ub2 (mult mtdc_four ub2)
                    (cmk_scale (Datatypes.S N2) one) Hub2le HN2)).
  exists k1. exists (projT1 Hp2). split.
  - exact Hk1.
  - split.
    + exact (projT2 Hp2).
    + exact HN2.
Defined.

End ConjBridge.

(* G2/G3 审计口：PA 预期 Closed（公理面为空、全 Set 层证书）                      *)

Print Assumptions mtdc_lo_inflation.

(* ################  批 2 假设消解块（C2 底册 #10） #################### *)
(* Section ConjBridge 两接口字段（lt_plus_compat_lt_le 与 Harch）的供给：  *)
(*   原 Section 与主件签名零改动；本块给出两字段的前置引理与主件的无参数位       *)
(*   精简版（签名保持式供给：原版保留参数位，精简版由前置引理就位）。        *)


(* lpc 位前置引理：语句面与 UpAblMetaDivThm mtd_lpc 逐字同                   *)
(*   real_lt_plus_compat_lt_le（CW219 Real 层成品）。                       *)
Definition mtdc_lpc_supply : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d) :=
  real_lt_plus_compat_lt_le.

(* Arch 位前置引理：语句面同 Section ConjBridge 的 Harch 位（le 前件分判）。 *)
(*   严格支由 uabm_arch_scale 供给（real_arch 的 const 形上界换形）；      *)
(*   非严格支（x 与零同义）取 N := 0，结论经 cmk_boost_pos（1 + k·w > 0）  *)
(*   与右端同义改写闭合。                                                  *)
Theorem mtdc_harch_supply : forall x : Real, le zero x ->
  sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one)).
Proof.
  intros x Hx.
  destruct Hx as [Hlt | Heq].
  - exact (uabm_arch_scale x Hlt).
  - exists (Datatypes.O).
    exact (lt_id_l x zero (cmk_scale (Datatypes.S Datatypes.O) one)
             (req_sym zero x Heq)
             (cmk_scale_S_pos mtdc_lpc_supply one Datatypes.O one_pos)).
Qed.

(* 签名保持式精简版：主件 mtdc_lo_inflation 的无参数位形式——lpc 位与 Arch 位  *)
(*   分别由 mtdc_lpc_supply 与 mtdc_harch_supply 就位，其余七参显式保留。  *)
(*   （类型即出节主件结论；由定义项直接推出，避免结论面二次誊写。）        *)
Definition mtdc_lo_inflation_supplied (TV0 : Real) (Htv0 : le zero TV0)
           (budget : Real) (Hbudget : lt zero budget)
           (lo : Real) (Hlo0 : lt zero lo) (Hds1 : lt (mult lo lo) one) :=
  mtdc_lo_inflation mtdc_lpc_supply TV0 Htv0 budget Hbudget lo Hlo0 Hds1
                    mtdc_harch_supply.

(* ================= 消解块假设面核验（预期全 Closed） ==================== *)
Print Assumptions mtdc_lpc_supply.
Print Assumptions mtdc_harch_supply.
Print Assumptions mtdc_lo_inflation_supplied.
(* ================= §2 mtd_natR_nonneg 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* §0 通用小件：nat 嵌入非负、Q 层运输 kit                                     *)

Lemma mtd_natR_nonneg : forall n : nat, le zero (reqd_nat_to_R n).
Proof.
  intro n. induction n as [| n IH].
  - exact (le_refl zero).
  - exact (lt_le_iff zero (reqd_nat_to_R (Datatypes.S n))
             (inl (reqd_nat_to_R_pos n))).
Defined.

(* Q 层 Qlt/Qle 在 Qeq 下的换端运输（stdlib Q_Setoid+Qlt_compat
   /Qle_comp instance 集合态重写一次成型；Z 层 nia/compat_r 直调路线弃用） *)

(* 9.1 stdlib 与全部依赖模块 grep 零命中 Qof_nat——
   件内自建（Qmake·Z.of_nat 载体；mtd_ 前缀防撞）。 *)
Definition mtd_Qof_nat (n : nat) : Q := Qmake (Z.of_nat n) 1.

Lemma mtd_qlt_eq_r : forall u v w : Q, v == w -> Qlt u v -> Qlt u w.
Proof.
  intros u v w Hvw Hlt. rewrite Hvw in Hlt. exact Hlt.
Qed.

Lemma mtd_qlt_eq_l : forall u v w : Q, u == v -> Qlt v w -> Qlt u w.
Proof.
  intros u v w Huv Hlt. rewrite <- Huv in Hlt. exact Hlt.
Qed.

Lemma mtd_qle_eq_r : forall u v w : Q, v == w -> Qle u v -> Qle u w.
Proof.
  intros u v w Hvw Hle. rewrite Hvw in Hle. exact Hle.
Qed.

Lemma mtd_qle_eq_l : forall u v w : Q, u == v -> Qle v w -> Qle u w.
Proof.
  intros u v w Huv Hle. rewrite <- Huv in Hle. exact Hle.
Qed.

(* Qle 加正项：0 ≤ p -> a ≤ a+p（Qplus_le_compat+Qplus_0_r 组合；
   Zpos(ad*pd) 原子项与 Z 乘积无 definitional 链，nia 盲区） *)
Lemma mtd_qle_plus_pos_r : forall a p : Q, (0 <= p)%Q -> Qle a (a + p).
Proof.
  intros a p Hp.
  apply (Qle_trans a (a + 0) (a + p)).
  - rewrite Qplus_0_r. apply Qle_refl.
  - exact (Qplus_le_compat a a 0 p (Qle_refl a) Hp).
Qed.

(* Qlt 右端同加项消去：x+z < y+z -> x < y（stdlib Qplus_lt_l iff 形
   proj1 直取） *)
Lemma mtd_qlt_cancel_r : forall x y z : Q, Qlt (x + z) (y + z) -> Qlt x y.
Proof.
  intros x y z Hlt. exact (proj1 (Qplus_lt_l x y z) Hlt).
Qed.

(* Q 正乘积：0 < a -> 0 < b -> 0 < a*b *)
Lemma mtd_qpos_mult : forall a b : Q, (0 < a)%Q -> (0 < b)%Q -> (0 < a * b)%Q.
Proof.
  intros a b Ha Hb.
  apply (mtd_qlt_eq_l 0 (0 * b) (a * b)).
  - ring.
  - exact (Qmult_lt_compat_r 0 a b Hb Ha).
Qed.

(* §0b Q 层换算小件：lia 对 Q 目标零支持（9.1 micromega 无 ZifyQ）——
   序小件一律 unfold 后落显式 Z 序引理链或 stdlib 项级组合。Q 层小件：          *)

Lemma mtd_Qof_nat_0 : forall n : nat, (0 <= mtd_Qof_nat n)%Q.
Proof.
  intro n. unfold Qle, mtd_Qof_nat. cbn [Qnum Qden].
  (* Z 层化：两端乘积显式归约后对 n 归纳，S 步由 Z.le_succ_diag_r 递进   *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  induction n as [| m IH].
  - change (Z.of_nat 0) with 0%Z. apply Z.le_refl.
  - rewrite Znat.Nat2Z.inj_succ.
    exact (Z.le_trans 0 (Z.of_nat m) (Z.succ (Z.of_nat m))
             IH (Z.le_succ_diag_r (Z.of_nat m))).
Qed.

Lemma mtd_Qof_nat_pos : forall n : nat, (0 < mtd_Qof_nat (Datatypes.S n))%Q.
Proof.
  intro n. unfold Qlt, mtd_Qof_nat. cbn [Qnum Qden].
  (* Z 层化：乘积归约后 Z.of_nat (S n) 依定义化为 Z.pos (Pos.of_succ_nat *)
  (* n)，取正性见证 Pos2Z.pos_is_pos                                    *)
  rewrite Z.mul_0_l, Z.mul_1_r.
  change (Z.of_nat (Datatypes.S n)) with (Z.pos (Pos.of_succ_nat n)).
  apply Pos2Z.pos_is_pos.
Qed.

Lemma mtd_Qof_nat_le_S : forall n : nat,
  (mtd_Qof_nat n < mtd_Qof_nat (Datatypes.S n))%Q.
Proof.
  intro n.
  (* 换端：右端以 Qeq 换为 mtd_Qof_nat n + 1（Z 层 inj_succ+Z.add_1_r）  *)
  apply (mtd_qlt_eq_r (mtd_Qof_nat n) (mtd_Qof_nat n + 1)
                      (mtd_Qof_nat (Datatypes.S n))).
  - unfold Qeq, Qplus, mtd_Qof_nat. cbn [Qnum Qden].
    rewrite !Z.mul_1_r, Znat.Nat2Z.inj_succ, Z.add_1_r. reflexivity.
  - (* 严格一步：0 < 1 经 Qplus_lt_r 前向（proj2，左加 z+x<z+y）平移，     *)
    (* 左端 Qeq 运输 z+0 ≡ z                                              *)
    assert (H01 : (0 < 1)%Q).
    { unfold Qlt. cbn [Qnum Qden].
      rewrite Z.mul_0_l, Z.mul_1_r. apply Pos2Z.pos_is_pos. }
    apply (mtd_qlt_eq_l (mtd_Qof_nat n) (mtd_Qof_nat n + 0)
                        (mtd_Qof_nat n + 1)).
    + ring.
    + exact (proj2 (Qplus_lt_r 0 1 (mtd_Qof_nat n)) H01).
Qed.

Lemma mtd_Qof_nat_Sge1 : forall n : nat,
  (1 <= mtd_Qof_nat (Datatypes.S n))%Q.
Proof.
  intro n.
  (* 换端：右端以 Qeq 换为 mtd_Qof_nat n + 1（同 le_S 的 Z 层恒等链）    *)
  apply (mtd_qle_eq_r 1 (mtd_Qof_nat n + 1) (mtd_Qof_nat (Datatypes.S n))).
  - unfold Qeq, Qplus, mtd_Qof_nat. cbn [Qnum Qden].
    rewrite !Z.mul_1_r, Znat.Nat2Z.inj_succ, Z.add_1_r. reflexivity.
  - (* 1 ≤ mtd_Qof_nat n + 1 ← 0 ≤ mtd_Qof_nat n（本件 mtd_Qof_nat_0）   *)
    (* 经 Qplus_le_r 前向（proj2，左加 z+x≤z+y）平移，两端 Qeq 运输       *)
    apply (mtd_qle_eq_l 1 (1 + 0) (mtd_Qof_nat n + 1)).
    + ring.
    + apply (mtd_qle_eq_r (1 + 0) (1 + mtd_Qof_nat n) (mtd_Qof_nat n + 1)).
      * ring.
      * exact (proj2 (Qplus_le_r 0 (mtd_Qof_nat n) 1) (mtd_Qof_nat_0 n)).
Qed.

(* b<1 -> 0<1-b（Real 侧 mtd_lt_one_minus 的 Q 层同形件） *)
Lemma mtd_qlt_one_minus : forall b : Q, (b < 1)%Q -> (0 < 1 - b)%Q.
Proof.
  intros b Hb.
  apply (mtd_qlt_cancel_r 0 (1 - b) b).
  apply (mtd_qlt_eq_l (0 + b) b ((1 - b) + b)).
  - ring.
  - apply (mtd_qlt_eq_r b 1 ((1 - b) + b)).
    + ring.
    + exact Hb.
Qed.

(* 0<b -> 1-b<1（Real 侧 mtd_lt_minus_one 的 Q 层同形件） *)
Lemma mtd_qlt_minus_one : forall b : Q, (0 < b)%Q -> (1 - b < 1)%Q.
Proof.
  intros b Hb.
  apply (mtd_qlt_cancel_r (1 - b) 1 b).
  apply (mtd_qlt_eq_l ((1 - b) + b) 1 (1 + b)).
  - ring.
  - apply (mtd_qlt_eq_l 1 (1 + 0) (1 + b)).
    + ring.
    + exact (proj2 (Qplus_lt_r 0 b 1) Hb).
Qed.

(* b<=1 -> 0<=1-b（Real 侧 mtd_le_one_minus 的 Q 层同形件；落 Z 后链式闭合。
   simpl 会把 Qsub 展成 Z 的 match 结构 lia 穿不透——change 手工落形） *)
Lemma mtd_qle_one_minus : forall b : Q, (b <= 1)%Q -> (0 <= 1 - b)%Q.
Proof.
  intros b H.
  apply (proj1 (Qplus_le_r 0 (1 - b) b)).
  apply (mtd_qle_eq_l (b + 0) b (b + (1 - b))).
  - ring.
  - apply (mtd_qle_eq_r b 1 (b + (1 - b))).
    + ring.
    + exact H.
Qed.

(* §1 G1：Q 层 Bernoulli 件（传递形）与定理 A（Q 层 Doeblin 界无界性）          *)

(* nat 指数 Q 幂（局部载体；stdlib Qpower 为 positive 形，nat 形自备并申报） *)
Fixpoint mtd_qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1
  | Datatypes.S m => x * mtd_qpow x m
  end.

(* G1 核：Bernoulli 不等式 Prop 形 (1−x)^n ≥ 1−n·x（0≤x≤1） *)
Lemma mtd_qbern_prop : forall (n : nat) (x : Q),
  (0 <= x <= 1)%Q -> (1 - mtd_Qof_nat n * x <= mtd_qpow (1 - x) n)%Q.
Proof.
  intro n. induction n as [| n IH]; intro x; intro Hb.
  - (* 基步定义性归约：n=0 时两端同为 1，零乘消去后取序自反 *)
    change (1 - mtd_Qof_nat 0 * x <= mtd_qpow (1 - x) 0)%Q
      with (1 - 0 * x <= 1)%Q.
    rewrite Qmult_0_l.
    apply Qle_refl.
  - assert (Hx0 : (0 <= x)%Q) by exact (proj1 Hb).
    assert (Hx1 : (x <= 1)%Q) by exact (proj2 Hb).
    assert (Hxx : (0 <= x * x)%Q) by exact (Qmult_le_0_compat x x Hx0 Hx0).
    assert (Hnx2 : (0 <= mtd_Qof_nat n * (x * x))%Q)
      by exact (Qmult_le_0_compat (mtd_Qof_nat n) (x * x)
                  (mtd_Qof_nat_0 n) Hxx).
    assert (HSn : (mtd_Qof_nat (Datatypes.S n) == mtd_Qof_nat n + 1)%Q).
    { (* 后继恒等：Z 层由 inj_succ 与 Z.add_1_r 双向收拢为同一项 *)
      unfold Qeq, Qplus, mtd_Qof_nat. cbn [Qnum Qden].
      rewrite !Z.mul_1_r, Znat.Nat2Z.inj_succ, Z.add_1_r. reflexivity. }
    assert (Hmid : (1 - mtd_Qof_nat (Datatypes.S n) * x
                    <= (1 - x) * (1 - mtd_Qof_nat n * x))%Q).
    { rewrite HSn.
      apply (mtd_qle_eq_r _ (1 - (mtd_Qof_nat n + 1) * x
                               + mtd_Qof_nat n * (x * x))).
      - ring.
      - exact (mtd_qle_plus_pos_r _ _ Hnx2). }
    assert (Hmul0 : ((1 - mtd_Qof_nat n * x) * (1 - x)
                     <= mtd_qpow (1 - x) n * (1 - x))%Q).
    { exact (Qmult_le_compat_r (1 - mtd_Qof_nat n * x) (mtd_qpow (1 - x) n)
                               (1 - x) (IH x Hb) (mtd_qle_one_minus x Hx1)). }
    assert (Hmul1 : ((1 - x) * (1 - mtd_Qof_nat n * x)
                     <= mtd_qpow (1 - x) n * (1 - x))%Q).
    { apply (mtd_qle_eq_l ((1 - x) * (1 - mtd_Qof_nat n * x))
                          ((1 - mtd_Qof_nat n * x) * (1 - x))
                          (mtd_qpow (1 - x) n * (1 - x))).
      - ring.
      - exact Hmul0. }
    assert (Hmul : ((1 - x) * (1 - mtd_Qof_nat n * x)
                    <= (1 - x) * mtd_qpow (1 - x) n)%Q).
    { apply (mtd_qle_eq_r ((1 - x) * (1 - mtd_Qof_nat n * x))
                          (mtd_qpow (1 - x) n * (1 - x))
                          ((1 - x) * mtd_qpow (1 - x) n)).
      - ring.
      - exact Hmul1. }
    exact (Qle_trans _ _ _ Hmid Hmul).
Qed.

(* G1 交付形：Bernoulli 传递形（全 QltT 判定面） *)
Lemma mtd_qbernoulli : forall (n : nat) (x r : Q),
  QltT (0#1) x -> QltT x (1#1) -> QltT r (1 - mtd_Qof_nat n * x) ->
  QltT r (mtd_qpow (1 - x) n).
Proof.
  intros n x r Hx0 Hx1 Hr.
  assert (Hb : (0 <= x <= 1)%Q).
  { split.
    - exact (Qlt_le_weak _ _ (QltT_to_Qlt (0#1) x Hx0)).
    - exact (Qlt_le_weak _ _ (QltT_to_Qlt x (1#1) Hx1)). }
  apply Qlt_to_QltT.
  apply (Qlt_le_trans r (1 - mtd_Qof_nat n * x) (mtd_qpow (1 - x) n)).
  - exact (QltT_to_Qlt r (1 - mtd_Qof_nat n * x) Hr).
  - exact (mtd_qbern_prop n x Hb).
Defined.

(* 定理 A 合取尾件：见证 w 的三重刻画（下界链全代数）。
   补前件申报：0<r 与 mtd_Qof_nat N<y（y 抽象时 N<y 不可证——语义必需前件） *)
Lemma mtd_q_tail : forall (N : nat) (lo0 r w q l02 y : Q),
  (0 < r)%Q -> (0 < q)%Q -> (q * y == 1 - r)%Q -> (0 < y)%Q -> (1 <= y)%Q ->
  (mtd_Qof_nat N < y)%Q ->
  (0 < w)%Q -> (w <= q)%Q -> (w <= l02)%Q -> (l02 < lo0)%Q ->
  And (QltT (0#1) w) (And (QltT w lo0) (QltT r (mtd_qpow (1 - w * w) N))).
Proof.
  intros N lo0 r w q l02 y Hr0 Hq0 Hqy Hy0 Hy1 HyN Hw0 Hwq Hwl Hll.
  assert (Hwy : (w * y <= 1 - r)%Q).
  { apply (mtd_qle_eq_r _ (q * y) (1 - r) Hqy).
    exact (Qmult_le_compat_r w q y Hwq (Qlt_le_weak _ _ Hy0)). }
  assert (Hwd : (w <= 1 - r)%Q).
  { assert (Hqy0 : (0 < q * y)%Q) by exact (mtd_qpos_mult q y Hq0 Hy0).
    assert (H1r0 : (0 < 1 - r)%Q).
    { apply (mtd_qlt_eq_r _ _ _ Hqy). exact Hqy0. }
    apply (proj1 (Qmult_le_r w (1 - r) y Hy0)).
    apply (Qle_trans (w * y) (1 - r) ((1 - r) * y)).
    - exact Hwy.
    - apply (mtd_qle_eq_r (1 - r) (y * (1 - r)) ((1 - r) * y)).
      + ring.
      + apply (mtd_qle_eq_l (1 - r) (1 * (1 - r)) (y * (1 - r))).
        * ring.
        * exact (Qmult_le_compat_r 1 y (1 - r) Hy1 (Qlt_le_weak _ _ H1r0)). }
  assert (Hw1 : (w < 1)%Q).
  { exact (Qle_lt_trans w (1 - r) 1 Hwd (mtd_qlt_minus_one r Hr0)). }
  assert (Hw2 : (0 < w * w)%Q) by (apply mtd_qpos_mult; exact Hw0).
  assert (Hww1 : (w * w < 1)%Q).
  { apply (Qlt_trans (w * w) w 1).
    - apply (mtd_qlt_eq_r (w * w) (1 * w) w).
      + ring.
      + exact (Qmult_lt_compat_r w 1 w Hw0 Hw1).
    - exact Hw1. }
  assert (Hwwlew : (w * w <= w)%Q).
  { apply (mtd_qle_eq_r (w * w) (1 * w) w).
    - ring.
    - exact (Qmult_le_compat_r w 1 w (Qlt_le_weak _ _ Hw1) (Qlt_le_weak _ _ Hw0)). }
  assert (HNwle : (mtd_Qof_nat N * (w * w) <= mtd_Qof_nat N * w)%Q).
  { apply (mtd_qle_eq_r (mtd_Qof_nat N * (w * w))
                        (w * mtd_Qof_nat N) (mtd_Qof_nat N * w)).
    - ring.
    - apply (mtd_qle_eq_l (mtd_Qof_nat N * (w * w))
                          ((w * w) * mtd_Qof_nat N)
                          (w * mtd_Qof_nat N)).
      + ring.
      + exact (Qmult_le_compat_r (w * w) w (mtd_Qof_nat N)
                                 Hwwlew (mtd_Qof_nat_0 N)). }
  assert (HNlt : (mtd_Qof_nat N * w < 1 - r)%Q).
  { assert (HNq : (mtd_Qof_nat N * w <= mtd_Qof_nat N * q)%Q).
    { assert (H1 : (w * mtd_Qof_nat N <= q * mtd_Qof_nat N)%Q).
      { exact (Qmult_le_compat_r w q (mtd_Qof_nat N) Hwq (mtd_Qof_nat_0 N)). }
      apply (mtd_qle_eq_r (mtd_Qof_nat N * w) (q * mtd_Qof_nat N)
                          (mtd_Qof_nat N * q)).
      - ring.
      - apply (mtd_qle_eq_l (mtd_Qof_nat N * w) (w * mtd_Qof_nat N)
                            (q * mtd_Qof_nat N)).
        + ring.
        + exact H1. }
    assert (HNq2 : (mtd_Qof_nat N * q < y * q)%Q).
    { apply (Qmult_lt_compat_r (mtd_Qof_nat N) y q Hq0).
      exact HyN. }
    apply (mtd_qlt_eq_r (mtd_Qof_nat N * w) (y * q) (1 - r)).
    - rewrite Qmult_comm. exact Hqy.
    - exact (Qle_lt_trans (mtd_Qof_nat N * w) (mtd_Qof_nat N * q) (y * q) HNq HNq2). }
  assert (Hr' : (r < 1 - mtd_Qof_nat N * (w * w))%Q).
  { assert (HNlt2 : (mtd_Qof_nat N * (w * w) < 1 - r)%Q).
    { exact (Qle_lt_trans (mtd_Qof_nat N * (w * w)) (mtd_Qof_nat N * w)
                          (1 - r) HNwle HNlt). }
    assert (Hlt1 : (mtd_Qof_nat N * (w * w) + r < (1 - r) + r)%Q).
    { exact (proj2 (Qplus_lt_l (mtd_Qof_nat N * (w * w)) (1 - r) r) HNlt2). }
    assert (Hlt2 : (mtd_Qof_nat N * (w * w) + r < 1)%Q).
    { apply (mtd_qlt_eq_r _ ((1 - r) + r) 1).
      - ring.
      - exact Hlt1. }
    assert (Hlt3 : (mtd_Qof_nat N * (w * w) + r
                    < (1 - mtd_Qof_nat N * (w * w)) + mtd_Qof_nat N * (w * w))%Q).
    { apply (mtd_qlt_eq_r _ 1 ((1 - mtd_Qof_nat N * (w * w))
                                 + mtd_Qof_nat N * (w * w))).
      - ring.
      - exact Hlt2. }
    apply (mtd_qlt_cancel_r r (1 - mtd_Qof_nat N * (w * w))
              (mtd_Qof_nat N * (w * w))).
    apply (mtd_qlt_eq_l (r + mtd_Qof_nat N * (w * w))
                        (mtd_Qof_nat N * (w * w) + r)
                        ((1 - mtd_Qof_nat N * (w * w)) + mtd_Qof_nat N * (w * w))).
    - ring.
    - exact Hlt3. }
  split.
  - apply Qlt_to_QltT. exact Hw0.
  - split.
    + apply Qlt_to_QltT. exact (Qle_lt_trans w l02 lo0 Hwl Hll).
    + apply Qlt_to_QltT.
      exact (Qlt_le_trans r (1 - mtd_Qof_nat N * (w * w))
               (mtd_qpow (1 - w * w) N) Hr'
               (mtd_qbern_prop N (w * w)
                  (conj (Qlt_le_weak _ _ Hw2) (Qlt_le_weak _ _ Hww1)))).
Qed.

(* 定理 A：Q 层 Doeblin 界无界性（QltT 见证形）。
   见证 lo := Qle_bool 可判定分裂：
     q  := (1−r)·inv(mtd_Qof_nat (S N))，l02 := (1/2)·lo0；
     lo := if Qle_bool q l02 then q else l02。 *)
Theorem mtd_q_doeblin_unbounded :
  forall (N : nat) (lo0 r : Q),
    QltT (0#1) lo0 -> QltT (0#1) r -> QltT r (1#1) ->
    sigT (fun lo : Q =>
      And (QltT (0#1) lo) (And (QltT lo lo0)
        (QltT r (mtd_qpow (1 - lo * lo) N)))).
Proof.
  intros N lo0 r Hlo0 Hr Hr1.
  assert (Hr0 : (0 < r)%Q) by exact (QltT_to_Qlt (0#1) r Hr).
  set (y := mtd_Qof_nat (Datatypes.S N)).
  assert (Hy0 : (0 < y)%Q) by exact (mtd_Qof_nat_pos N).
  assert (Hy1 : (1 <= y)%Q) by exact (mtd_Qof_nat_Sge1 N).
  assert (HyN : (mtd_Qof_nat N < y)%Q) by exact (mtd_Qof_nat_le_S N).
  assert (Hyn0 : ~ (y == 0)%Q).
  { intro E. apply (Qlt_not_eq 0 y Hy0). exact (Qeq_sym _ _ E). }
  assert (Hinv0 : (0 < / y)%Q) by exact (Qinv_lt_0_compat y Hy0).
  assert (Hd0 : (0 < (1 - r))%Q)
    by exact (mtd_qlt_one_minus r (QltT_to_Qlt r (1#1) Hr1)).
  set (q := (1 - r) * / y).
  assert (Hq0 : (0 < q)%Q) by exact (mtd_qpos_mult (1 - r) (/ y) Hd0 Hinv0).
  assert (Hqy : q * y == 1 - r).
  { unfold q. rewrite <- (Qmult_assoc (1 - r) (/ y) y).
    rewrite (Qmult_comm (/ y) y).
    rewrite (Qmult_inv_r y Hyn0).
    ring. }
  set (l02 := (1#2) * lo0).
  assert (Hl020 : (0 < l02)%Q).
  { apply (mtd_qpos_mult (1#2) lo0).
    - unfold Qlt. cbn [Qnum Qden]. rewrite Z.mul_0_l, Z.mul_1_r.
      exact (Pos2Z.pos_is_pos 1).
    - exact (QltT_to_Qlt (0#1) lo0 Hlo0). }
  assert (Hl02lt : (l02 < lo0)%Q).
  { apply (mtd_qlt_eq_r l02 (1 * lo0) lo0).
    - ring.
    - assert (Hh : ((1#2) < 1)%Q)
        by (unfold Qlt; cbn [Qnum Qden];
            rewrite Z.mul_1_r, Z.mul_1_l; exact (Z.lt_succ_diag_r 1)).
      exact (Qmult_lt_compat_r (1#2) 1 lo0
               (QltT_to_Qlt (0#1) lo0 Hlo0) Hh). }
  destruct (Qle_bool q l02) eqn:E.
  - (* true 支：见证 q *)
    assert (Hql : (q <= l02)%Q).
    { unfold Qle_bool in E. unfold Qle.
      apply (proj1 (Z.leb_le _ _)). exact E. }
    exact (existT _ q (mtd_q_tail N lo0 r q q l02 y
                           Hr0 Hq0 Hqy Hy0 Hy1 HyN
                           Hq0 (Qle_refl q) Hql Hl02lt)).
  - (* false 支：见证 l02（此时 l02 < q） *)
    assert (Hlq : (l02 < q)%Q).
    { unfold Qle_bool in E. apply Z.leb_gt in E. unfold Qlt. exact E. }
    exact (existT _ l02 (mtd_q_tail N lo0 r l02 q l02 y
                             Hr0 Hq0 Hqy Hy0 Hy1 HyN
                             Hl020 (Qlt_le_weak _ _ Hlq)
                             (Qle_refl l02) Hl02lt)).
Defined.

(* §2 Real 层序小件（严格性运输 + Bernoulli plus-形）                          *)

(* 类场（req/le/lt，RealEnhancedReal 实例）与具体 real_eq/real_le
   /real_lt 的 definitional 互转（实例 req:=real_eq / le:=real_le / lt:=real_lt）。
   mte_*/mtw_*（具体面）与本件类面件互换时经此组显式桥接。 *)
Lemma mtd_req_real_eq : forall a b : Real, req a b -> real_eq a b.
Proof. intros a b H. exact H. Defined.

Lemma mtd_real_eq_req : forall a b : Real, real_eq a b -> req a b.
Proof. intros a b H. exact H. Defined.

Lemma mtd_le_real_le : forall a b : Real, le a b -> real_le a b.
Proof. intros a b H. exact H. Defined.

Lemma mtd_real_le_le : forall a b : Real, real_le a b -> le a b.
Proof. intros a b H. exact H. Defined.

Lemma mtd_lt_real_lt : forall a b : Real, lt a b -> real_lt a b.
Proof. intros a b H. exact H. Defined.

Lemma mtd_real_lt_lt : forall a b : Real, real_lt a b -> lt a b.
Proof. intros a b H. exact H. Defined.

(* lt 换端（req 运载） *)
Lemma mtd_lt_req_l : forall a b c : Real, req a b -> lt b c -> lt a c.
Proof.
  intros a b c Hab Hlt. exact (lt_id_l a b c Hab Hlt).
Defined.

Lemma mtd_lt_req_r : forall a b c : Real, lt a b -> req b c -> lt a c.
Proof.
  intros a b c Hlt Hbc. exact (lt_id_r a b c Hbc Hlt).
Defined.

(* 1 − b > 0（由 b < 1） *)
Lemma mtd_lt_one_minus : forall b : Real, lt b one -> lt zero (req_minus one b).
Proof.
  intro b. intro Hb.
  exact (lt_id_l zero (plus b (opp b)) (req_minus one b)
           (req_sym (plus b (opp b)) zero (plus_opp b))
           (mte_lt_plus_r b one (opp b) Hb)).
Defined.

(* 1 − b < 1（由 0 < b） *)
Lemma mtd_lt_minus_one : forall b : Real, lt zero b -> lt (req_minus one b) one.
Proof.
  intro b. intro Hb.
  apply (lt_id_r (req_minus one b) (plus (req_minus one b) b) one
           (mtw_minus_plus_r one b)).
  apply (lt_id_r (req_minus one b) (plus b (req_minus one b))
                 (plus (req_minus one b) b)
           (plus_comm b (req_minus one b))).
  apply (lt_id_l (req_minus one b) (plus zero (req_minus one b))
                 (plus b (req_minus one b))
           (req_sym (plus zero (req_minus one b)) (req_minus one b)
              (req_plus_zero_l (req_minus one b)))).
  exact (mte_lt_plus_r zero b (req_minus one b) Hb).
Defined.

(* 0 ≤ 1 − x（由 x ≤ 1；le_plus_cancel_l 仅 S04/R 型在库——
   取类场 lt_le_iff+le_id_r 组合） *)
Lemma mtd_le_one_minus : forall x : Real, le x one -> le zero (req_minus one x).
Proof.
  intro x. intro H.
  destruct H as [Hlt | Heq].
  - exact (lt_le_iff _ _ (inl (mtd_lt_one_minus x Hlt))).
  - apply (le_id_r zero zero (req_minus one x)).
    + exact (req_sym (req_minus one x) zero
               (req_trans (req_minus one x) (plus x (opp x)) zero
                  (req_sym (plus x (opp x)) (req_minus one x)
                     (req_plus_compat x one (opp x) (opp x) Heq
                        (req_refl (opp x))))
                  (plus_opp x))).
    + exact (le_refl zero).
Defined.

(* Real 层 lt 右端同加项消去（eps 层一次成型，模板＝mte_lt_plus_r 反向） *)
Lemma mtd_rlt_cancel_r : forall a b c : Real,
  lt (plus a c) (plus b c) -> lt a b.
Proof.
  intros a b c Hlt. destruct Hlt as [eps [Heps [N HN]]].
  unfold real_lt. exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    assert (Hpt : projT1 (real_plus b c) n - projT1 (real_plus a c) n
                  == projT1 b n - projT1 a n).
    { assert (Ha : projT1 (real_plus a c) n == projT1 a n + projT1 c n)
        by (apply real_plus_proj).
      assert (Hb : projT1 (real_plus b c) n == projT1 b n + projT1 c n)
        by (apply real_plus_proj).
      rewrite Hb, Ha. field. }
    assert (Hcmp : Qcompare eps (projT1 (real_plus b c) n
                                  - projT1 (real_plus a c) n)
                 = Qcompare eps (projT1 b n - projT1 a n)).
    { apply (Qcompare_comp eps eps (Qeq_refl eps)). exact Hpt. }
    unfold QltT, Qlt_bool. rewrite <- Hcmp. exact (HN n Hn).
Qed.

(* (S n) 嵌入的乘法展开：(S n)·x == x + n·x *)
Lemma mtd_Snat_mult : forall (n : nat) (x : Real),
  req (mult (reqd_nat_to_R (Datatypes.S n)) x)
      (plus x (mult (reqd_nat_to_R n) x)).
Proof.
  intros n x.
  exact (req_trans (mult (plus one (reqd_nat_to_R n)) x)
                   (mult x (plus one (reqd_nat_to_R n)))
                   (plus x (mult (reqd_nat_to_R n) x))
    (mult_comm (plus one (reqd_nat_to_R n)) x)
    (req_trans (mult x (plus one (reqd_nat_to_R n)))
               (plus (mult x one) (mult x (reqd_nat_to_R n)))
               (plus x (mult (reqd_nat_to_R n) x))
      (distrib x one (reqd_nat_to_R n))
      (req_plus_compat (mult x one) x
                       (mult x (reqd_nat_to_R n))
                       (mult (reqd_nat_to_R n) x)
         (mult_one x) (mult_comm x (reqd_nat_to_R n))))).
Defined.

(* 幂非负（(1−x) 载体；语句面修正：前提=0≤1−x（原 0≤x 使命题为假——
   x>1 时 (1−x)^1<0），自洽形且调用面零改） *)
Lemma mtd_rpow_nonneg : forall (n : nat) (x : Real),
  le zero (req_minus one x) -> le zero (req_r_pow (req_minus one x) n).
Proof.
  intro n. induction n as [| n IH]; intros x Hx.
  - exact (lt_le_iff zero one (inl one_pos)).
  - exact (reqd_le_mult_nonneg_t12 (req_minus one x)
             (req_r_pow (req_minus one x) n) Hx (IH x Hx)).
Defined.

Lemma mtd_rpow_le_one : forall (n : nat) (x : Real),
  le zero x -> le x one -> le (req_r_pow (req_minus one x) n) one.
Proof.
  intro n. induction n as [| n IH]; intros x Hx0 Hx1.
  - exact (le_refl one).
  - assert (HP0 : le zero (req_minus one x)) by exact (mtd_le_one_minus x Hx1).
    assert (HP1 : le (req_minus one x) one).
    { apply (mte_le_congr_r (req_minus one x) (plus (req_minus one x) x) one).
      - apply (mte_le_congr_l (req_minus one x)
                              (plus (req_minus one x) zero)
                              (plus (req_minus one x) x)).
        + exact (req_sym (plus (req_minus one x) zero) (req_minus one x)
                   (plus_zero (req_minus one x))).
        + exact (mte_le_plus_compat (req_minus one x) (req_minus one x)
                       zero x (real_le_refl (req_minus one x)) Hx0).
      - exact (mtw_minus_plus_r one x). }
    apply (le_trans (mult (req_minus one x) (req_r_pow (req_minus one x) n))
                    (req_minus one x) one).
    + exact (mte_le_congr_r
               (mult (req_minus one x) (req_r_pow (req_minus one x) n))
               (mult (req_minus one x) one) (req_minus one x)
        (req_le_mult_compat_r (req_minus one x)
           (req_r_pow (req_minus one x) n) one HP0 (IH x Hx0 Hx1))
        (mult_one (req_minus one x))).
    + exact HP1.
Defined.

(* Bernoulli plus-形：(1−x)^n + n·x ≥ 1（0≤x≤1） *)
Lemma mtd_rbern_plus : forall (n : nat) (x : Real),
  le zero x -> le x one ->
  le one (plus (req_r_pow (req_minus one x) n) (mult (reqd_nat_to_R n) x)).
Proof.
  intro n. induction n as [| n IH]; intros x Hx0 Hx1.
  - apply (mte_le_congr_l one
             (plus one (mult (reqd_nat_to_R 0) x))
             (plus (req_r_pow (req_minus one x) 0)
                   (mult (reqd_nat_to_R 0) x))).
    + exact (mtd_req_real_eq one (plus one (mult (reqd_nat_to_R 0) x))
        (req_sym (plus one (mult (reqd_nat_to_R 0) x)) one
           (req_trans (plus one (mult (reqd_nat_to_R 0) x))
                      (plus one zero) one
              (req_plus_compat one one (mult (reqd_nat_to_R 0) x) zero
                 (req_refl one)
                 (req_trans (mult (reqd_nat_to_R 0) x)
                            (mult x (reqd_nat_to_R 0)) zero
                    (mult_comm (reqd_nat_to_R 0) x)
                    (mult_zero x)))
              (plus_zero one)))).
    + exact (mtd_real_le_le (plus one (mult (reqd_nat_to_R 0) x))
               (plus (req_r_pow (req_minus one x) 0)
                     (mult (reqd_nat_to_R 0) x))
               (real_le_refl (plus one (mult (reqd_nat_to_R 0) x)))).
  - assert (HP0 : le zero (req_minus one x)) by exact (mtd_le_one_minus x Hx1).
    assert (HP1 : le (req_minus one x) one).
    { apply (mte_le_congr_r (req_minus one x) (plus (req_minus one x) x) one).
      - apply (mte_le_congr_l (req_minus one x)
                              (plus (req_minus one x) zero)
                              (plus (req_minus one x) x)).
        + exact (req_sym (plus (req_minus one x) zero) (req_minus one x)
                   (plus_zero (req_minus one x))).
        + exact (mte_le_plus_compat (req_minus one x) (req_minus one x)
                       zero x (real_le_refl (req_minus one x)) Hx0).
      - exact (mtw_minus_plus_r one x). }
    assert (HX1 : le (req_r_pow (req_minus one x) n) one).
    { exact (mtd_rpow_le_one n x Hx0 Hx1). }
    assert (HXx : le (mult (req_r_pow (req_minus one x) n) x) x).
    { exact (mte_le_congr_l
               (mult (req_r_pow (req_minus one x) n) x)
               (mult x (req_r_pow (req_minus one x) n)) x
               (mult_comm (req_r_pow (req_minus one x) n) x)
               (mte_le_congr_r (mult x (req_r_pow (req_minus one x) n))
                               (mult x one) x
                  (req_le_mult_compat_r x (req_r_pow (req_minus one x) n) one
                     Hx0 HX1)
                  (mult_one x))). }
    assert (HXle : le (req_r_pow (req_minus one x) n)
                      (plus (mult (req_minus one x)
                                  (req_r_pow (req_minus one x) n)) x)).
    { apply (mte_le_congr_l (req_r_pow (req_minus one x) n)
               (mult (req_r_pow (req_minus one x) n)
                     (plus (req_minus one x) x))
               (plus (mult (req_minus one x)
                           (req_r_pow (req_minus one x) n)) x)).
      - exact (req_trans (req_r_pow (req_minus one x) n)
                 (mult (req_r_pow (req_minus one x) n) one)
                 (mult (req_r_pow (req_minus one x) n)
                       (plus (req_minus one x) x))
            (req_sym (mult (req_r_pow (req_minus one x) n) one)
                     (req_r_pow (req_minus one x) n)
                     (mult_one (req_r_pow (req_minus one x) n)))
            (req_mult_compat (req_r_pow (req_minus one x) n)
                             (req_r_pow (req_minus one x) n)
                             one (plus (req_minus one x) x)
                             (req_refl (req_r_pow (req_minus one x) n))
                             (req_sym (plus (req_minus one x) x) one
                                (mtw_minus_plus_r one x)))).
      - exact (mte_le_congr_l (mult (req_r_pow (req_minus one x) n)
                                    (plus (req_minus one x) x))
                              (plus (mult (req_r_pow (req_minus one x) n)
                                          (req_minus one x))
                                    (mult (req_r_pow (req_minus one x) n) x))
                              (plus (mult (req_minus one x)
                                          (req_r_pow (req_minus one x) n)) x)
                   (distrib (req_r_pow (req_minus one x) n)
                            (req_minus one x) x)
                   (mte_le_congr_l
                      (plus (mult (req_r_pow (req_minus one x) n)
                                  (req_minus one x))
                            (mult (req_r_pow (req_minus one x) n) x))
                      (plus (mult (req_minus one x)
                                  (req_r_pow (req_minus one x) n))
                            (mult (req_r_pow (req_minus one x) n) x))
                      (plus (mult (req_minus one x)
                                  (req_r_pow (req_minus one x) n)) x)
                      (req_plus_compat
                         (mult (req_r_pow (req_minus one x) n) (req_minus one x))
                         (mult (req_minus one x) (req_r_pow (req_minus one x) n))
                         (mult (req_r_pow (req_minus one x) n) x)
                         (mult (req_r_pow (req_minus one x) n) x)
                         (mult_comm (req_r_pow (req_minus one x) n)
                                    (req_minus one x))
                         (req_refl (mult (req_r_pow (req_minus one x) n) x)))
                      (le_plus_compat (mult (req_minus one x)
                                            (req_r_pow (req_minus one x) n))
                                      (mult (req_minus one x)
                                            (req_r_pow (req_minus one x) n))
                                      (mult (req_r_pow (req_minus one x) n) x)
                                      x
                         (le_refl (mult (req_minus one x)
                                        (req_r_pow (req_minus one x) n)))
                         HXx))). }
    apply (le_trans one
             (plus (plus (mult (req_minus one x)
                                 (req_r_pow (req_minus one x) n)) x)
                   (mult (reqd_nat_to_R n) x))
             (plus (mult (req_minus one x) (req_r_pow (req_minus one x) n))
                   (mult (reqd_nat_to_R (Datatypes.S n)) x))).
    + exact (le_trans one
             (plus (req_r_pow (req_minus one x) n)
                   (mult (reqd_nat_to_R n) x))
             (plus (plus (mult (req_minus one x)
                                 (req_r_pow (req_minus one x) n)) x)
                   (mult (reqd_nat_to_R n) x))
          (IH x Hx0 Hx1)
          (le_plus_compat (req_r_pow (req_minus one x) n)
                          (plus (mult (req_minus one x)
                                      (req_r_pow (req_minus one x) n)) x)
                          (mult (reqd_nat_to_R n) x)
                          (mult (reqd_nat_to_R n) x)
                     HXle
                     (le_refl (mult (reqd_nat_to_R n) x)))).
    + exact (mte_le_congr_l
               (plus (plus (mult (req_minus one x)
                                   (req_r_pow (req_minus one x) n)) x)
                     (mult (reqd_nat_to_R n) x))
               (plus (mult (req_minus one x)
                           (req_r_pow (req_minus one x) n))
                     (plus x (mult (reqd_nat_to_R n) x)))
               (plus (mult (req_minus one x)
                           (req_r_pow (req_minus one x) n))
                     (mult (reqd_nat_to_R (Datatypes.S n)) x))
               (req_sym (plus (mult (req_minus one x)
                                    (req_r_pow (req_minus one x) n))
                              (plus x (mult (reqd_nat_to_R n) x)))
                        (plus (plus (mult (req_minus one x)
                                            (req_r_pow (req_minus one x) n)) x)
                              (mult (reqd_nat_to_R n) x))
                   (plus_assoc (mult (req_minus one x)
                                     (req_r_pow (req_minus one x) n))
                               x (mult (reqd_nat_to_R n) x)))
               (inr (req_plus_compat
                  (mult (req_minus one x) (req_r_pow (req_minus one x) n))
                  (mult (req_minus one x) (req_r_pow (req_minus one x) n))
                  (plus x (mult (reqd_nat_to_R n) x))
                  (mult (reqd_nat_to_R (Datatypes.S n)) x)
                  (req_refl (mult (req_minus one x)
                                  (req_r_pow (req_minus one x) n)))
                  (req_sym (mult (reqd_nat_to_R (Datatypes.S n)) x)
                           (plus x (mult (reqd_nat_to_R n) x))
                           (mtd_Snat_mult n x))))).
Defined.

(* le 右端同加项消去（le_plus_cancel_l 仅 S04/R 型在库——
   自建：le_plus_compat + plus_assoc/plus_opp/plus_zero 运输） *)
Lemma mtd_le_cancel_r : forall a b c : Real,
  le (plus a c) (plus b c) -> le a b.
Proof.
  intros a b c H.
  assert (H1 : le (plus (plus a c) (opp c)) (plus (plus b c) (opp c))).
  { exact (le_plus_compat (plus a c) (plus b c) (opp c) (opp c)
             H (le_refl (opp c))). }
  apply (le_id_l a (plus (plus a c) (opp c)) b).
  - exact (req_sym (plus (plus a c) (opp c)) a
             (req_trans (plus (plus a c) (opp c))
                        (plus a (plus c (opp c)))
                        a
                (req_sym (plus a (plus c (opp c)))
                         (plus (plus a c) (opp c))
                    (plus_assoc a c (opp c)))
                (req_trans (plus a (plus c (opp c)))
                           (plus a zero)
                           a
                    (req_plus_compat a a (plus c (opp c)) zero
                       (req_refl a) (plus_opp c))
                    (plus_zero a)))).
  - exact (le_id_r (plus (plus a c) (opp c))
                   (plus (plus b c) (opp c)) b
              (req_trans (plus (plus b c) (opp c))
                         (plus b (plus c (opp c)))
                         b
                  (req_sym (plus b (plus c (opp c)))
                           (plus (plus b c) (opp c))
                      (plus_assoc b c (opp c)))
                  (req_trans (plus b (plus c (opp c)))
                             (plus b zero)
                             b
                      (req_plus_compat b b (plus c (opp c)) zero
                         (req_refl b) (plus_opp c))
                      (plus_zero b)))
              H1).
Defined.

(* Bernoulli minus-形（交付形）：(1−x)^n ≥ 1−n·x *)
Lemma mtd_rbern : forall (n : nat) (x : Real),
  le zero x -> le x one ->
  le (req_minus one (mult (reqd_nat_to_R n) x))
     (req_r_pow (req_minus one x) n).
Proof.
  intros n x Hx0 Hx1.
  apply (mtd_le_cancel_r (req_minus one (mult (reqd_nat_to_R n) x))
                         (req_r_pow (req_minus one x) n)
                         (mult (reqd_nat_to_R n) x)).
  exact (mte_le_congr_l
     (plus (req_minus one (mult (reqd_nat_to_R n) x))
           (mult (reqd_nat_to_R n) x))
     one
     (plus (req_r_pow (req_minus one x) n)
           (mult (reqd_nat_to_R n) x))
     (mtw_minus_plus_r one (mult (reqd_nat_to_R n) x))
     (mtd_rbern_plus n x Hx0 Hx1)).
Defined.

(* §3 G2+G3：参数化两态核（偏移 lo²/2）+ 精确幂律 + 预算下界                    *)

Section mtd_param.

Variable lo : Real.
Hypothesis Hlo0 : lt zero lo.
Hypothesis Hlo1 : lt lo one.

Let ds := mult lo lo.
Let Hdsle : le ds lo :=
  mte_le_congr_r (mult lo lo) (mult lo one) lo
    (req_le_mult_compat_r lo lo one (lt_le_iff zero lo (inl Hlo0))
       (lt_le_iff lo one (inl Hlo1)))
    (mult_one lo).
Let Hds1 : lt ds one := le_lt_trans ds lo one Hdsle Hlo1.
Let Hc0 : lt zero (req_minus one ds) := mtd_lt_one_minus ds Hds1.

Definition mtd_w : Real := mult ds mtw_half.

Definition mtd_K (s s' : bool) : Real :=
  if s then (if s' then req_minus one mtd_w else mtd_w)
       else (if s' then mtd_w else req_minus one mtd_w).

Definition mtd_step (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (mtd_K true s')) (mult (mu false) (mtd_K false s')).

Fixpoint mtd_titer (n : nat) (mu : bool -> Real) : bool -> Real :=
  match n with
  | O => mu
  | Datatypes.S m => mtd_step (mtd_titer m mu)
  end.

Lemma mtd_row_t : req (plus (mtd_K true true) (mtd_K true false)) one.
Proof. unfold mtd_K. exact (mtw_minus_plus_r one mtd_w). Defined.

Lemma mtd_row_f : req (plus (mtd_K false true) (mtd_K false false)) one.
Proof.
  unfold mtd_K.
  apply (req_trans (plus mtd_w (req_minus one mtd_w))
                   (plus (req_minus one mtd_w) mtd_w) one).
  - exact (plus_comm mtd_w (req_minus one mtd_w)).
  - exact (mtw_minus_plus_r one mtd_w).
Defined.

(* 质量守恒（World3 mtw_mass_iter 的参数化逐行翻译） *)
Lemma mtd_mass_iter : forall (n : nat) (mu : bool -> Real),
  req (mtw_sumf mu) one -> req (mtw_sumf (mtd_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hm.
  - exact Hm.
  - unfold mtw_sumf in *; unfold mtd_step.
    apply (req_trans
             (plus (plus (mult (mtd_titer n mu true) (mtd_K true true))
                         (mult (mtd_titer n mu false) (mtd_K false true)))
                   (plus (mult (mtd_titer n mu true) (mtd_K true false))
                         (mult (mtd_titer n mu false) (mtd_K false false))))
             (plus (plus (mult (mtd_titer n mu true) (mtd_K true true))
                         (mult (mtd_titer n mu true) (mtd_K true false)))
                   (plus (mult (mtd_titer n mu false) (mtd_K false true))
                         (mult (mtd_titer n mu false) (mtd_K false false))))
             one).
    + exact (req_plus_swap_mid
               (mult (mtd_titer n mu true) (mtd_K true true))
               (mult (mtd_titer n mu false) (mtd_K false true))
               (mult (mtd_titer n mu true) (mtd_K true false))
               (mult (mtd_titer n mu false) (mtd_K false false))).
    + apply (req_trans
               (plus (plus (mult (mtd_titer n mu true) (mtd_K true true))
                           (mult (mtd_titer n mu true) (mtd_K true false)))
                     (plus (mult (mtd_titer n mu false) (mtd_K false true))
                           (mult (mtd_titer n mu false) (mtd_K false false))))
               (plus (mult (mtd_titer n mu true)
                           (plus (mtd_K true true) (mtd_K true false)))
                     (mult (mtd_titer n mu false)
                           (plus (mtd_K false true) (mtd_K false false))))
               one).
      * exact (req_plus_compat
                 (plus (mult (mtd_titer n mu true) (mtd_K true true))
                       (mult (mtd_titer n mu true) (mtd_K true false)))
                 (mult (mtd_titer n mu true)
                       (plus (mtd_K true true) (mtd_K true false)))
                 (plus (mult (mtd_titer n mu false) (mtd_K false true))
                       (mult (mtd_titer n mu false) (mtd_K false false)))
                 (mult (mtd_titer n mu false)
                       (plus (mtd_K false true) (mtd_K false false)))
                 (req_sym
                    (mult (mtd_titer n mu true)
                          (plus (mtd_K true true) (mtd_K true false)))
                    (plus (mult (mtd_titer n mu true) (mtd_K true true))
                          (mult (mtd_titer n mu true) (mtd_K true false)))
                    (distrib (mtd_titer n mu true) (mtd_K true true)
                             (mtd_K true false)))
                 (req_sym
                    (mult (mtd_titer n mu false)
                          (plus (mtd_K false true) (mtd_K false false)))
                    (plus (mult (mtd_titer n mu false) (mtd_K false true))
                          (mult (mtd_titer n mu false) (mtd_K false false)))
                    (distrib (mtd_titer n mu false) (mtd_K false true)
                             (mtd_K false false)))).
      * apply (req_trans
                 (plus (mult (mtd_titer n mu true)
                             (plus (mtd_K true true) (mtd_K true false)))
                       (mult (mtd_titer n mu false)
                             (plus (mtd_K false true) (mtd_K false false))))
                 (plus (mult (mtd_titer n mu true) one)
                       (mult (mtd_titer n mu false) one))
                 one).
        -- exact (req_plus_compat
                    (mult (mtd_titer n mu true)
                          (plus (mtd_K true true) (mtd_K true false)))
                    (mult (mtd_titer n mu true) one)
                    (mult (mtd_titer n mu false)
                          (plus (mtd_K false true) (mtd_K false false)))
                    (mult (mtd_titer n mu false) one)
                    (req_mult_compat (mtd_titer n mu true)
                                     (mtd_titer n mu true)
                                     (plus (mtd_K true true) (mtd_K true false))
                                     one
                                     (req_refl (mtd_titer n mu true))
                                     mtd_row_t)
                    (req_mult_compat (mtd_titer n mu false)
                                     (mtd_titer n mu false)
                                     (plus (mtd_K false true)
                                           (mtd_K false false))
                                     one
                                     (req_refl (mtd_titer n mu false))
                                     mtd_row_f)).
        -- apply (req_trans
                    (plus (mult (mtd_titer n mu true) one)
                          (mult (mtd_titer n mu false) one))
                    (plus (mtd_titer n mu true) (mtd_titer n mu false)) one).
           ++ exact (req_plus_compat
                       (mult (mtd_titer n mu true) one)
                       (mtd_titer n mu true)
                       (mult (mtd_titer n mu false) one)
                       (mtd_titer n mu false)
                       (mult_one (mtd_titer n mu true))
                       (mult_one (mtd_titer n mu false))).
           ++ exact (IH mu Hm).
Defined.

(* 差分反号对应（World3 mtw_df_opp_dv 的参数化翻译） *)
Lemma mtd_df_opp_dv : forall n : nat,
  req (mtw_df (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
      (opp (mtw_dv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))).
Proof.
  intro n.
  assert (HX : req ((mtd_titer n mtw_mu0) false)
                   (req_minus one ((mtd_titer n mtw_mu0) true))).
  { exact (mtw_compl (mtd_titer n mtw_mu0)
             (mtd_mass_iter n mtw_mu0 mtw_mu0_mass)). }
  assert (HY : req ((mtd_titer n mtw_nu0) false)
                   (req_minus one ((mtd_titer n mtw_nu0) true))).
  { exact (mtw_compl (mtd_titer n mtw_nu0)
             (mtd_mass_iter n mtw_nu0 mtw_nu0_mass)). }
  apply (req_trans (req_minus ((mtd_titer n mtw_mu0) false)
                              ((mtd_titer n mtw_nu0) false))
                   (req_minus (req_minus one ((mtd_titer n mtw_mu0) true))
                              (req_minus one ((mtd_titer n mtw_nu0) true)))
                   (opp (req_minus ((mtd_titer n mtw_mu0) true)
                                   ((mtd_titer n mtw_nu0) true)))).
  - exact (reqd_minus_compat ((mtd_titer n mtw_mu0) false)
             (req_minus one ((mtd_titer n mtw_mu0) true))
             ((mtd_titer n mtw_nu0) false)
             (req_minus one ((mtd_titer n mtw_nu0) true)) HX HY).
  - apply (req_trans
              (req_minus (req_minus one ((mtd_titer n mtw_mu0) true))
                         (req_minus one ((mtd_titer n mtw_nu0) true)))
              (req_minus (opp ((mtd_titer n mtw_mu0) true))
                         (opp ((mtd_titer n mtw_nu0) true)))
              (opp (req_minus ((mtd_titer n mtw_mu0) true)
                              ((mtd_titer n mtw_nu0) true)))).
    + exact (req_minus_plus_congr_l one
               (opp ((mtd_titer n mtw_mu0) true))
               (opp ((mtd_titer n mtw_nu0) true))).
    + apply (req_trans
               (req_minus (opp ((mtd_titer n mtw_mu0) true))
                          (opp ((mtd_titer n mtw_nu0) true)))
               (plus (opp ((mtd_titer n mtw_mu0) true))
                     ((mtd_titer n mtw_nu0) true))
               (opp (req_minus ((mtd_titer n mtw_mu0) true)
                               ((mtd_titer n mtw_nu0) true)))).
      * exact (req_plus_compat (opp ((mtd_titer n mtw_mu0) true))
                  (opp ((mtd_titer n mtw_mu0) true))
                  (opp (opp ((mtd_titer n mtw_nu0) true)))
                  ((mtd_titer n mtw_nu0) true)
                  (req_refl (opp ((mtd_titer n mtw_mu0) true)))
                  (req_double_neg ((mtd_titer n mtw_nu0) true))).
      * exact (req_sym (opp (req_minus ((mtd_titer n mtw_mu0) true)
                                       ((mtd_titer n mtw_nu0) true)))
                       (plus (opp ((mtd_titer n mtw_mu0) true))
                             ((mtd_titer n mtw_nu0) true))
                       (req_opp_minus ((mtd_titer n mtw_mu0) true)
                                      ((mtd_titer n mtw_nu0) true))).
Defined.

(* 单步差分耦合（泛型，核 mtd_K） *)
Lemma mtd_dv_step_gen : forall x y : bool -> Real,
  req (mtw_dv (mtd_step x) (mtd_step y))
      (plus (mult (mtw_dv x y) (mtd_K true true))
            (mult (mtw_df x y) (mtd_K false true))).
Proof.
  intros x y. unfold mtw_dv, mtw_df, mtd_step.
  apply (req_trans
           (req_minus (plus (mult (x true) (mtd_K true true))
                            (mult (x false) (mtd_K false true)))
                      (plus (mult (y true) (mtd_K true true))
                            (mult (y false) (mtd_K false true))))
           (plus (req_minus (mult (x true) (mtd_K true true))
                            (mult (y true) (mtd_K true true)))
                 (req_minus (mult (x false) (mtd_K false true))
                            (mult (y false) (mtd_K false true))))
           (plus (mult (req_minus (x true) (y true)) (mtd_K true true))
                 (mult (req_minus (x false) (y false)) (mtd_K false true)))).
  - exact (req_minus_plus_distr (mult (x true) (mtd_K true true))
             (mult (x false) (mtd_K false true))
             (mult (y true) (mtd_K true true))
             (mult (y false) (mtd_K false true))).
  - exact (req_plus_compat
             (req_minus (mult (x true) (mtd_K true true))
                        (mult (y true) (mtd_K true true)))
             (mult (req_minus (x true) (y true)) (mtd_K true true))
             (req_minus (mult (x false) (mtd_K false true))
                        (mult (y false) (mtd_K false true)))
             (mult (req_minus (x false) (y false)) (mtd_K false true))
             (req_minus_factor_pt (x true) (y true) (mtd_K true true))
             (req_minus_factor_pt (x false) (y false) (mtd_K false true))).
Defined.

(* 系数恒等：(1−w) − w == 1 − lo²（w := lo²/2） *)
Lemma mtd_diag_minus_off :
  req (req_minus (mtd_K true true) (mtd_K false true)) (req_minus one ds).
Proof.
  apply (req_trans (plus (plus one (opp mtd_w)) (opp mtd_w))
                   (plus one (opp (plus mtd_w mtd_w))) (req_minus one ds)).
  - exact (req_trans (plus (plus one (opp mtd_w)) (opp mtd_w))
                     (plus one (plus (opp mtd_w) (opp mtd_w)))
                     (plus one (opp (plus mtd_w mtd_w)))
              (req_sym (plus one (plus (opp mtd_w) (opp mtd_w)))
                       (plus (plus one (opp mtd_w)) (opp mtd_w))
                  (plus_assoc one (opp mtd_w) (opp mtd_w)))
              (req_plus_compat one one
                  (plus (opp mtd_w) (opp mtd_w))
                  (opp (plus mtd_w mtd_w))
                  (req_refl one)
                  (req_sym (opp (plus mtd_w mtd_w))
                           (plus (opp mtd_w) (opp mtd_w))
                      (req_opp_plus mtd_w mtd_w)))).
  - apply (req_plus_compat one one (opp (plus mtd_w mtd_w)) (opp ds)
             (req_refl one)
             (req_opp_compat (plus mtd_w mtd_w) ds
                (req_trans (plus mtd_w mtd_w)
                           (mult ds (plus mtw_half mtw_half)) ds
                  (req_sym (mult ds (plus mtw_half mtw_half))
                           (plus mtd_w mtd_w)
                           (distrib ds mtw_half mtw_half))
                  (req_trans (mult ds (plus mtw_half mtw_half))
                             (mult ds one) ds
                    (req_mult_compat ds ds (plus mtw_half mtw_half) one
                       (req_refl ds) mtw_hh_one)
                    (mult_one ds))))).
Defined.

(* 常数尾件：h·(1−w) − h·w == (1−lo²)·h *)
Lemma mtd_h_coeff : forall h : Real,
  req (plus (mult h (mtd_K true true)) (opp (mult h (mtd_K false true))))
      (mult (req_minus one ds) h).
Proof.
  intro h.
  apply (req_trans
           (plus (mult h (mtd_K true true))
                 (opp (mult h (mtd_K false true))))
           (mult h (req_minus (mtd_K true true) (mtd_K false true)))
           (mult (req_minus one ds) h)).
  - exact (req_sym
             (mult h (req_minus (mtd_K true true) (mtd_K false true)))
             (req_minus (mult h (mtd_K true true))
                        (mult h (mtd_K false true)))
             (req_mult_minus_distr_l h (mtd_K true true)
                (mtd_K false true))).
  - exact (req_trans (mult h (req_minus (mtd_K true true) (mtd_K false true)))
                     (mult h (req_minus one ds))
                     (mult (req_minus one ds) h)
              (req_mult_compat h h
                 (req_minus (mtd_K true true) (mtd_K false true))
                 (req_minus one ds)
                 (req_refl h) mtd_diag_minus_off)
              (mult_comm h (req_minus one ds))).
Defined.

Lemma mtd_rpow_pos : forall n : nat,
  lt zero (req_r_pow (req_minus one ds) n).
Proof.
  intro n. induction n as [| n IH].
  - exact one_pos.
  - exact (mult_positive (req_minus one ds)
             (req_r_pow (req_minus one ds) n) Hc0 IH).
Defined.

(* 主归纳：dv(n) == (1−lo²)^n（World3 mtw_dv_iter 的参数化翻译） *)
Lemma mtd_dv_iter : forall n : nat,
  req (mtw_dv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
      (req_r_pow (req_minus one ds) n).
Proof.
  intro n. induction n as [| n IH].
  - exact (req_trans (plus one (opp zero)) (plus one zero) one
             (req_plus_compat one one (opp zero) zero
                (req_refl one) reqd_opp_zero)
             (plus_zero one)).
  - assert (Hdf : req (mtw_df (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
                      (opp (req_r_pow (req_minus one ds) n))).
    { exact (req_trans
               (mtw_df (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
               (opp (mtw_dv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0)))
               (opp (req_r_pow (req_minus one ds) n))
             (mtd_df_opp_dv n)
             (req_opp_compat (mtw_dv (mtd_titer n mtw_mu0)
                                     (mtd_titer n mtw_nu0))
                             (req_r_pow (req_minus one ds) n) IH)). }
    apply (req_trans
             (mtw_dv (mtd_titer (Datatypes.S n) mtw_mu0)
                     (mtd_titer (Datatypes.S n) mtw_nu0))
             (plus (mult (mtw_dv (mtd_titer n mtw_mu0)
                                 (mtd_titer n mtw_nu0))
                         (mtd_K true true))
                   (mult (mtw_df (mtd_titer n mtw_mu0)
                                 (mtd_titer n mtw_nu0))
                         (mtd_K false true)))
             (req_r_pow (req_minus one ds) (Datatypes.S n))).
    + exact (mtd_dv_step_gen (mtd_titer n mtw_mu0)
               (mtd_titer n mtw_nu0)).
    + apply (req_trans
               (plus (mult (mtw_dv (mtd_titer n mtw_mu0)
                                   (mtd_titer n mtw_nu0))
                           (mtd_K true true))
                     (mult (mtw_df (mtd_titer n mtw_mu0)
                                   (mtd_titer n mtw_nu0))
                           (mtd_K false true)))
               (plus (mult (req_r_pow (req_minus one ds) n)
                           (mtd_K true true))
                     (opp (mult (req_r_pow (req_minus one ds) n)
                                (mtd_K false true))))
               (req_r_pow (req_minus one ds) (Datatypes.S n))).
      * exact (req_plus_compat
                 (mult (mtw_dv (mtd_titer n mtw_mu0)
                               (mtd_titer n mtw_nu0))
                       (mtd_K true true))
                 (mult (req_r_pow (req_minus one ds) n) (mtd_K true true))
                 (mult (mtw_df (mtd_titer n mtw_mu0)
                               (mtd_titer n mtw_nu0))
                       (mtd_K false true))
                 (opp (mult (req_r_pow (req_minus one ds) n)
                            (mtd_K false true)))
                 (req_mult_compat
                    (mtw_dv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
                    (req_r_pow (req_minus one ds) n)
                    (mtd_K true true) (mtd_K true true)
                    IH (req_refl (mtd_K true true)))
                 (req_trans
                    (mult (mtw_df (mtd_titer n mtw_mu0)
                                  (mtd_titer n mtw_nu0))
                          (mtd_K false true))
                    (mult (opp (req_r_pow (req_minus one ds) n))
                          (mtd_K false true))
                    (opp (mult (req_r_pow (req_minus one ds) n)
                               (mtd_K false true)))
                    (req_mult_compat
                       (mtw_df (mtd_titer n mtw_mu0)
                               (mtd_titer n mtw_nu0))
                       (opp (req_r_pow (req_minus one ds) n))
                       (mtd_K false true) (mtd_K false true)
                       Hdf (req_refl (mtd_K false true)))
                    (req_opp_mult_r (req_r_pow (req_minus one ds) n)
                                    (mtd_K false true)))).
      * exact (mtd_h_coeff (req_r_pow (req_minus one ds) n)).
Defined.

(* 精确幂律：TV(n) == (1−lo²)^n · TV₀（World3 mtw_tv_exact_iter 翻译） *)
Theorem mtd_tv_exact_iter : forall n : nat,
  req (mtw_tv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
      (mult (req_r_pow (req_minus one ds) n) (mtw_tv mtw_mu0 mtw_nu0)).
Proof.
  intro n.
  assert (Ha1 : req (abs (mtw_dv (mtd_titer n mtw_mu0)
                                (mtd_titer n mtw_nu0)))
                    (req_r_pow (req_minus one ds) n)).
  { exact (req_trans
             (abs (mtw_dv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0)))
             (abs (req_r_pow (req_minus one ds) n))
             (req_r_pow (req_minus one ds) n)
             (req_abs_compat (mtw_dv (mtd_titer n mtw_mu0)
                                     (mtd_titer n mtw_nu0))
                             (req_r_pow (req_minus one ds) n)
                             (mtd_dv_iter n))
             (abs_pos (req_r_pow (req_minus one ds) n)
                      (mtd_rpow_pos n))). }
  assert (Ha2 : req (abs (mtw_df (mtd_titer n mtw_mu0)
                                (mtd_titer n mtw_nu0)))
                    (req_r_pow (req_minus one ds) n)).
  { exact (req_trans
             (abs (mtw_df (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0)))
             (abs (opp (req_r_pow (req_minus one ds) n)))
             (req_r_pow (req_minus one ds) n)
             (req_abs_compat (mtw_df (mtd_titer n mtw_mu0)
                                     (mtd_titer n mtw_nu0))
                             (opp (req_r_pow (req_minus one ds) n))
                             (req_trans
                                (mtw_df (mtd_titer n mtw_mu0)
                                        (mtd_titer n mtw_nu0))
                                (opp (mtw_dv (mtd_titer n mtw_mu0)
                                             (mtd_titer n mtw_nu0)))
                                (opp (req_r_pow (req_minus one ds) n))
                                (mtd_df_opp_dv n)
                                (req_opp_compat
                                   (mtw_dv (mtd_titer n mtw_mu0)
                                           (mtd_titer n mtw_nu0))
                                   (req_r_pow (req_minus one ds) n)
                                   (mtd_dv_iter n))))
             (req_trans (abs (opp (req_r_pow (req_minus one ds) n)))
                        (abs (req_r_pow (req_minus one ds) n))
                        (req_r_pow (req_minus one ds) n)
                (abs_opp (req_r_pow (req_minus one ds) n))
                (abs_pos (req_r_pow (req_minus one ds) n)
                         (mtd_rpow_pos n)))). }
  apply (req_trans (mtw_tv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
                   (mult mtw_half
                         (plus (req_r_pow (req_minus one ds) n)
                               (req_r_pow (req_minus one ds) n)))
                   (mult (req_r_pow (req_minus one ds) n)
                         (mtw_tv mtw_mu0 mtw_nu0))).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mtd_titer n mtw_mu0 s)
                                  (mtd_titer n mtw_nu0 s))))
             (plus (req_r_pow (req_minus one ds) n)
                   (req_r_pow (req_minus one ds) n))
             (req_refl mtw_half)
             (req_plus_compat
                (abs (req_minus (mtd_titer n mtw_mu0 true)
                                (mtd_titer n mtw_nu0 true)))
                (req_r_pow (req_minus one ds) n)
                (abs (req_minus (mtd_titer n mtw_mu0 false)
                                (mtd_titer n mtw_nu0 false)))
                (req_r_pow (req_minus one ds) n) Ha1 Ha2)).
  - apply (req_trans
             (mult mtw_half
                   (plus (req_r_pow (req_minus one ds) n)
                         (req_r_pow (req_minus one ds) n)))
             (mult mtw_half
                   (mult (plus one one) (req_r_pow (req_minus one ds) n)))
             (mult (req_r_pow (req_minus one ds) n)
                   (mtw_tv mtw_mu0 mtw_nu0))).
    + exact (req_mult_compat mtw_half mtw_half
               (plus (req_r_pow (req_minus one ds) n)
                     (req_r_pow (req_minus one ds) n))
               (mult (plus one one) (req_r_pow (req_minus one ds) n))
               (req_refl mtw_half)
               (req_sym (mult (plus one one)
                              (req_r_pow (req_minus one ds) n))
                        (plus (req_r_pow (req_minus one ds) n)
                              (req_r_pow (req_minus one ds) n))
                        (req_two_mult (req_r_pow (req_minus one ds) n)))).
    + apply (req_trans
               (mult mtw_half
                     (mult (plus one one)
                           (req_r_pow (req_minus one ds) n)))
               (mult (mult mtw_half (plus one one))
                     (req_r_pow (req_minus one ds) n))
               (mult (req_r_pow (req_minus one ds) n)
                     (mtw_tv mtw_mu0 mtw_nu0))).
      * exact (mult_assoc mtw_half (plus one one)
                 (req_r_pow (req_minus one ds) n)).
      * apply (req_trans
                 (mult (mult mtw_half (plus one one))
                       (req_r_pow (req_minus one ds) n))
                 (mult one (req_r_pow (req_minus one ds) n))
                 (mult (req_r_pow (req_minus one ds) n)
                       (mtw_tv mtw_mu0 mtw_nu0))).
        -- exact (req_mult_compat (mult mtw_half (plus one one)) one
                     (req_r_pow (req_minus one ds) n)
                     (req_r_pow (req_minus one ds) n)
                     (req_trans (mult mtw_half (plus one one))
                                (mult (plus one one) mtw_half) one
                        (mult_comm mtw_half (plus one one))
                        (inv_pos_correct (plus one one) req_two_pos))
                     (req_refl (req_r_pow (req_minus one ds) n))).
        -- exact (req_trans (mult one (req_r_pow (req_minus one ds) n))
                            (req_r_pow (req_minus one ds) n)
                            (mult (req_r_pow (req_minus one ds) n)
                                  (mtw_tv mtw_mu0 mtw_nu0))
                     (req_mult_one_l (req_r_pow (req_minus one ds) n))
                     (req_sym (mult (req_r_pow (req_minus one ds) n)
                                    (mtw_tv mtw_mu0 mtw_nu0))
                              (req_r_pow (req_minus one ds) n)
                         (req_trans (mult (req_r_pow (req_minus one ds) n)
                                          (mtw_tv mtw_mu0 mtw_nu0))
                                    (mult (req_r_pow (req_minus one ds) n) one)
                                    (req_r_pow (req_minus one ds) n)
                              (req_mult_compat (req_r_pow (req_minus one ds) n)
                                               (req_r_pow (req_minus one ds) n)
                                               (mtw_tv mtw_mu0 mtw_nu0) one
                                               (req_refl (req_r_pow (req_minus one ds) n))
                                               mtw_tv0_one)
                              (mult_one (req_r_pow (req_minus one ds) n))))).
Defined.

(* 预算下界（World3 mtw_no_mixing_below 的参数化翻译——定型件） *)
Theorem mtd_no_mixing_below : forall (n : nat) (B : Real),
  lt B (mult (req_r_pow (req_minus one ds) n) (mtw_tv mtw_mu0 mtw_nu0)) ->
  lt B (mtw_tv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0)).
Proof.
  intros n B H.
  exact (lt_id_r B (mult (req_r_pow (req_minus one ds) n)
                        (mtw_tv mtw_mu0 mtw_nu0))
                  (mtw_tv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
          (req_sym (mtw_tv (mtd_titer n mtw_mu0) (mtd_titer n mtw_nu0))
                   (mult (req_r_pow (req_minus one ds) n)
                         (mtw_tv mtw_mu0 mtw_nu0))
                   (mtd_tv_exact_iter n)) H).
Defined.

End mtd_param.

(* §4 主件：mtd_unbounded（lo→0 混合时间无界，nat 见证形）                      *)

Theorem mtd_unbounded :
  forall (N : nat) (budget : Real),
    lt zero budget -> lt budget one ->
    sigT (fun lo : Real =>
      And (lt zero lo) (And (lt lo one)
        (lt budget (mtw_tv (mtd_titer lo N mtw_mu0)
                           (mtd_titer lo N mtw_nu0))))).
Proof.
  intros N budget H0 H1.
  assert (Hd0 : lt zero (req_minus one budget)) by exact (mtd_lt_one_minus budget H1).
  assert (Hd1 : lt (req_minus one budget) one) by exact (mtd_lt_minus_one budget H0).
  set (y := reqd_nat_to_R (Datatypes.S N)).
  assert (Hy : lt zero y) by exact (reqd_nat_to_R_pos N).
  assert (Hdlo : le zero (req_minus one budget))
    by exact (lt_le_iff zero (req_minus one budget) (inl Hd0)).
  set (lw := mult (req_minus one budget) (inv_pos y Hy)).
  assert (Hw0 : lt zero lw).
  { exact (mult_positive (req_minus one budget) (inv_pos y Hy)
             Hd0 (inv_pos_pos y Hy)). }
  assert (Hwy : req (mult lw y) (req_minus one budget)).
  { unfold lw. apply (req_trans (mult (mult (req_minus one budget) (inv_pos y Hy)) y)
                                (mult (req_minus one budget) (mult (inv_pos y Hy) y))
                                (req_minus one budget)).
    - exact (req_sym (mult (req_minus one budget) (mult (inv_pos y Hy) y))
                     (mult (mult (req_minus one budget) (inv_pos y Hy)) y)
                (mult_assoc (req_minus one budget) (inv_pos y Hy) y)).
    - apply (req_trans (mult (req_minus one budget) (mult (inv_pos y Hy) y))
                       (mult (req_minus one budget) one)
                       (req_minus one budget)).
      + exact (req_mult_compat (req_minus one budget) (req_minus one budget)
                  (mult (inv_pos y Hy) y) one
                  (req_refl (req_minus one budget))
                  (req_trans (mult (inv_pos y Hy) y)
                             (mult y (inv_pos y Hy)) one
                        (mult_comm (inv_pos y Hy) y)
                        (inv_pos_correct y Hy))).
      + exact (mult_one (req_minus one budget)). }
  assert (H1y : le one y).
  { apply (mte_le_congr_r one (plus one (reqd_nat_to_R N)) y).
    - apply (mte_le_congr_l one (plus one zero) (plus one (reqd_nat_to_R N))).
      + exact (req_sym (plus one zero) one (plus_zero one)).
      + exact (mte_le_plus_compat one one zero (reqd_nat_to_R N)
                   (real_le_refl one) (mtd_natR_nonneg N)).
    - exact (req_refl y). }
  assert (Hwle : le lw (req_minus one budget)).
  { apply (mte_le_congr_l lw (mult lw one) (req_minus one budget)
             (mtd_req_real_eq lw (mult lw one)
                (req_sym (mult lw one) lw (mult_one lw)))).
    exact (mte_le_congr_r (mult lw one) (mult lw y) (req_minus one budget)
             (req_le_mult_compat_r lw one y (lt_le_iff zero lw (inl Hw0)) H1y)
             Hwy). }
  assert (Hw1 : lt lw one).
  { exact (le_lt_trans lw (req_minus one budget) one Hwle Hd1). }
  assert (Hwwle : le (mult lw lw) lw).
  { exact (mte_le_congr_r (mult lw lw) (mult lw one) lw
             (req_le_mult_compat_r lw lw one
                (lt_le_iff zero lw (inl Hw0)) (lt_le_iff lw one (inl Hw1)))
             (mult_one lw)). }
  assert (Hds1 : lt (mult lw lw) one).
  { exact (le_lt_trans (mult lw lw) lw one Hwwle Hw1). }
  assert (HNlt : lt (mult (reqd_nat_to_R N) lw) (req_minus one budget)).
  { exact (lt_id_r (mult (reqd_nat_to_R N) lw) (mult lw y)
             (req_minus one budget) Hwy
      (lt_id_l (mult (reqd_nat_to_R N) lw)
               (mult lw (reqd_nat_to_R N)) (mult lw y)
               (mult_comm (reqd_nat_to_R N) lw)
               (real_mult_lt_compat_l (reqd_nat_to_R N) y lw
                  (mte_lt_plus_one (reqd_nat_to_R N))
                  Hw0))). }
  assert (HNds_lt : lt (mult (reqd_nat_to_R N) (mult lw lw))
                       (req_minus one budget)).
  { exact (le_lt_trans (mult (reqd_nat_to_R N) (mult lw lw))
             (mult (reqd_nat_to_R N) lw) (req_minus one budget)
             (req_le_mult_compat_r (reqd_nat_to_R N) (mult lw lw) lw
                (mtd_natR_nonneg N) Hwwle)
             HNlt). }
  assert (Hbern : le (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
                     (req_r_pow (req_minus one (mult lw lw)) N)).
  { exact (mtd_rbern N (mult lw lw)
             (lt_le_iff zero (mult lw lw) (inl (mult_positive lw lw Hw0 Hw0)))
             (lt_le_iff (mult lw lw) one (inl Hds1))). }
  assert (Hlt1 : lt (plus (mult (reqd_nat_to_R N) (mult lw lw)) budget) one).
  { exact (lt_id_r (plus (mult (reqd_nat_to_R N) (mult lw lw)) budget)
             (plus (req_minus one budget) budget) one
             (mtw_minus_plus_r one budget)
             (mte_lt_plus_r (mult (reqd_nat_to_R N) (mult lw lw))
                            (req_minus one budget) budget HNds_lt)). }
  assert (Hlt2 : lt (plus budget (mult (reqd_nat_to_R N) (mult lw lw)))
                    (plus (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
                          (mult (reqd_nat_to_R N) (mult lw lw)))).
  { apply (lt_id_l (plus budget (mult (reqd_nat_to_R N) (mult lw lw)))
             (plus (mult (reqd_nat_to_R N) (mult lw lw)) budget)
             (plus (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
                   (mult (reqd_nat_to_R N) (mult lw lw)))
             (plus_comm budget (mult (reqd_nat_to_R N) (mult lw lw)))).
    exact (lt_id_r
             (plus (mult (reqd_nat_to_R N) (mult lw lw)) budget) one
             (plus (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
                   (mult (reqd_nat_to_R N) (mult lw lw)))
             (req_sym
                (plus (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
                      (mult (reqd_nat_to_R N) (mult lw lw)))
                one
                (mtw_minus_plus_r one (mult (reqd_nat_to_R N) (mult lw lw))))
             Hlt1). }
  assert (Hbud : lt budget
                   (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))).
  { exact (mtd_rlt_cancel_r budget
             (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
             (mult (reqd_nat_to_R N) (mult lw lw)) Hlt2). }
  assert (Hbelow : lt budget
                    (mult (req_r_pow (req_minus one (mult lw lw)) N)
                          (mtw_tv mtw_mu0 mtw_nu0))).
  { apply (lt_id_r budget (req_r_pow (req_minus one (mult lw lw)) N)
             (mult (req_r_pow (req_minus one (mult lw lw)) N)
                   (mtw_tv mtw_mu0 mtw_nu0))).
    - exact (req_sym
               (mult (req_r_pow (req_minus one (mult lw lw)) N)
                     (mtw_tv mtw_mu0 mtw_nu0))
               (req_r_pow (req_minus one (mult lw lw)) N)
          (req_trans (mult (req_r_pow (req_minus one (mult lw lw)) N)
                           (mtw_tv mtw_mu0 mtw_nu0))
                     (mult (req_r_pow (req_minus one (mult lw lw)) N) one)
                     (req_r_pow (req_minus one (mult lw lw)) N)
              (req_mult_compat (req_r_pow (req_minus one (mult lw lw)) N)
                               (req_r_pow (req_minus one (mult lw lw)) N)
                               (mtw_tv mtw_mu0 mtw_nu0) one
                               (req_refl (req_r_pow (req_minus one (mult lw lw)) N))
                               mtw_tv0_one)
              (mult_one (req_r_pow (req_minus one (mult lw lw)) N)))).
    - exact (mte_lt_le_trans budget
               (req_minus one (mult (reqd_nat_to_R N) (mult lw lw)))
               (req_r_pow (req_minus one (mult lw lw)) N)
               Hbud Hbern). }
  exists lw. split.
  - exact Hw0.
  - split.
    + exact Hw1.
    + exact (mtd_no_mixing_below lw Hw0 Hw1 N budget Hbelow).
Defined.

(* §5 G4：合取收尾（B 侧下界 × C 侧 LoInflation 膨胀律，共享见证 lo）           *)

(* lpc 件内自证（复用 mte_lt_plus_r；零接口参数位） *)
Definition mtd_lpc : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hlt Hle. destruct Hle as [Hlt2 | Heq].
  - exact (real_lt_plus_compat a b c d Hlt Hlt2).
  - exact (lt_id_r (plus a c) (plus b c) (plus b d)
             (req_plus_compat b b c d (req_refl b) Heq)
             (mte_lt_plus_r a b c Hlt)).
Defined.

Definition mtd_inv2 : Real := inv_pos (plus one one) req_two_pos.
Definition mtd_four : Real := plus (plus one one) (plus one one).
Definition mtd_loh (l : Real) : Real := mult l mtd_inv2.

(*   （桥接引理 mtdc_lo_inflation，居 UpAblMetaConjBridge）在共享见证 lo      *)
(*   上的合取：3 族 6 处载体换名                                             *)
(*   （ums_scale→cmk_scale ×2、r_pow→cmk_r_pow ×2、minus→req_minus ×2）       *)
(*   语句面最小换名，语义零形变；两主件                                     *)
(*   mtd_unbounded/mtd_q_doeblin_unbounded 语句面                           *)
(*   零触碰。                                                               *)
Theorem mtd_unbounded_conj :
  forall (N : nat) (TV0 : Real) (Htv0 : le zero TV0)
         (budget : Real) (Hbudget : lt zero budget) (Hb1 : lt budget one)
         (Harch : forall x : Real, le zero x ->
                    sigT (fun M : nat => lt x (cmk_scale (Datatypes.S M) one))),
  sigT (fun lo : Real =>
    And (lt zero lo) (And (lt lo one)
      (And (lt budget (mtw_tv (mtd_titer lo N mtw_mu0)
                              (mtd_titer lo N mtw_nu0)))
        (forall (Hlo0 : lt zero lo) (Hds1 : lt (mult lo lo) one),
          sigT (fun k1 : nat => sigT (fun k2 : nat =>
            And (lt (mult (cmk_r_pow (req_minus one (mult lo lo)) k1) TV0) budget)
              (And (lt (mult (cmk_r_pow (req_minus one
                              (mult (mtd_loh lo) (mtd_loh lo))) k2) TV0)
                      budget)
                   (lt (mult mtd_four
                          (mult TV0
                             (inv_pos
                                (mult (mult (mtd_loh lo) (mtd_loh lo)) budget)
                                (mult_positive
                                   (mult (mtd_loh lo) (mtd_loh lo)) budget
                                   (mult_positive (mtd_loh lo) (mtd_loh lo)
                                      (mult_positive lo mtd_inv2 Hlo0
                                         (inv_pos_pos (plus one one)
                                            req_two_pos))
                                      (mult_positive lo mtd_inv2 Hlo0
                                         (inv_pos_pos (plus one one)
                                            req_two_pos)))
                                   Hbudget))))
                       (cmk_scale k2 one))))))))).
Proof.
  intros N TV0 Htv0 budget Hbudget Hb1 Harch.
  destruct (mtd_unbounded N budget Hbudget Hb1) as [lw [Hw0 [Hw1 HtvN]]].
  exists lw. split.
  - exact Hw0.
  - split.
    + exact Hw1.
    + split.
      * exact HtvN.
      * intros Hlo0 Hds1.
        exact (mtdc_lo_inflation mtd_lpc TV0 Htv0 budget Hbudget
                  lw Hlo0 Hds1 Harch).
Defined.

(* 公理面自检：主件 Closed（零新假设）审计面                                      *)

Print Assumptions mtd_qbernoulli.
Print Assumptions mtd_q_doeblin_unbounded.
Print Assumptions mtd_rbern.
Print Assumptions mtd_tv_exact_iter.
Print Assumptions mtd_no_mixing_below.
Print Assumptions mtd_unbounded.
Print Assumptions mtd_lpc.
Print Assumptions mtd_unbounded_conj.
