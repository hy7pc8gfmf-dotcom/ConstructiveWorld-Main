(* ==========================================================================)
   UpReqNegFactorB.v — 负因子乘法的序反转（≤_B）
   使命: t27_le_b_mult_r_nonpos_opp/t27_le_b_mult_r_nonpos_or/t27_le_b_mult_r_negstrict 与 t27_le_b_mult_l_nonpos_or（≤_B 对负因子的反转族）及 t27_le_nonpos_to_nonneg_opp。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB3、UpReqPowMonoBridge
   对标: 实数序在负数乘法下的反转（≤_B 一致序版本）。
   构造性: 全件 Qed 闭合、零承认词面；证体不引入额外公理前提。
   编译配方: Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""（vo 树同世界重编），COQLIB/ROCQLIB 全字面环境前缀。
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
Require Import UpRealLeB.
Require Import UpRealLeB3.
Require Import UpReqPowMonoBridge.

(* ============================================================ *)
(* 〇、负因子证书桥：c ≤ 0（Or 形）给 0 ≤ −c（Or 形）                     *)
(*   取负反序（real_opp_le_compat）＋ 负零归一（real_opp_zero）换形。      *)
(*   正面 x3d 件4（Or 给 B 单向桥）的负号副本面。                         *)
(* ============================================================ *)
Lemma t27_le_nonpos_to_nonneg_opp : forall c : Real,
  real_le c real_zero -> real_le real_zero (real_opp c).
Proof.
  intros c Hc.
  exact (RealSetoid.real_le_id_l real_zero (real_opp real_zero)           (real_opp c)           (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)           (real_opp_le_compat c real_zero Hc)).
Qed.

(* ============================================================ *)
(* 一、共轭核：0 ≤ −c（Or 形）给 b·c ≤_B a·c                              *)
(*   链：正面件1 于因子 −c 处（Hrev）→ le_b 取负反序（Hflip，eps 翻转     *)
(*   步由 leb3_le_b_opp_rev 给出）→ real_opp_mult＋opp 对合 双端等式      *)
(*   运输（HoppA/HoppB）→ eq_r／eq_l 双运输完成。                         *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_opp : forall a b c : Real,
  real_le_b a b -> real_le real_zero (real_opp c) ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc0.
  (* 正面保序于负因子共轭位：a·(−c) ≤_B b·(−c) *)
  assert (Hrev : real_le_b (real_mult a (real_opp c))
                           (real_mult b (real_opp c)))
    by exact (x3d_le_b_mult_r_nonneg_or a b (real_opp c) H Hc0).
  (* le_b 取负反序：−(b·(−c)) ≤_B −(a·(−c)) *)
  assert (Hflip : real_le_b
                    (real_opp (real_mult b (real_opp c)))
                    (real_opp (real_mult a (real_opp c))))
    by exact (leb3_le_b_opp_rev (real_mult a (real_opp c))
                                (real_mult b (real_opp c)) Hrev).
  (* 右端换形：−(a·(−c)) == a·c（opp 入乘＋对合归一） *)
  assert (HoppA : real_eq (real_opp (real_mult a (real_opp c)))
                          (real_mult a c)).
  { apply (real_eq_trans _ (real_mult a (real_opp (real_opp c))) _).
    - exact (real_opp_mult a (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat a
               (real_opp (real_opp c)) a c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* 左端换形：−(b·(−c)) == b·c（同款） *)
  assert (HoppB : real_eq (real_opp (real_mult b (real_opp c)))
                          (real_mult b c)).
  { apply (real_eq_trans _ (real_mult b (real_opp (real_opp c))) _).
    - exact (real_opp_mult b (real_opp c)).
    - apply (RealSetoid.real_eq_mult_compat b
               (real_opp (real_opp c)) b c).
      + apply real_eq_refl.
      + exact (real_opp_opp c). }
  (* eq_l／eq_r 双运输完成：b·c ≤_B a·c *)
  exact (leb3_le_b_eq_r (real_mult b c)
           (real_opp (real_mult a (real_opp c))) (real_mult a c)
           (leb3_le_b_eq_l (real_opp (real_mult b (real_opp c)))
              (real_mult b c)
              (real_opp (real_mult a (real_opp c))) HoppB Hflip)
           HoppA).
Qed.

(* ============================================================ *)
(* 二、主件：原语句逐字——x ≤_B y 且 c ≤ 0 给 y·c ≤_B x·c              *)
(*   件0 桥一接入共轭核。与正面件1（x3d_le_b_mult_r_nonneg_or）           *)
(*   逐参数位对位：证书 0≤c 换 c≤0，结论方向翻转。                            *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_opp.
  - exact H.
  - exact (t27_le_nonpos_to_nonneg_opp c Hc).
Qed.

(* ============================================================ *)
(* 三、左因子反变形：c·y ≤_B c·x（comm 双运输平移件2）                     *)
(*   正面 x3d 件2 的负号副本。                                           *)
(* ============================================================ *)
Lemma t27_le_b_mult_l_nonpos_or : forall a b c : Real,
  real_le_b a b -> real_le c real_zero ->
  real_le_b (real_mult c b) (real_mult c a).
Proof.
  intros a b c H Hc.
  apply (leb3_le_b_eq_l (real_mult b c) (real_mult c b) (real_mult c a)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult b c) (real_mult a c) (real_mult c a)).
    + exact (t27_le_b_mult_r_nonpos_or a b c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 四、严格负因子对照形：c < 0 给 y·c ≤_B x·c                             *)
(*   lt 转 Or（real_lt_le_iff_req 取 inl 支）后一跳件2。                  *)
(*   正面 x3d 件3（严格正因子对照形）的负号副本。                         *)
(* ============================================================ *)
Lemma t27_le_b_mult_r_negstrict : forall a b c : Real,
  real_le_b a b -> real_lt c real_zero ->
  real_le_b (real_mult b c) (real_mult a c).
Proof.
  intros a b c H Hc.
  apply t27_le_b_mult_r_nonpos_or.
  - exact H.
  - exact (RealSetoid.real_lt_le_iff_req c real_zero (inl Hc)).
Qed.

(* ============================================================ *)
(* 五、假设审计（全件证据在编译日志）                                     *)
(* ============================================================ *)

Print Assumptions t27_le_nonpos_to_nonneg_opp.
Print Assumptions t27_le_b_mult_r_nonpos_opp.
Print Assumptions t27_le_b_mult_r_nonpos_or.
Print Assumptions t27_le_b_mult_l_nonpos_or.
Print Assumptions t27_le_b_mult_r_negstrict.

(* ============================================================ *)
(* 尾注：诚实登记表                                                        *)
(* 【对称面结果】负面反变面（件2 主件）与正面保序面（x3d 件1）合成        *)
(*   Or 形因子证书强度下的完整乘法保序两面对：符号证书在手时，乘法        *)
(*   保序／反变方向由因子符号唯一确定，两面经取负共轭互为副本。           *)
(* 【显式假设对位】因子仅 B 形已知（无 Or 形符号证书）的负面版＝正面件4       *)
(*   显式假设的副本，两面显式假设形状对称，禁无依据凑形。                  *)
(* ============================================================ *)
