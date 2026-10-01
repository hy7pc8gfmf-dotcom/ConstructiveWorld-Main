(* ==========================================================================)
   UpReqCf2TvGenSupply —— Fin2 总变差 general 位非负消解边界检验件；同域语句面
   使命：本件形式化Fin2 总变差 general 位非负消解边界检验件。
   本件并载：泛型有限世界数据段 TV 封装件（零承认件）；3 元世界点质量对位严格正检验件（零承认件）。
   依赖：List, S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog
     S08_RealMainlineDPO, S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp,
     UpReqAlgebra, UpReqSumD, UpReqDist, UpReqConcSoftmax, UpReqSampling, UpReqConcMixSel, UpReqConcB1, UpReqConcB2,
     AttnDoeblin, UpReqConcFin2。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqDist.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import UpReqConcB2.
Require Import AttnDoeblin.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* 件一·供给向强形：零归一前件——对任意 mu nu，plain abs_nonneg 字段
   直接消解 general 位 TV₀≥0。 *)
Lemma uc2t_habs_cf2tv_nonneg : forall (mu nu : bool -> Real),
  (forall x : Real, le zero (abs x)) -> le zero (cf2_tv mu nu).
Proof.
  intros mu nu Habs.
  apply (le_id_l zero (mult cf2_inv_two zero) (cf2_tv mu nu)
           (req_sym (mult cf2_inv_two zero) zero (mult_zero cf2_inv_two))).
  unfold cf2_tv.
  apply (req_le_mult_compat_r cf2_inv_two zero
           (cf2_sumf (fun s : bool => abs (req_minus (mu s) (nu s))))).
  - (* cf2_inv_two = (1+1)⁻¹ > 0 升非负（req 层正性件） *)
    exact (sumd_lt_le cf2_inv_two (inv_pos_pos (plus one one) req_two_pos)).
  - (* 逐项 Habs → 列表和非负；cf2_sumf 定义性即 sumd_list_sum bool _ [true; false] *)
    exact (sumd_list_sum_nonneg bool
             (fun s : bool => abs (req_minus (mu s) (nu s))) [true; false]
             (fun s : bool => Habs (req_minus (mu s) (nu s)))).
Qed.

(* 件一·规格形：带归一前件口径，强形一行推论
   （归一前件对供给向不可达命题无贡献，此处如实登记其未被使用）。 *)
Lemma uc2t_habs_cf2tv_nonneg_norm : forall (mu nu : bool -> Real),
  (forall x : Real, le zero (abs x)) ->
  req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> le zero (cf2_tv mu nu).
Proof.
  intros mu nu Habs _ _.
  exact (uc2t_habs_cf2tv_nonneg mu nu Habs).
Qed.

(* 件二·反向半边：general 位 TV₀≥0 消解（带归一前件口径）复原 plain abs_nonneg 字段。 *)
Lemma uc2t_cf2tv_nonneg_habs_rev :
  (forall (mu nu : bool -> Real),
     req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> le zero (cf2_tv mu nu)) ->
  forall x : Real, le zero (abs x).
Proof.
  intros H x.
  (* nu ≡ half 归一：half + (half + 0) = (1+1)·half = 1 *)
  assert (Hnu : req (cf2_sumf (fun _ : bool => cf2_inv_two)) one).
  { exact (req_trans (plus cf2_inv_two (plus cf2_inv_two zero))
                     (plus cf2_inv_two cf2_inv_two) one
             (req_plus_compat cf2_inv_two cf2_inv_two (plus cf2_inv_two zero) cf2_inv_two
                              (req_refl cf2_inv_two) (plus_zero cf2_inv_two))
             (req_trans (plus cf2_inv_two cf2_inv_two)
                        (mult (plus one one) cf2_inv_two) one
                        (req_sym (mult (plus one one) cf2_inv_two)
                                 (plus cf2_inv_two cf2_inv_two)
                                 (req_two_mult cf2_inv_two))
                        (inv_pos_correct (plus one one) req_two_pos))). }
  (* mu ≡ half±x 摆动对归一：(half+x) + ((half−x)+0) = (half+half) + (x+(−x))
     = (half+half) + 0 = half+half = (1+1)·half = 1 *)
  assert (Hmu : req (cf2_sumf (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x))) one).
  { exact (req_trans (plus (plus cf2_inv_two x) (plus (plus cf2_inv_two (opp x)) zero))
                     (plus (plus cf2_inv_two x) (plus cf2_inv_two (opp x)))
                     one
                     (req_plus_compat (plus cf2_inv_two x) (plus cf2_inv_two x)
                                      (plus (plus cf2_inv_two (opp x)) zero) (plus cf2_inv_two (opp x))
                                      (req_refl (plus cf2_inv_two x))
                                      (plus_zero (plus cf2_inv_two (opp x))))
                     (req_trans (plus (plus cf2_inv_two x) (plus cf2_inv_two (opp x)))
                                (plus (plus cf2_inv_two cf2_inv_two) (plus x (opp x)))
                                one
                                (req_plus_swap_mid cf2_inv_two x cf2_inv_two (opp x))
                                (req_trans (plus (plus cf2_inv_two cf2_inv_two) (plus x (opp x)))
                                           (plus (plus cf2_inv_two cf2_inv_two) zero)
                                           one
                                           (req_plus_compat (plus cf2_inv_two cf2_inv_two) (plus cf2_inv_two cf2_inv_two)
                                                            (plus x (opp x)) zero
                                                            (req_refl (plus cf2_inv_two cf2_inv_two))
                                                            (req_plus_opp_r x))
                                           (req_trans (plus (plus cf2_inv_two cf2_inv_two) zero)
                                                      (plus cf2_inv_two cf2_inv_two)
                                                      one
                                                      (req_plus_zero_r (plus cf2_inv_two cf2_inv_two))
                                                      (req_trans (plus cf2_inv_two cf2_inv_two)
                                                                 (mult (plus one one) cf2_inv_two)
                                                                 one
                                                                 (req_sym (mult (plus one one) cf2_inv_two)
                                                                          (plus cf2_inv_two cf2_inv_two)
                                                                          (req_two_mult cf2_inv_two))
                                                                 (inv_pos_correct (plus one one) req_two_pos)))))). }
  (* 逐项差：(half+x)−half = x、(half−x)−half = −x（req_minus_plus_cancel_r）；
     abs 字段回提后 −x 支经 abs_opp 同归 abs x；半倍和 half·(|x|+|x|) = |x| 闭合 *)
  assert (Htv : req (cf2_tv (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x)) (fun _ : bool => cf2_inv_two)) (abs x)).
  { exact (req_trans
             (mult cf2_inv_two
                   (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                         (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero)))
             (mult cf2_inv_two (plus (abs x) (abs x)))
             (abs x)
             (req_mult_compat cf2_inv_two cf2_inv_two
                              (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                    (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero))
                              (plus (abs x) (abs x))
                              (req_refl cf2_inv_two)
                              (req_trans (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                               (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero))
                                         (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                               (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)))
                                         (plus (abs x) (abs x))
                                         (req_plus_compat (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero)
                                                          (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                          (req_refl (abs (req_minus (plus cf2_inv_two x) cf2_inv_two)))
                                                          (plus_zero (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))))
                                         (req_plus_compat (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (abs x)
                                                          (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                          (abs x)
                                                          (req_abs_compat (req_minus (plus cf2_inv_two x) cf2_inv_two) x
                                                                          (req_minus_plus_cancel_r cf2_inv_two x))
                                                          (req_trans (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                                     (abs (opp x)) (abs x)
                                                                     (req_abs_compat (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two) (opp x)
                                                                                     (req_minus_plus_cancel_r cf2_inv_two (opp x)))
                                                                     (abs_opp x)))))
             (req_trans (mult cf2_inv_two (plus (abs x) (abs x)))
                        (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                        (abs x)
                        (distrib cf2_inv_two (abs x) (abs x))
                        (req_trans (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                                   (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                   (abs x)
                                   (req_sym (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                            (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                                            (req_mult_plus_distr_r cf2_inv_two cf2_inv_two (abs x)))
                                   (req_trans (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                              (mult one (abs x)) (abs x)
                                              (req_mult_compat (plus cf2_inv_two cf2_inv_two) one (abs x) (abs x)
                                                               (req_trans (plus cf2_inv_two cf2_inv_two)
                                                                          (mult (plus one one) cf2_inv_two) one
                                                                          (req_sym (mult (plus one one) cf2_inv_two)
                                                                                   (plus cf2_inv_two cf2_inv_two)
                                                                                   (req_two_mult cf2_inv_two))
                                                                          (inv_pos_correct (plus one one) req_two_pos))
                                                               (req_refl (abs x)))
                                              (req_mult_one_l (abs x)))))). }
  exact (le_id_r zero
           (cf2_tv (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x))
                   (fun _ : bool => cf2_inv_two))
           (abs x) Htv (H _ _ Hmu Hnu)).
Qed.

(* ============================ §1 泛型有限世界数据段 TV 封装件（零承认件） ============================ *)
From Stdlib Require Import List.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section 泛型有限世界：载体 S 与枚举列表 l 全程参数化                  *)
(* ============================================================ *)

Section Uc2tGenWorld.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.

(* 泛型 TV 算子：inv2 · Σ_{s ∈ l} |mu s − nu s|。                       *)
(* inv2 显式传参＝1/2 类常数自持（零依赖 Fin2 特化件）；列表和走         *)
(* sumd_list_sum（UpReqSumD 列表折叠机，与 csm_sumf 同构自持）。          *)
Definition uc2t_gen_tv (inv2 : R) (mu nu : S -> R) (l : list S) : R :=
  mult inv2 (sumd_list_sum S (fun s : S => abs (req_minus (mu s) (nu s))) l).

(* 求和桥泛型封装（cf2_sum_eq_list 的列表泛型对应物）：泛型 TV 定义性    *)
(* 即「系数乘列表和」，req_refl 定义级闭合。                              *)
Lemma uc2t_gen_tv_eq_list :
  forall (inv2 : R) (mu nu : S -> R) (l : list S),
    req (uc2t_gen_tv inv2 mu nu l)
        (mult inv2 (sumd_list_sum S (fun s : S => abs (req_minus (mu s) (nu s))) l)).
Proof.
  intros inv2 mu nu l. exact (req_refl _).
Qed.

(* 主件：plain 形 abs 非负全称前件（Habs 显式假设位）消解泛型 TV 非负。  *)
(* 两跳：①逐点非负⟹列表和非负（sumd_list_sum_nonneg，前件全称不限       *)
(* In，宽于所需）；②正系数乘 le 保持（req_le_mult_compat_r）＋req 换轨   *)
(* 一跳（le_id_l）。                                                     *)
Lemma uc2t_gen_tv_nonneg_habs :
  forall (inv2 : R) (mu nu : S -> R) (l : list S),
    lt zero inv2 ->
    (forall x : R, le zero (abs x)) ->
    le zero (uc2t_gen_tv inv2 mu nu l).
Proof.
  intros inv2 mu nu l Hinv2 Habs. unfold uc2t_gen_tv.
  exact (le_id_l zero (mult inv2 zero)
           (mult inv2
              (sumd_list_sum S (fun s : S => abs (req_minus (mu s) (nu s))) l))
           (req_sym _ _ (mult_zero inv2))
           (req_le_mult_compat_r inv2 zero
              (sumd_list_sum S (fun s : S => abs (req_minus (mu s) (nu s))) l)
              (sumd_lt_le inv2 Hinv2)
              (sumd_list_sum_nonneg S
                 (fun s : S => abs (req_minus (mu s) (nu s))) l
                 (fun s : S => Habs (req_minus (mu s) (nu s)))))).
Qed.

(* ---- 常数列表和泛型封装（均匀归一的归纳肢；reqd_nat_to_R 加法结构）---- *)

Lemma uc2t_gen_sum_const :
  forall (c : R) (l : list S),
    req (sumd_list_sum S (fun _ : S => c) l)
        (mult c (reqd_nat_to_R (length l))).
Proof.
  intro c. intro l. induction l as [| x t IH].
  - exact (req_sym _ _ (mult_zero c)).
  - exact (req_trans _ _ _
             (req_plus_compat c (mult c one)
                (sumd_list_sum S (fun _ : S => c) t)
                (mult c (reqd_nat_to_R (length t)))
                (req_sym _ _ (req_mult_one_r c)) IH)
             (req_sym _ _ (distrib c one (reqd_nat_to_R (length t))))).
Qed.

(* 泛型世界基数（＝枚举列表长的实数嵌入）及其正性证书。 *)
Definition uc2t_gen_nR (l : list S) : R := reqd_nat_to_R (length l).

Lemma uc2t_gen_nR_pos :
  forall (l : list S), l <> (@nil S) -> lt zero (uc2t_gen_nR l).
Proof.
  intro l. intro Hne. destruct l as [| x t].
  - exact (False_rect _ (Hne eq_refl)).
  - exact (reqd_nat_to_R_pos (length t)).
Qed.

(* 均匀分布归一泛型封装（cf2_Unif_norm 的列表泛型对应物）：任意非空有限  *)
(* enum 上 1/n 常数质量和为一。 *)
Lemma uc2t_gen_unif_norm :
  forall (l : list S) (Hne : l <> (@nil S)),
    req (sumd_list_sum S
           (fun _ : S => inv_pos (uc2t_gen_nR l) (uc2t_gen_nR_pos l Hne)) l)
        one.
Proof.
  intro l. intro Hne.
  apply (req_trans _
           (mult (inv_pos (uc2t_gen_nR l) (uc2t_gen_nR_pos l Hne))
                 (uc2t_gen_nR l)) _).
  - exact (uc2t_gen_sum_const
             (inv_pos (uc2t_gen_nR l) (uc2t_gen_nR_pos l Hne)) l).
  - exact (req_trans _ _ _
             (req_mult_comm_rewrite
                (inv_pos (uc2t_gen_nR l) (uc2t_gen_nR_pos l Hne))
                (uc2t_gen_nR l))
             (inv_pos_correct (uc2t_gen_nR l) (uc2t_gen_nR_pos l Hne))).
Qed.

(* enum 非空证书泛型封装（cf2_enum_ne 的列表泛型对应物；同款 Not 认证    *)
(* 形——False 消去落 Set 的库内先例认证形，使用面＝核链非空槽）。 *)
Lemma uc2t_gen_enum_ne :
  forall (s : S) (l : list S), Not (cons s l = (@nil S)).
Proof.
  intros s l H. discriminate H.
Qed.

End Uc2tGenWorld.

(* ============================ §2 3 元世界点质量对位严格正检验件（零承认件） ============================ *)
From Stdlib Require Import List.
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
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqDist.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* T1 · 3 元世界数据（显式三值枚举；非退化＝wA／wB 两行相异）            *)
(* ============================================================ *)

Inductive uc2t_w3 : Set := uc2t_wA | uc2t_wB | uc2t_wC.

Definition uc2t_enum3 : list uc2t_w3 := [uc2t_wA; uc2t_wB; uc2t_wC].

(* 点质量对：mu0 = [1;0;0]、nu0 = [0;1;0] *)
Definition uc2t_mu0w3 : uc2t_w3 -> Real :=
  fun s : uc2t_w3 => match s with uc2t_wA => one | _ => zero end.
Definition uc2t_nu0w3 : uc2t_w3 -> Real :=
  fun s : uc2t_w3 => match s with uc2t_wB => one | _ => zero end.

(* 逐点差值证书值（wA／wB 支为 one，wC 支两点质量重合为 zero） *)
Definition uc2t_pt3 : uc2t_w3 -> Real :=
  fun s : uc2t_w3 => match s with uc2t_wC => zero | _ => one end.

(* TV3 算子（cf2_tv 同构换世界；inv2 借 Fin2 件＝1/2 自持常数；列表和    *)
(* 直走 sumd_list_sum 列表折叠机） *)
Definition uc2t_tv3 (mu nu : uc2t_w3 -> Real) : Real :=
  mult cf2_inv_two
       (sumd_list_sum uc2t_w3
          (fun s : uc2t_w3 => abs (req_minus (mu s) (nu s))) uc2t_enum3).

(* ============================================================ *)
(* T2 · 三段模板重演：逐点证书 → 和折叠 → 严格正                        *)
(* ============================================================ *)

(* 段一：逐点 |mu0 − nu0| = uc2t_pt3 s（wA：one−zero 直归一；wB：zero−one *)
(* 经 abs_opp 换形；wC：zero−zero 经 abs_zero 字段 req 形直供） *)
Lemma uc2t_abs_pt_w3 : forall s : uc2t_w3,
  req (abs (req_minus (uc2t_mu0w3 s) (uc2t_nu0w3 s))) (uc2t_pt3 s).
Proof.
  intro s. destruct s as [ | | ].
  - exact (req_trans _ _ _
             (req_abs_compat
                (req_minus (uc2t_mu0w3 uc2t_wA) (uc2t_nu0w3 uc2t_wA)) one
                (req_trans _ _ _
                   (req_plus_compat one one (opp zero) zero
                      (req_refl one) reqd_opp_zero)
                   (plus_zero one)))
             (abs_pos one one_pos)).
  - exact (req_trans _ _ _
             (req_abs_compat
                (req_minus (uc2t_mu0w3 uc2t_wB) (uc2t_nu0w3 uc2t_wB)) (opp one)
                (req_plus_zero_l (opp one)))
             (req_trans _ _ _ (abs_opp one) (abs_pos one one_pos))).
  - exact (req_trans _ _ _
             (req_abs_compat
                (req_minus (uc2t_mu0w3 uc2t_wC) (uc2t_nu0w3 uc2t_wC)) zero
                (req_trans _ _ _ (req_plus_zero_l zero) reqd_opp_zero))
             abs_zero).
Defined.

(* 段二：逐点差和折叠：Σ |mu0 − nu0| = 1 + 1（1+1+0 合并，cf2_tv_sum_one  *)
(* 同构） *)
Lemma uc2t_tv3_sum_two : req
  (sumd_list_sum uc2t_w3
     (fun s : uc2t_w3 => abs (req_minus (uc2t_mu0w3 s) (uc2t_nu0w3 s)))
     uc2t_enum3)
  (plus one one).
Proof.
  exact (req_trans _ _ _
           (req_plus_compat
              (abs (req_minus (uc2t_mu0w3 uc2t_wA) (uc2t_nu0w3 uc2t_wA)))
              (abs (req_minus (uc2t_mu0w3 uc2t_wA) (uc2t_nu0w3 uc2t_wA)))
              (plus (abs (req_minus (uc2t_mu0w3 uc2t_wB) (uc2t_nu0w3 uc2t_wB)))
                    (abs (req_minus (uc2t_mu0w3 uc2t_wC) (uc2t_nu0w3 uc2t_wC))))
              (plus one zero)
              (uc2t_abs_pt_w3 uc2t_wA)
              (req_plus_compat
                 (abs (req_minus (uc2t_mu0w3 uc2t_wB) (uc2t_nu0w3 uc2t_wB)))
                 one
                 (abs (req_minus (uc2t_mu0w3 uc2t_wC) (uc2t_nu0w3 uc2t_wC)))
                 zero
                 (uc2t_abs_pt_w3 uc2t_wB)
                 (uc2t_abs_pt_w3 uc2t_wC)))
           (req_plus_compat
              (abs (req_minus (uc2t_mu0w3 uc2t_wA) (uc2t_nu0w3 uc2t_wA)))
              one
              (plus one zero) one
              (uc2t_abs_pt_w3 uc2t_wA) (req_plus_zero_l one))).
Defined.

(* 段三：TV3 严格正（req_mult_compat 换内项＋mult_positive＋inv_pos_pos＋ *)
(* req_two_pos；req_lt_id_r_loc 换形一跳——cf2_tv_pos 同构） *)
Theorem uc2t_tv3_pos : lt zero (uc2t_tv3 uc2t_mu0w3 uc2t_nu0w3).
Proof.
  apply (req_lt_id_r_loc zero
           (mult cf2_inv_two (plus one one))
           (uc2t_tv3 uc2t_mu0w3 uc2t_nu0w3)).
  - exact (req_sym
             (mult cf2_inv_two
                (sumd_list_sum uc2t_w3
                   (fun s : uc2t_w3 =>
                      abs (req_minus (uc2t_mu0w3 s) (uc2t_nu0w3 s)))
                   uc2t_enum3))
             (mult cf2_inv_two (plus one one))
             (req_mult_compat cf2_inv_two cf2_inv_two
                (sumd_list_sum uc2t_w3
                   (fun s : uc2t_w3 =>
                      abs (req_minus (uc2t_mu0w3 s) (uc2t_nu0w3 s)))
                   uc2t_enum3)
                (plus one one)
                (req_refl cf2_inv_two) uc2t_tv3_sum_two)).
  - exact (mult_positive cf2_inv_two (plus one one)
             (inv_pos_pos (plus one one) req_two_pos) req_two_pos).
Defined.

(* le 一跳（点质量对位零前件供件——严格正→非负，不触 plain 形 abs 非负   *)
(* 字段：点位闭合路径与基数无关的机检实证） *)
Lemma uc2t_tv3_nonneg : le zero (uc2t_tv3 uc2t_mu0w3 uc2t_nu0w3).
Proof.
  apply (lt_le_iff zero (uc2t_tv3 uc2t_mu0w3 uc2t_nu0w3)).
  left.
  exact uc2t_tv3_pos.
Defined.

(* ============================================================ *)
(* T3 · Fin2 求和机实例注记：cf2_sumf 定义性即泛型列表折叠机在          *)
(*     bool/[true;false] 上的实例（req_refl 一跳；泛型世界封装件与      *)
(*     Fin2 特化线同源共机的机检注记）                                  *)
(* ============================================================ *)

Lemma uc2t_fin2_sumf_gen_instance : forall f : bool -> Real,
  req (cf2_sumf f) (sumd_list_sum bool f [true; false]).
Proof.
  intro f. exact (req_refl _).
Defined.
