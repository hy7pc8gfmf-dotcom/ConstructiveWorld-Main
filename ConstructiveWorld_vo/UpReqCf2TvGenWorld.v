(* ============================================================ *)
(* UpReqCf2TvGenWorld.v —— 泛型有限世界数据段 TV 封装件（零承认件）     *)
(*                                                              *)
(* 一、模块名＋数学使命：任意有限 enum 世界（世界载体与枚举列表全程      *)
(*     参数化，非 bool 特化）的世界数据段逐点事实泛型封装：泛型全变差    *)
(*     TV 算子 uc2t_gen_tv 及其逐点绝对值非负前件（Habs 显式假设位）     *)
(*     消解主件；另附常数列表和、均匀分布归一、enum 非空证书三件泛型     *)
(*     封装。将「世界数据段枚举归纳」步升为机检：列表归纳腿由在库        *)
(*     sumd_list_sum_nonneg 供给，本件增量＝泛型 TV 封装＋前件消解。     *)
(* 二、依赖清单：CW_ConstructiveWorld_219（S01-S15 聚合导出面）、        *)
(*     UpReqAlgebra（req_minus／req_le_mult_compat_r／le_id_l／          *)
(*     req_mult_one_r／req_mult_comm_rewrite／sumd_lt_le 等）、          *)
(*     UpReqSumD（sumd_list_sum／sumd_list_sum_nonneg）、                *)
(*     UpReqDist（reqd_nat_to_R 系；UpReqSumD 传递依赖，闭包零增量）。   *)
(* 三、对标行：UpReqConcFin2.v cf2_enum_ne(L93)／cf2_sum_eq_list(L138)／ *)
(*     cf2_Unif_norm(L152)／cf2_tv(L236)；核心依赖模块                     *)
(*     sumd_list_sum_nonneg（UpReqSumD.v L112，前件全称不限 In，宽形）。 *)
(* 四、构造性注记：全件语句 Set 值（req／le／lt 全 Set 层接口面，        *)
(*     enum 非空证书沿用库内 Not 认证形先例）；零承认件（无未证断言、    *)
(*     无经典逻辑），纯项式组装。签名修订登记：主件对系数 inv2 携带      *)
(*     lt zero inv2 前件——inv2 无正性前件时语句不真（inv2 取负元即      *)
(*     反例），此为最小修复前件；具体实例位由 inv_pos_pos 一跳供给。     *)
(*     不可泛化项登记：z 双界（cf2_z_lb／cf2_z_ub）的非平凡内容＝        *)
(*     ±Delta 两点值域的具体证书，系世界特有数据，泛型化产物只能是       *)
(*     「逐点界假设即结论」的同义回声，故不设泛型件；上游 rsq_bs_ 核     *)
(*     链本就以（类型，enum 列表）双参数直通，各 nR 世界自供 z 界证书    *)
(*     即可接入，机检面无缺口。                                          *)
(* 五、编译配方：9.1 全路径 coqc；COQLIB／ROCQLIB 置空；-Q . "" 空根     *)
(*     映射；大输出文件重定向。                                          *)
(* ============================================================ *)

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

(* ---- 常数列表和泛型封装（均匀归一的归纳腿；reqd_nat_to_R 加法结构）---- *)

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
