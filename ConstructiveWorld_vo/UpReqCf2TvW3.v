(* ============================================================ *)
(* UpReqCf2TvW3.v —— 3 元世界点质量对位严格正检验件（零承认件）         *)
(*                                                              *)
(* 一、模块名＋数学使命：显式三值枚举世界（uc2t_w3）上点质量对位         *)
(*     [1;0;0]／[0;1;0] 的全变差 TV 严格正判据重演：uc2t_tv3_pos。       *)
(*     作为「非退化判据（≥2 相异 logit 点）不随世界基数变化」的机检      *)
(*     背书：点质量位闭合走严格正→非负一跳，不触 plain 形 abs 非负      *)
(*     字段供给（general 位仍挂该字段，不在本件范围，如实申报）。        *)
(* 二、依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、     *)
(*     UpReqDist、UpReqConcFin2（借 cf2_inv_two＝1/2 自持常数）。        *)
(* 三、对标行：UpReqConcFin2.v cf2_abs_pt_one(L241)／cf2_tv_sum_one      *)
(*     (L260)／cf2_tv_pos(L281)／cf2_tv_nonneg(L297) 三段模板逐跳换     *)
(*     世界；逐点证书值域 {one, one, zero}（wC 点两点质量重合，差为零），*)
(*     和＝1+1+0＝2，TV＝1/2·2＝1；wC 零点支由接口字段 abs_zero（req    *)
(*     形）直供。附 Fin2 求和机实例注记一件。                            *)
(* 四、构造性注记：全件语句 Set 值；零承认件（无未证断言、无经典逻辑）   *)
(*     ；三支 destruct 逐点证书＋嵌套 req_plus_compat 折叠＋             *)
(*     req_lt_id_r_loc 换形一跳，纯项式组装。                            *)
(* 五、编译配方：9.1 全路径 coqc；COQLIB／ROCQLIB 置空；-Q . "" 空根     *)
(*     映射；大输出文件重定向。                                          *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
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
