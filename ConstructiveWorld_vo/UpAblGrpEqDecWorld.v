(* ============================================================ *)
(* UpAblGrpEqDecWorld.v —— 族A grp_eq_dec 可判等前提的载体世界装配件      *)
(* 母本前提位置：S15_TailFEPUp.v                                  *)
(*   （Module UpGRPO219 · Section GRPONoDup） *)
(*   Variable grp_eq_dec : forall i j : Group, Or (Id i j) (Not (Id i j)) *)
(* 本件使命：仿照既有 keep_dec:=@inl unit 的实例化先例，                  *)
(*   装配具体 Group 载体世界（bool 二元组群）并供给该前提的可判等实例，    *)
(*   逐项供给该节前提组（覆盖表/规模正性/无重复表/零奖励），收束为        *)
(*   「抽象前提在具体载体上的实例化消解」定理形。                        *)
(*                                                              *)
(* 本件为零承认件：纯构造性；零公理、零承认、零新设前提、零经典逻辑；    *)
(*   语句面全 Set 层（Id/Or/Not/InT/prod 均为 S01 Set 层形）；全 Qed/    *)
(*   Defined 收尾；Print Assumptions 全 Closed 核验于件尾。              *)
(*                                                              *)
(* 事实注记：GRPONoDup 节 Group 为抽象 Set 参量，库内           *)
(*   无既有具体形态；节前提组＝group_enum/group_cover/     *)
(*   grp_eq_dec（本前提位置）/reward_group/G_pos（实名，  *)
(*   group_size_pos 此名在库内不存在）/Hnd_g。S01 系实数接口       *)
(*   RealInterfaceEnhanced 全库无具体实例（S02 明言完整实例属大    *)
(*   工程），故实层轴以抽象参量入包（forall RI                            *)
(*   泛量化），本件覆盖范围＝Group 载体轴，实层前提不在本件范围。        *)
(*                                                              *)
(* 非平凡承载点：Id 构造子判别（Id true/false 构造子冲突的 J 依赖消去，  *)
(*   内核模式匹配判别——非 Corelib or_introl，Or 为 S01 Set 层别名        *)
(*   Or:=A+B，@inl/@inr 直用）；四支判定逐支构造性见证；InT 判别         *)
(*   （inversion 冲突消解）；nodup_g 项式装配；母本 B2/B3 主定理 bool 世界实例化消解。 *)
(*                                                              *)
(* 所用上游出口（限定名引用）：UpGRPO219.nat_to_R_g/nodup_g/list_sum_g/  *)
(*   grpo_indicator_sum_one/grpo_uniform_mass——Module 限定名避撞名；    *)
(*   母本源件零改动。                                                    *)
(* 对标行：无直接对应物（可判等前提的具体载体实例层）。                  *)
(* 编译配方：9.1 直调（coqc 无 -Q），cpu_guard 包裹，-o 输出临时目录。   *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Import ListNotations.

Section GQCWorld.
Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* ===== §1 具体载体世界：二元组群（bool 两点枚举型） ===== *)

Definition gqc_Group : Set := bool.
Definition gqc_enum : list gqc_Group := [true; false].

(* ===== §2 覆盖枚举表前提（group_cover : forall i, InT i grp_enum） ===== *)

Lemma gqc_cover : forall i : gqc_Group, InT i gqc_enum.
Proof.
  intro i. destruct i.
  - exact (InT_here true (false :: nil)).
  - exact (InT_next false true (false :: nil) (InT_here false (@nil bool))).
Qed.

(* ===== §3 grp_eq_dec 可判等前提：bool 载体可判等实例（本件非平凡承载点） ===== *)
(* Id 为 S01 Set 层归纳等词；判别＝构造子冲突的依赖消去（大消去）。     *)
(* Or 为 S01 Set 层别名 Or:=A+B，逐支 @inl/@inr 见证，非经典排除律。    *)

Lemma gqc_true_neq_false : Not (Id true false).
Proof. intro h. inversion h. Qed.

Lemma gqc_false_neq_true : Not (Id false true).
Proof. intro h. inversion h. Qed.

Definition gqc_grp_eq_dec : forall i j : gqc_Group, Or (Id i j) (Not (Id i j)) :=
  fun i j =>
    match i as a return (Or (Id a j) (Not (Id a j))) with
    | true =>
        match j as b return (Or (Id true b) (Not (Id true b))) with
        | true => @inl _ _ id_refl
        | false => @inr _ _ gqc_true_neq_false
        end
    | false =>
        match j as b return (Or (Id false b) (Not (Id false b))) with
        | true => @inr _ _ gqc_false_neq_true
        | false => @inl _ _ id_refl
        end
    end.

(* ===== §4 reward_group 前提：零奖励常值（该前提位置无特殊要求） ===== *)

Definition gqc_reward : gqc_Group -> R := fun _ => zero.

(* ===== §5 规模正性前提（母本实名 G_pos；规模＝二元组群，|枚举|=2） ===== *)

Lemma gqc_G_pos : lt zero (UpGRPO219.nat_to_R_g (length gqc_enum)).
Proof.
  exact (UpGRPO219.nat_to_R_g_pos (Datatypes.S O)).
Qed.

(* ===== §6 无重复表前提（Hnd_g : nodup_g Group group_enum） ===== *)
(* InT 判别工具：nil 位空匹配＋构造子冲突消解（inversion）。           *)

Lemma gqc_InT_nil_empty : forall b : gqc_Group, InT b nil -> Empty_set.
Proof. intros b Hin. inversion Hin. Qed.

Lemma gqc_notin_tf : InT true (false :: nil) -> Empty_set.
Proof. intro Hin. now inversion Hin. Qed.

Lemma gqc_notin_ft : InT false (true :: nil) -> Empty_set.
Proof. intro Hin. now inversion Hin. Qed.

Definition gqc_Hnd : UpGRPO219.nodup_g gqc_Group gqc_enum :=
  (gqc_notin_tf, (gqc_InT_nil_empty false, tt)).

(* ===== §7 封装证书（前提组封装记录型：仿 S17 keep_dec 实例先例） ===== *)
(* 前提序＝母本声明序（Group/group_enum/group_cover/grp_eq_dec/          *)
(*   reward_group/G_pos/Hnd_g）；实层轴以抽象参量入包泛量化。            *)

Inductive gqc_pack : Type :=
| gqc_pack_intro :
    forall (Grp : Set) (grp_enum : list Grp)
           (group_cover : forall i : Grp, InT i grp_enum)
           (grp_eq_dec : forall i j : Grp, Or (Id i j) (Not (Id i j)))
           (reward_group : Grp -> R)
           (G_pos : lt zero (UpGRPO219.nat_to_R_g (length grp_enum)))
           (Hnd_g : UpGRPO219.nodup_g Grp grp_enum),
      gqc_pack.

Theorem gqc_supplied : gqc_pack.
Proof.
  exact (gqc_pack_intro gqc_Group gqc_enum gqc_cover gqc_grp_eq_dec
                        gqc_reward gqc_G_pos gqc_Hnd).
Qed.

(* ===== §8 抽象前提在具体载体上的实例化消解（母本 B2/B3 主定理） ===== *)

Theorem gqc_indicator_sum_one_bool : forall j : gqc_Group,
  InT j gqc_enum ->
  Id (UpGRPO219.list_sum_g gqc_Group (fun i : gqc_Group =>
        match gqc_grp_eq_dec i j with
        | inl _ => one
        | inr _ => zero
        end) gqc_enum) one.
Proof.
  intro j. intro Hin.
  exact (UpGRPO219.grpo_indicator_sum_one gqc_Group gqc_enum gqc_grp_eq_dec
                                          gqc_Hnd j Hin).
Qed.

Theorem gqc_uniform_mass_bool : forall j : gqc_Group,
  InT j gqc_enum ->
  Id (UpGRPO219.list_sum_g gqc_Group (fun i : gqc_Group =>
        mult (inv_pos (UpGRPO219.nat_to_R_g (length gqc_enum)) gqc_G_pos)
             (match gqc_grp_eq_dec i j with
              | inl _ => one
              | inr _ => zero
              end)) gqc_enum)
     (inv_pos (UpGRPO219.nat_to_R_g (length gqc_enum)) gqc_G_pos).
Proof.
  intro j. intro Hin.
  exact (UpGRPO219.grpo_uniform_mass gqc_Group gqc_enum gqc_grp_eq_dec
                                     gqc_G_pos gqc_Hnd j Hin).
Qed.

End GQCWorld.

(* ===== 收尾：公理依赖核验 ===== *)

Print Assumptions gqc_supplied.
Print Assumptions gqc_indicator_sum_one_bool.
Print Assumptions gqc_uniform_mass_bool.
