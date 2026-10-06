(* uabd_supply_S05_Z_align_pos_unit.v —— Z_align 正性：单点实例世界闭合供给 *)
(* 使命：Z_align_pos 槽的实例级完全消解——在库内唯一具体 SumOver 实例
   （uab_ssUnit／uab_soUnit，单点状态空间）上给出零附加前提的闭合正性
   定理。件①为抽象接口缺失的严格保正性质的实例级见证（uab_soUnit 的
   sum_over_S 定义面为因子行，逐点前提直接代入）；件②由件①与接口
   正性字段（mult_positive／exp_neg_pos）复合，闭合装配 Z_align 正性。
   先例同族：配分正性单点消解二件（配套库件 :130／:141 行）。 *)
(* 依赖：S01_BaseRing（RealInterfaceEnhanced 类字段）、S05_AlignmentGRPO
   （Z_align）、G13 配套库件（uab_ssUnit／uab_soUnit／uab_ssUnit_elem，逐名见 Require 行）。 *)
(* 构造性：语句全 Set 层；证明为显式构造链（定义面展开 + 逐点代入 +
   字段复合），零公理、零承认、零经典逻辑。 *)
(* 编译配方：coqc -q -Q <主 vo 树> "" -Q . "" uabd_supply_S05_Z_align_pos_unit.v
   （COQLIB／ROCQLIB 全字面导出，9.1 工具链）。 *)

Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import UpAblT13c_G13.

(* ① 单点 SumOver 实例的严格保正供给（抽象接口未载严格正字段，
   本件为该性质的实例级见证） *)
Theorem uabd_uab_soUnit_sum_pos :
  forall {RI0 : RealInterfaceEnhanced}
         (f : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0),
    (forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)), lt zero (f s)) ->
    lt zero (@sum_over_S RI0 (@uab_ssUnit (@RI_base RI0))
               (@uab_soUnit (@RI_base RI0)) f).
Proof.
  intros RI0 f H.
  exact (H (@uab_ssUnit_elem (@RI_base RI0))).
Qed.

(* ② 闭合形：零附加前提的 Z_align 正性（单点实例世界，全链在库） *)
Theorem uabd_Z_align_pos_unit :
  forall {RI0 : RealInterfaceEnhanced}
         (reward : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0)
         (beta : @R RI0) (Hb : lt zero beta)
         (pi_ref : @S RI0 (@uab_ssUnit (@RI_base RI0)) -> @R RI0)
         (Hp : forall s : @S RI0 (@uab_ssUnit (@RI_base RI0)), lt zero (pi_ref s)),
    lt zero (@Z_align RI0 (@uab_ssUnit (@RI_base RI0)) (@uab_soUnit (@RI_base RI0))
                    reward beta Hb pi_ref).
Proof.
  intros RI0 reward beta Hb pi_ref Hp.
  unfold Z_align.
  apply uabd_uab_soUnit_sum_pos.
  intro s.
  exact (mult_positive (pi_ref s)
                       (@exp_neg RI0 (opp (mult (inv_pos beta Hb) (reward s))))
                       (Hp s)
                       (exp_neg_pos (opp (mult (inv_pos beta Hb) (reward s))))).
Qed.

Print Assumptions uabd_uab_soUnit_sum_pos.
Print Assumptions uabd_Z_align_pos_unit.
