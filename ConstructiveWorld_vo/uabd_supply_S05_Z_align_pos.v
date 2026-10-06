(* uabd_supply_S05_Z_align_pos.v —— 闭式对齐配分函数正性：一般接口层伴生供给定理 *)
(* 使命：S05_AlignmentGRPO Alignment 节 Z_align_pos 槽（lt zero Z_align）的
   伴生供给。Z_align 为闭式定义（pi_ref 与 exp_neg 因子逐点积的求和），
   其被积项逐点为正是接口正性字段（mult_positive、exp_neg_pos）的直接推论；
   本件将该槽消解为定理：由一般求和保正前提 Hsum 两跳构造链给出
   （逐点正性装配 → 求和保正实例化）。 *)
(* 依赖：S01_BaseRing（RealInterfaceEnhanced／SumOver 类字段）、
   S05_AlignmentGRPO（Z_align 闭式定义，End Alignment 后导出形）。 *)
(* 构造性：语句全 Set 层（lt 为 Set 值序）；证明为显式构造链，零公理、
   零承认、零经典逻辑；原槽陈述在此作为定理结论非平凡给出（引用库内
   真实字段供给链，非 assumption 重述）。 *)
(* 编译配方：coqc -q -Q <主 vo 树> "" -Q . "" uabd_supply_S05_Z_align_pos.v
   （COQLIB／ROCQLIB 全字面导出，9.1 工具链）。 *)

Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.

Theorem uabd_Z_align_pos_of_sum_pos :
  forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI} {SO : SumOver RI SS}
         (reward : @S RI SS -> @R RI) (beta : @R RI)
         (Hb : lt zero beta) (pi_ref : @S RI SS -> @R RI)
         (Hp : forall s : @S RI SS, lt zero (pi_ref s))
         (Hsum : forall f : @S RI SS -> @R RI,
                 (forall s : @S RI SS, lt zero (f s)) ->
                 lt zero (@sum_over_S RI SS SO f)),
    lt zero (Z_align reward beta Hb pi_ref).
Proof.
  intros RI SS SO reward beta Hb pi_ref Hp Hsum.
  unfold Z_align.
  apply Hsum.
  intro s.
  exact (mult_positive (pi_ref s)
                       (@exp_neg RI (opp (mult (inv_pos beta Hb) (reward s))))
                       (Hp s)
                       (exp_neg_pos (opp (mult (inv_pos beta Hb) (reward s))))).
Qed.

Print Assumptions uabd_Z_align_pos_of_sum_pos.
