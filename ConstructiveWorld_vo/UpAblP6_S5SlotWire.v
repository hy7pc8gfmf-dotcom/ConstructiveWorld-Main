(* ===================================================================== *)
(* UpAblP6_S5SlotWire.v —— S5SlotWire 接口参数的具体实例供给件           *)
(* 使命：为上游 S5SlotWire 的已证定理供给具体数据（实例供给，零新数学），  *)
(*       使抽象结论在具体数据上真实求值：协方差单位点正性与恒等式、产率    *)
(*       单位权重、宏观损耗单调的 of_nat 三前提实现与两步轨道点、Q 层      *)
(*       η=μ=x₀=1/2 数值衰减的闭式求值。                                 *)
(* 依赖：S01_BaseRing、fa56_id_carrier、fa56c_ext、PhysPredAblation、      *)
(*       p4a_GradSignQDec、S5SlotWire；stdlib QArith_base/Qring/Qabs/      *)
(*       Lists.List。构造性注记：语句面全在本库 Set 层；上游声明全         *)
(*       Defined（可执行求值面）；全件 Qed 收束；零公理零承认。编译配方：   *)
(*       coqc 9.1 直调，cpu_guard 温控，-o 临时目录，树内零写入。           *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56c_ext.
Require Import PhysPredAblation.
Require Import p4a_GradSignQDec.
Require Import S5SlotWire.
From Stdlib Require Import QArith_base Qring Qabs.
From Stdlib Require Import Lists.List.

(* ============ §1 节内四组具体实例（协方差/恒等/产率/宏观损耗） ========== *)

Section UasswFeed.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le   := @le RI.
Let lt   := @lt RI.

(* ---- 实例一（协方差单位点正性：uassw_covariance_unit_pos） -----------
   给出数据 D := one、H_inv := one（接口单位点），正性前提由
   one_pos 与 one_pos 提供——上游引理 ssw_covariance_pos 在该具体数据上
   实例化消解，结论 lt zero (fa56_covariance one one) 即单位点协方差
   正性实例。证明链经 fa56_covariance_pos（mult_positive）在本点闭合；
   单位点双正的具体选取为本文供给。 ---- *)
Theorem uassw_covariance_unit_pos : lt zero (fa56_covariance one one).
Proof.
  exact (ssw_covariance_pos one one one_pos one_pos).
Qed.

(* ---- 实例二（恒等式单位点求值：uassw_fluctuation_unit_id） -----------
   给出数据 D := one、H_inv := one。fa56_covariance 在该点定义性展开为
   mult one one，恒等由构造子 id_refl 直接给出——
   恒等两臂逐位同型（定义性展开级，如实注记）。 ---- *)
Theorem uassw_fluctuation_unit_id : Id (fa56_covariance one one) (mult one one).
Proof.
  exact id_refl.
Qed.

(* ---- 实例三（产率单位权重：uassw_entropy_production_unit） -----------
   给出数据 Flx := unit、TD := unit、w := 常一权重、theta := 常一势、
   J := tt、X := tt。fa56c 产率定义（权重×势）在该点求值：
   常一×常一＝mult one one，恒等经上游引理 ssw_entropy_production_rate
   实例化后按 β 规约闭合。 ---- *)
Theorem uassw_entropy_production_unit :
  Id (fa56c_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt)
     (mult one one).
Proof.
  exact (ssw_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt).
Qed.

(* ---- 实例四（of_nat 三前提具体实现：uassw_macro_loss_zero_step2） -----
   给出数据：nat_to_R 具体实现（零元 zero、步进 plus·one 的
   nat 递归构造，泛型于接口），三个前提逐一构造为独立 Qed 引理：
   零元恒等（iota 求值）、步进恒等（iota 求值）、非负性（归纳＋
   plus_le_lt_pos 在具体点合成），再应用于 ssw_macro_loss_monotone
   于 m0 := zero、t := 2 的两步轨道点。 ---- *)
Fixpoint nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S m => plus (nat_to_R m) one
  end.

Theorem uassw_nat_to_R_zero_id : Id (nat_to_R O) zero.
Proof.
  exact id_refl.
Qed.

Theorem uassw_nat_to_R_step :
  forall n : nat, Id (nat_to_R (Datatypes.S n)) (plus (nat_to_R n) one).
Proof.
  intro n.
  exact id_refl.
Qed.

Theorem uassw_nat_to_R_nonneg : forall n : nat, le zero (nat_to_R n).
Proof.
  induction n as [| m IH].
  - apply le_refl.
  - apply lt_le_iff.
    apply inl.
    apply plus_le_lt_pos.
    * exact IH.
    * apply one_pos.
Qed.

Theorem uassw_macro_loss_zero_step2 :
  le (ppa_macro_loss (iterate ppa_macro_dynamics (Datatypes.S (Datatypes.S O)) zero))
     (ppa_macro_loss zero).
Proof.
  exact (ssw_macro_loss_monotone nat_to_R
           uassw_nat_to_R_zero_id uassw_nat_to_R_step uassw_nat_to_R_nonneg
           zero (Datatypes.S (Datatypes.S O))).
Qed.

End UasswFeed.

(* ============ §2 Q 层数值实例（η=μ=x₀=1/2 与闭式求值伴随引理） ========== *)

Open Scope Q_scope.

(* ---- 实例五（Q 数值：eta := 1/2、mu := 1/2、x0 := 1/2、n := 0、k := 1） -
   给出数据：ημ ＝ 1/4 ＜ 1（收缩系数 κ ＝ 3/4 落于 (0,1)），三个前提
   逐件由 Q 层有序比较计算闭合；上游引理 ssw_full_sign_decay_instance_ref
   在该闭式点实例化出数值衰减不等式。 ---- *)
Theorem uassw_full_sign_decay_half :
  Qle (Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) (O + Datatypes.S O) (1#2))))
      (gsq_pow (gsq_kappa (1#2) (1#2)) (Datatypes.S O)
         * Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) O (1#2)))).
Proof.
  apply (ssw_full_sign_decay_instance_ref (1#2) (1#2) (1#2) O (Datatypes.S O)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ---- 闭式求值伴随引理三件：具体数据经 Defined 定义体算至有理数 -------
   κ(1/2,1/2) ＝ 3/4、g(1/2) ＝ 1/4、轨道一步 x₁ ＝ 3/8——
   gsq_step 三分支判定（stdlib 构造性三分，Defined 透明）在该点
   真实求值，结论逐位为字面有理数（经 Qeq 交叉积比较闭合）。 ---- *)
Theorem uassw_kappa_half_eval : gsq_kappa (1#2) (1#2) == (3#4).
Proof.
  vm_compute. reflexivity.
Qed.

Theorem uassw_grad_half_eval : gsq_grad (1#2) (1#2) == (1#4).
Proof.
  vm_compute. reflexivity.
Qed.

Theorem uassw_iter_half_step_eval : gsq_iter (1#2) (1#2) (Datatypes.S O) (1#2) == (3#8).
Proof.
  vm_compute. reflexivity.
Qed.

Close Scope Q_scope.

(* ============ 收尾核验（Print Assumptions 逐件 Closed） ================ *)

Print Assumptions uassw_covariance_unit_pos.
Print Assumptions uassw_fluctuation_unit_id.
Print Assumptions uassw_entropy_production_unit.
Print Assumptions uassw_nat_to_R_zero_id.
Print Assumptions uassw_nat_to_R_step.
Print Assumptions uassw_nat_to_R_nonneg.
Print Assumptions uassw_macro_loss_zero_step2.
Print Assumptions uassw_full_sign_decay_half.
Print Assumptions uassw_kappa_half_eval.
Print Assumptions uassw_grad_half_eval.
Print Assumptions uassw_iter_half_step_eval.
