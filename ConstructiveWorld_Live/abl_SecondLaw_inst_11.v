(* ==========================================================================)
   abl_SecondLaw_inst_11.v — SecondLawQuantified 节假设实例化（sumf:=list-sum 形；源件 ConstructiveWorld_Live/SecondLawQuantified.v，只读对照）
   使命: SlqSecondLaw 节（L48-346）五槽的实例化消融——sumf 具体化为
     real_list_sum（和函数），则节假设 sumpos/sumext/sumlinear/sumadd 全变为
     可证引理；T_pos 以具体 T:=real_plus real_one real_one（=2）数值实例化。
     S/energy 为纯数据位（无假设内容），以具体 X 承载。
   要点登记：(a) list-sum 读法下 sumpos 的正性须以非空表承载——沿源件
     消解块（L590-594）cons 形先例（语句面零 Prop），并导出源件留待的
     任意非空枚举形（abl11_sumpos_nonempty，l <> nil 前提位沿源件 Part 2
     主件 L356/L444 同款；该位系 Prop 前提承载桥，不入提取检验组）。
   (b) T:=2 取构造形 real_plus real_one real_one，T_pos 由 S02:3197
     real_lt_plus_compat × S07:6967 real_lt_zero_one 组合（0+0==0 沿
     S02:2348 real_plus_zero 运输）。
   (c) 节机头实例化见证缩减登记：拟用 UpReqTempDefs 的
     real_boltzmann_dist_temp（L154 六参位）做机头实例化，但其依赖链
     需先编 S14 大件（14,326 行，超时纪律下不入池）——五槽实例化本体不受
     影响；升级方向：入池后补一枚机头见证（调用形照源件 L70-73，填充件已在本件备好）。
   结构: Part 1 节形状机器锚五枚（源件 L51-67 槽形状逐字复刻为 Definition，
     类型检查=复刻忠实）；Part 2 四求和假设实例化（sumpos 独立构造链，
     零 False 消去；sumext/sumlinear/sumadd 由 S08 RealListSumMain 节四库件
     直接闭合）；Part 3 T:=2 实例化；Part 4 填充件（具体实例住入锚形=
     实例化机器判定）。
   依赖: S01_BaseRing–S08_RealMainlineDPO；Stdlib List、Extraction。
   构造性: 纯构造性零承认词面；语句面零 Prop（唯一 Prop 位=Hnil 桥前提，
     源件 Part 2 同款先例，显式登记）；全件 Qed 闭合；尾 Print Assumptions
     全 Closed；提取检验组（五主件+sumf 锚）Obj.magic=0。
   编译配方: 隔离池 /tmp/x12pool（S01-S08 真拷），cd /tmp/x12pool &&
     bash cpu_guard.sh -- rocq c -q -native-compiler no -Q /tmp/x12pool ""
     abl_SecondLaw_inst_11.v（cwd 异地、节流）。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.

(* ============================================================ *)
(* Part 1 · 节形状机器锚（源件 SecondLawQuantified.v L51-67 逐字复刻）    *)
(*   五枚锚形定义：类型检查通过=复刻忠实（S 改名 S0 防遮蔽，其余零改动）。  *)
(* ============================================================ *)

Definition abl11_shape_sumpos (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f : S0 -> Real),
    (forall s : S0, real_lt real_zero (f s)) -> real_lt real_zero (sumf f).

Definition abl11_shape_sumext (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f g : S0 -> Real),
    (forall s : S0, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).

Definition abl11_shape_sumlinear (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (a : Real) (f : S0 -> Real),
    real_eq (sumf (fun s : S0 => real_mult a (f s))) (real_mult a (sumf f)).

Definition abl11_shape_sumadd (S0 : Type) (sumf : (S0 -> Real) -> Real) :=
  forall (f g : S0 -> Real),
    real_eq (sumf (fun s : S0 => real_plus (f s) (g s)))
            (real_plus (sumf f) (sumf g)).

Definition abl11_shape_T_pos (T0 : Real) := real_lt real_zero T0.

(* ============================================================ *)
(* Part 2 · sumf 实例读法 + 四求和假设实例化                              *)
(*   abl11_sumf X l := real_list_sum X f l（S08 RealListSumMain 节       *)
(*   L281 Fixpoint，节闭后 X 首参）。                                     *)
(* ============================================================ *)

Definition abl11_sumf (X : Type) (l : list X) (f : X -> Real) : Real :=
  real_list_sum X f l.

(* ---- 槽 1 · sumpos（cons 形主实例化；独立构造链，零 False 消去）-------- *)
(*   构造链：单元素表 f x + 0 沿 real_plus_zero 运输即 f x > 0             *)
(*   （S08 real_list_sum_pos 单元素案同款）；多元素表两项皆正 ⟹ 和正      *)
(*   （S02 real_lt_plus_compat 见证加法）。nil 分支零触及（cons 形下      *)
(*   不可达），故全链无 False 消去、提取面干净。                           *)
Lemma abl11_listsum_pos_aux : forall (X : Type) (l : list X) (f : X -> Real),
  (forall s : X, real_lt real_zero (f s)) ->
  forall x : X, real_lt real_zero (real_list_sum X f (cons x l)).
Proof.
  intros X l.
  induction l as [| y rest IH]; intros f Hf x; simpl.
  - (* cons x nil：f x + 0 == f x 沿 eq 运输（S08 单元素案同款） *)
    apply (RealSetoid.real_lt_id_r real_zero (f x) (real_plus (f x) real_zero)).
    + apply (real_eq_sym (real_plus (f x) real_zero) (f x)).
      apply (real_plus_zero (f x)).
    + exact (Hf x).
  - (* cons x (y::rest)：0+0 < f x + (f y + Σrest)，下界沿 plus_zero 运输 *)
    apply (RealSetoid.real_lt_compat
             (real_plus real_zero real_zero) real_zero
             (real_plus (f x) (real_plus (f y) (real_list_sum X f rest)))
             (real_plus (f x) (real_plus (f y) (real_list_sum X f rest)))).
    + exact (real_plus_zero real_zero).
    + apply real_eq_refl.
    + exact (real_lt_plus_compat real_zero (f x) real_zero
               (real_plus (f y) (real_list_sum X f rest)) (Hf x) (IH f Hf y)).
Qed.

Theorem abl11_sumpos : forall (X : Type) (f : X -> Real) (x : X) (l : list X),
  (forall s : X, real_lt real_zero (f s)) ->
  real_lt real_zero (abl11_sumf X (cons x l) f).
Proof.
  intros X f x l Hf.
  unfold abl11_sumf.
  exact (abl11_listsum_pos_aux X l f Hf x).
Qed.

(* 槽 1 补全 · 源件消解块留待位导出：任意非空枚举形（l <> nil 前提位，     *)
(*   源件 Part 2 主件 L356/L444 语句面同款先例；Prop 前提承载桥，不入      *)
(*   提取检验组）。                                                       *)
Theorem abl11_sumpos_nonempty : forall (X : Type) (l : list X) (f : X -> Real),
  l <> nil ->
  (forall s : X, real_lt real_zero (f s)) ->
  real_lt real_zero (abl11_sumf X l f).
Proof.
  intros X l f Hnn Hf.
  destruct l as [| x l0].
  - exfalso. exact (Hnn eq_refl).
  - unfold abl11_sumf. exact (abl11_listsum_pos_aux X l0 f Hf x).
Qed.

(* ---- 槽 2 · sumext（S08:296 逐点外延件直接闭合）---------------------- *)
Theorem abl11_sumext : forall (X : Type) (l : list X) (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (abl11_sumf X l f) (abl11_sumf X l g).
Proof.
  intros X l f g H.
  unfold abl11_sumf.
  exact (real_list_sum_ext X f g l H).
Qed.

(* ---- 槽 3 · sumlinear（S08:363 系数提出件直接闭合）-------------------- *)
Theorem abl11_sumlinear : forall (X : Type) (l : list X) (a : Real) (f : X -> Real),
  real_eq (abl11_sumf X l (fun s : X => real_mult a (f s)))
          (real_mult a (abl11_sumf X l f)).
Proof.
  intros X l a f.
  unfold abl11_sumf.
  exact (real_list_sum_linear X a f l).
Qed.

(* ---- 槽 4 · sumadd（S08:341 逐点加法分配件直接闭合）------------------- *)
Theorem abl11_sumadd : forall (X : Type) (l : list X) (f g : X -> Real),
  real_eq (abl11_sumf X l (fun s : X => real_plus (f s) (g s)))
          (real_plus (abl11_sumf X l f) (abl11_sumf X l g)).
Proof.
  intros X l f g.
  unfold abl11_sumf.
  exact (real_list_sum_add X f g l).
Qed.

(* ============================================================ *)
(* Part 3 · 槽 5 · T_pos（T:=2 口径实例化）                               *)
(*   two := real_plus real_one real_one；0+0 < 1+1 由 real_lt_zero_one   *)
(*   双肢加性组合（S02:3197），下界 0+0==0 沿 S02:2348 运输。             *)
(* ============================================================ *)

Definition abl11_T : Real := real_plus real_one real_one.

Theorem abl11_T_pos : real_lt real_zero abl11_T.
Proof.
  unfold abl11_T.
  apply (RealSetoid.real_lt_compat (real_plus real_zero real_zero) real_zero
           (real_plus real_one real_one) (real_plus real_one real_one)).
  - exact (real_plus_zero real_zero).
  - apply real_eq_refl.
  - exact (real_lt_plus_compat real_zero real_one real_zero real_one
             real_lt_zero_one real_lt_zero_one).
Qed.

(* ============================================================ *)
(* Part 4 · 填充件：具体实例住入节形状锚（实例化的机器判定面）             *)
(*   五枚填充件类型即 Part 1 锚形在 sumf:=abl11_sumf X l / T:=abl11_T     *)
(*   处的实例——类型检查通过=具体读法逐字满足节假设形状（形状对应说明     *)
(*   的机器证）。定义件（无 Qed，类型检查即其验证）。                     *)
(* ============================================================ *)

Definition abl11_fill_sumpos (X : Type) (x : X) (l : list X) :
  abl11_shape_sumpos X (abl11_sumf X (cons x l)) :=
  fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
    abl11_sumpos X f x l Hf.

Definition abl11_fill_sumext (X : Type) (l : list X) :
  abl11_shape_sumext X (abl11_sumf X l) :=
  fun (f g : X -> Real) (H : forall s : X, real_eq (f s) (g s)) =>
    abl11_sumext X l f g H.

Definition abl11_fill_sumlinear (X : Type) (l : list X) :
  abl11_shape_sumlinear X (abl11_sumf X l) :=
  fun (a : Real) (f : X -> Real) => abl11_sumlinear X l a f.

Definition abl11_fill_sumadd (X : Type) (l : list X) :
  abl11_shape_sumadd X (abl11_sumf X l) :=
  fun (f g : X -> Real) => abl11_sumadd X l f g.

Definition abl11_fill_T_pos : abl11_shape_T_pos abl11_T := abl11_T_pos.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                               *)
(*   对账三联：定理名清单 7 = Qed 计数 7 = PA 语句 7，零差。              *)
(*   定理 7：abl11_listsum_pos_aux / abl11_sumpos / abl11_sumpos_nonempty *)
(*           / abl11_sumext / abl11_sumlinear / abl11_sumadd / abl11_T_pos *)
(*   定义件 12（无 Qed，类型检查即验证）：abl11_sumf / 五 shape 锚 /      *)
(*           五 fill 填充 / abl11_T。                                     *)
(* ============================================================ *)

Print Assumptions abl11_listsum_pos_aux.
Print Assumptions abl11_sumpos.
Print Assumptions abl11_sumpos_nonempty.
Print Assumptions abl11_sumext.
Print Assumptions abl11_sumlinear.
Print Assumptions abl11_sumadd.
Print Assumptions abl11_T_pos.

(* 提取检验组（六条；判据=合并输出 Obj.magic 计数 0）：
   五主实例化件 + sumf 锚（纯 Fixpoint）。Hnil 桥不入组（头注登记）。 *)
Recursive Extraction abl11_sumf.
Recursive Extraction abl11_sumpos.
Recursive Extraction abl11_sumext.
Recursive Extraction abl11_sumlinear.
Recursive Extraction abl11_sumadd.
Recursive Extraction abl11_T_pos.
