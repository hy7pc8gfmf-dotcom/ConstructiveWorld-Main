(* 五字段指针｜模块：LW2MetricCompat.v。
   数学使命：度量对柯西等价的无损性（保距兼容）。若实数 X 与 Y 柯西等价（real_eq），
   则 X 到有理点 q 的距离 real_metric X (real_const q) 与 Y 到 q 的距离
   real_metric Y (real_const q) 作为实数相等（real_eq）。证明逐 eps 构造：取
   real_eq X Y 在 eps 处的模量 N1 作同模量见证；逐点经 lic_metric_proj 将两侧距离
   投影归约为 Qabs (projT1 X n - q) 与 Qabs (projT1 Y n - q)；由 q_abs_abs_triangle
   得 ||X_n − q| − |Y_n − q|| ≤ |X_n − Y_n|（差式经 ring 重整），以 Qle_lt_trans
   收束于 eps。
   依赖：S01_BaseRing（Set 层 NatLe）、S02_CauchyComplete（Real/real_eq/real_const/
   QltT/QltT_to_Qlt/Qlt_to_QltT）、S03_QExp（real_metric、q_abs_abs_triangle），
   UpReqIrrationalCriterion（lic_metric_proj 逐点投影归约）。
   对标：Bishop 构造分析中度量函数沿柯西等价的无损性（距离实数逐 eps 相等）；
   与 LW2SepTransport.v 的逐 eps 投影归约工艺同源。
   构造性：语句面全 Set 层（real_eq 为 Set 值逐 eps 数据，恒等取 Qeq），零承认、
   零经典逻辑、Require 面不引公理模块；证明体仅用三角不等式与等式重整。
   编译配方：coqc -native-compiler no -q -Q . ""
   -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""
   LW2MetricCompat.v，工作目录本沙箱；COQLIB 与 ROCQLIB 环境变量同值指向
   Rocq 9.1 库根。
*)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Opaque Qred.

(* 保距兼容：柯西等价的两个实数到同一有理点的距离作为实数相等 *)
Lemma lw2t_metric_compat : forall (X Y : Real) (q : Q),
  real_eq X Y ->
  real_eq (real_metric X (real_const q)) (real_metric Y (real_const q)).
Proof.
  intros X Y q Heq.
  unfold real_eq. intros eps Heps.
  destruct (Heq eps Heps) as [N1 HN1].
  exists N1. intros n Hn.
  apply Qlt_to_QltT.
  rewrite (lic_metric_proj X q n).
  rewrite (lic_metric_proj Y q n).
  pose proof (HN1 n Hn) as Hd.
  apply QltT_to_Qlt in Hd.
  apply (Qle_lt_trans _ (Qabs (projT1 X n - projT1 Y n))).
  - pose proof (q_abs_abs_triangle (projT1 X n - q)%Q (projT1 Y n - q)%Q) as Htri.
    assert (Hring : ((projT1 X n - q) - (projT1 Y n - q) ==
                     projT1 X n - projT1 Y n)%Q) by ring.
    rewrite Hring in Htri. exact Htri.
  - exact Hd.
Qed.

Print Assumptions lw2t_metric_compat.
