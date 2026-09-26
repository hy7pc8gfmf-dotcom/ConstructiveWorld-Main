(* ==========================================================================)
   ToyR_fka_weak_triangle_ref.v — 二元 Gram 不等式核的实数层实例化引述件
   使命: (ac+bd)² ≤ (a²+b²)(c²+d²) 的实数层实例：语句面逐字照录 ForwardKLAdjudication 定格区，由被引主件 wtc_weak_triangle_load（@ 全显调用）直接给出；范围如实注记为 Gram 核实例而非 KL 弱三角本体。
   依赖: S01_BaseRing、fa53_compat_abs、WeakTriangleClose；Local Existing Instance RI_base。
   对标: Cauchy–Schwarz 不等式的二元实数实例。
   构造性: 语句面零公理零承认词面——唯一定理由被引主件直接给出，无新证明面、无新声明、无经典逻辑。
   编译配方: Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。
   ========================================================================== *)

Require Import S01_BaseRing. Require Import fa53_compat_abs.
Require Import WeakTriangleClose.
(* 裸名 R/plus/mult/le 顶层解析前提补注（S01／WeakTriangleClose 同款定式；
   缺此行时顶层展开报 Could not find an instance for RealInterface，
   补此一行即合，语句面仍逐字）： *)
Local Existing Instance RI_base.
Theorem fka_weak_triangle_ref :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI)
         (a b c d : R),
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof. intros RI DO a b c d. exact (@wtc_weak_triangle_load RI DO a b c d). Qed.

Print Assumptions fka_weak_triangle_ref.
