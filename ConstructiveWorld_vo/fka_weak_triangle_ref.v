(* ===== fka_weak_triangle_ref.v ===== *)
(* fka_weak_triangle_ref.v —— 二元 Gram 不等式核实例化引述件 *)
(* 使命：二元 Gram 不等式核 (ac+bd)² ≤ (a²+b²)(c²+d²) 在实数层的实例化；
   语句面逐字照录 ForwardKLAdjudication.v 定格区（三 Require ＋ Theorem ＋ exact 直接给出被引主件）。
   被引主件 = WeakTriangleClose.wtc_weak_triangle_load（Section WeakTriangleLoad
   花括号上下文出节后的形式：双隐最大插入 @wtc ?RI ?DO，DO 型=DecidableOrder(@RI_base ?RI)。
   调形注记：定格区 exact 直接裸名调用与该形参数个数失配，故本件在证明内
   intros 五参后以 @ 全显给出 wtc_weak_triangle_load，语句面零改动。
   范围如实注记：本件所证内容为二元 Gram 核
   (ac+bd)² ≤ (a²+b²)(c²+d²) 的实数层实例，并非 KL 弱三角真形本体
   wtl_cond_triangle（后者仍是唯一真形，
   见 ForwardKLAdjudication §二 件 1，UpReqWeakTriangle）。
   构造性注记：语句面零公理零承认——本件唯一定理由被引主件直接给出，无新证明面、
   无新声明、无经典逻辑面。
   依赖 Require：S01_BaseRing、fa53_compat_abs、WeakTriangleClose；
   Local Existing Instance RI_base 为裸名 R/plus/mult/le 顶层解析前提。
   编译配方：Rocq 9.1 coqc 直调，cpu_guard 包裹，-o 输出临时目录，树内零写入。 *)

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
