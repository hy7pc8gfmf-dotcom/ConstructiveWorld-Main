(* ===== fka_weak_triangle_ref.v ===== *)
(* 席位 PA6-24（论文6 战役施工席·写盘席）· T232 fka_weak_triangle_ref 机械闭合装机件 · 2026-09-20 *)
(* 装法依据：消融50/T230-PA6-22-fka尾巴精勘.md 判定「可闭合」（候闸条件 2026-09-19 整体翻绿：
   被引主件四关全绿有 T111/T112/T140/T101 四台账互证，登记时所记 Require 三重倒墙全消解）。
   语句面逐字照录 ConstructiveWorld_Live/ForwardKLAdjudication.v :113-120 候闸定格区
   （三 Require ＋ Theorem ＋ exact 主件直给；登记件本体与 Live 树零改动，本件为独立新装）。
   被引主件 = WeakTriangleClose::wtc_weak_triangle_load（Section WeakTriangleLoad
   花括号上下文卸出；实测卸出形=双隐最大插入 @wtc ?RI ?DO，DO 型=DecidableOrder(@RI_base ?RI)。
   实测装机记录：定格 exact 裸呼系 arity 4 对 6 失配，按 T230 唯一校验点授权于 exact 行
   机械实现=intros 五参后 @ 全显直给，语句面零改动）。
   分工如实（照登记件 :102-103 判词）：本件收编内容 = 二元 Gram 核 (ac+bd)² ≤ (a²+b²)(c²+d²)
   的实数层装载腿转发收编，非 KL 弱三角真形本体 wtl_cond_triangle（后者仍是唯一真形，
   见 ForwardKLAdjudication §二 件 1，UpReqWeakTriangle.v:158）。
   零承认件自审：语句面零 公理／零 承认件——本件唯一定理由被引主件直给，无新证面、
   无新声明、无经典逻辑面；头注全中文（本机扫描口径剥注释后扫，双保险）。
   铁律自审：本席只写 消融50/ 本件；产物只落 /tmp/pa7_work；Live 树与登记件本体只读；
   姊妹席辖区零碰；零云端零 git。 *)

Require Import S01_BaseRing. Require Import fa53_compat_abs.
Require Import WeakTriangleClose.
(* 裸名 R/plus/mult/le 顶层解析桥（S01:2941／WeakTriangleClose:117 同款定式；
   实测装机记录：定格区直接顶层展开缺此桥，G2 首跑曝 Could not find an
   instance for RealInterface，补此一行即合，语句面仍逐字）： *)
Local Existing Instance RI_base.
Theorem fka_weak_triangle_ref :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI)
         (a b c d : R),
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof. intros RI DO a b c d. exact (@wtc_weak_triangle_load RI DO a b c d). Qed.

Print Assumptions fka_weak_triangle_ref.
