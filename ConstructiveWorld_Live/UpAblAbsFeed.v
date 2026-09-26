(* ==========================================================================)
   UpAblAbsFeed.v — 实数有限表和的绝对值上界三推论并列
   使命: 逐 eps 形 |Σ_l f| ≤ Σ_l |f| + eps、B 形（real_le_b 谓词）、及由 B 形经提升引理得到的逐 eps 形（结论相同、路线不同）。
   依赖: CW_ConstructiveWorld_219、UpRealLeB、S08_RealMainlineDPO、UpAblAbsSumLeB、UpAblAbsSumLeB2、UpAblAbsSumLeEps、Stdlib List。
   对标: mathlib 有限和三角不等式（abs_sum_le 一类）的构造实数对应物。
   构造性: 三结论语句面均为序谓词 real_le/real_le_b（Set 层值）；全件 Qed 闭合、零承认词面、无经典逻辑；文末逐一 Print Assumptions 全 Closed。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树原地重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB.
Require Import UpAblAbsSumLeB2.
Require Import UpAblAbsSumLeEps.
From Stdlib Require Import List.

(* ============================================================ *)
(* §1 · 供体引理在库核对：以下 Check 逐一确认供体签名在库                 *)
(* ============================================================ *)

Check uabS4_abs_list_sum_le_B.    (* B 形：|Σ_l f| ≤_B Σ_l |f|（real_le_b 版） *)
Check uabS4_abs_list_sum_le_eps.  (* 逐 eps 全称：0 < eps ⟹ |Σ_l f| ≤ Σ_l |f| + eps *)
Check uabS4b_slot_abs_sum_le_B.   (* 抽象求和接口下的 B 形（供 uabf_kv_abs_triangle_list_B 实例化） *)
Check uabS4e_bform_to_eps.        (* 提升引理：B 形与 0 < eps ⟹ 逐 eps 形 *)
Check real_list_sum.              (* 表和定义：nil 归 real_zero，cons 递归求和 *)

(* ============================================================ *)
(* §2 · 逐 eps 形主推论：|Σ_l f| ≤ Σ_l |f| + eps（0 < eps）              *)
(* ============================================================ *)

Corollary uabf_kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real)
  (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  exact (uabS4_abs_list_sum_le_eps X f l eps Heps).
Qed.

(* ============================================================ *)
(* §3 · 第二路线：B 形推论与经 uabS4e_bform_to_eps 的提升                *)
(* ============================================================ *)

(* uabf_kv_abs_triangle_list_B：将表和 real_list_sum 代入
   uabS4b_slot_abs_sum_le_B 的抽象求和接口——nil 与 cons 两方程均定义性成立，B 形直接推得。 *)
Corollary uabf_kv_abs_triangle_list_B : forall (X : Type) (f : X -> Real)
  (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x : X => real_abs (f x)) l).
Proof.
  intros X f l.
  exact (uabS4b_slot_abs_sum_le_B X (real_list_sum X)
           (fun f0 => real_eq_refl real_zero)
           (fun f0 w rest =>
              real_eq_refl (real_plus (f0 w) (real_list_sum X f0 rest)))
           f l).
Qed.

(* uabf_kv_abs_triangle_list_eps_slotroute：由 B 形经 uabS4e_bform_to_eps
   提升为逐 eps 形，与 uabf_kv_abs_triangle_list_eps 结论相同、证明路线不同。 *)
Corollary uabf_kv_abs_triangle_list_eps_slotroute :
  forall (X : Type) (f : X -> Real) (l : list X) (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l eps Heps.
  apply (uabS4e_bform_to_eps _ _ eps Heps).
  exact (uabf_kv_abs_triangle_list_B X f l).
Qed.

(* ============================================================ *)
(* §4 · 假设审计：三条结论的 Print Assumptions 应全为 Closed              *)
(* ============================================================ *)
Print Assumptions uabf_kv_abs_triangle_list_eps.
Print Assumptions uabf_kv_abs_triangle_list_B.
Print Assumptions uabf_kv_abs_triangle_list_eps_slotroute.
