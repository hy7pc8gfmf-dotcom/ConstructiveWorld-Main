(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabT9_tvd_ctx_minorization（原 L31，2 句玩具证）                     *)
(*   uabT9_tvd_ctx_Krow（原 L17，2 句玩具证）                             *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblT9_UpTVDoeblin.v —— TV 全变差面 Doeblin 证书前置引理：tvd_K 具体   *)
(*   实例上的行归一化与最小化界，对应 UpTVDoeblin 的 K_row 与            *)
(*   UpTVDoeblin 的 minorization（δ*·u ≤ K）。                           *)
(* 供体：tvd_K_row、tvd_minorization              *)
(*   （δ* = e^{−2γ/T}），于具体实例直接实例化消解。                      *)
(* 依赖：CW_ConstructiveWorld_219、UpTVDoeblin（只读使用，原树零改）。    *)
(* 构造性注记：零承认（Qed 闭合，文末 Print Assumptions 审计）；Set 层    *)
(*   承载；可提取。编译配方：coqc 9.1 直调无 -Q，cpu_guard 包裹，         *)
(*   -o 临时目录（树内 .vo 不动）。                                      *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.
From Stdlib Require Import List.

(* 即 tvd_K_row@UpTVDoeblin:1743 于 K := tvd_K 具体实例的实例化消解 *)
Theorem uabT9_tvd_ctx_Krow :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp)
         (z : list Real -> list Real -> Real) (i : list Real),
    real_eq (real_list_sum (list Real) (tvd_K states n_pos Ttemp Ttemp_pos z i)
               states)
            real_one.
Proof.
  intros states n_pos Ttemp Ttemp_pos z i.
  exact (tvd_K_row states n_pos Ttemp Ttemp_pos z i).
Qed.

(* 即 tvd_minorization@UpTVDoeblin:1933，取 δ*:=tvd_dstar、u:=tvd_u、K:=tvd_K *)
Theorem uabT9_tvd_ctx_minorization :
  forall (states : list (list Real))
         (n_pos : real_lt real_zero (real_of_nat (length states)))
         (Ttemp : Real) (Ttemp_pos : real_lt real_zero Ttemp) (gamma : Real)
         (z : list Real -> list Real -> Real),
    (forall i j : list Real, real_le (real_opp gamma) (z i j)) ->
    (forall i j : list Real, real_le (z i j) gamma) ->
    forall i j : list Real,
      real_le (real_mult (tvd_dstar Ttemp Ttemp_pos gamma)
                         (tvd_u states n_pos j))
              (tvd_K states n_pos Ttemp Ttemp_pos z i j).
Proof.
  intros states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j.
  exact (tvd_minorization states n_pos Ttemp Ttemp_pos gamma z Hlb Hub i j).
Qed.

(* 假设审计：两定理 Print Assumptions 应为空 *)
Print Assumptions uabT9_tvd_ctx_Krow.
Print Assumptions uabT9_tvd_ctx_minorization.
