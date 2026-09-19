(* ============================================================ *)
(* UpAblT13b_UpTVDoeblin.v —— 假设消融战役 T13b 承接席（批7 TV 面一位）        *)
(* 辖区：UpTVDoeblin.v 一位（T13a 移交单 §6 批7 行点名）：                       *)
(*   位1 UpTVDoeblin.v:458  delta_le_one（TVRealWorld 交叠距离上界位）           *)
(* 批7 第 2 位裁决（T13a 移交「1 位普查未逐行列明（待勘）」）：本席逐行实测       *)
(*   UpTVDoeblin 全档假设位恰 22 位（:208/:448-463/:1623-1631），普查表内        *)
(*   逐行位 N3/T18/W1 与表头 N4/T17/W1 自不一致——第 4 位无坐标可认列，           *)
(*   最近候选 n_pos@:449 证书供给形普查已判T；按逐行实测为准，批7 实收 1 位，     *)
(*   计数勘误随账（fail-loud 不硬凑）。                                          *)
(* 被消融位语句（现档逐字）：                                                    *)
(*   :458 Variable delta_le_one : real_le delta real_one.                        *)
(* 放电母本：rta_delta_le_one_of_minorization@RateTheoryAblation:60              *)
(*   （出节全参形：K_row/u_norm/minorization 三前提全参喂入，P7B 判例）。          *)
(* 消融形（诚实登记）：实载体语句面自足（real_list_sum 族），零实例装配，          *)
(*   母本三前提显式参直喂。                                                      *)
(* 分级：N1（库内放电件直喂，前提显式参）。                                      *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、RateTheoryAblation。     *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                           *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import RateTheoryAblation.
From Stdlib Require Import List.

(* 位1 ←:458（minorization 消去链直喂；K_row/u_norm/minorization 前提显式参） *)
Theorem uabT13b_tv_delta_le_one :
  forall (states : list (list Real)) (K : list Real -> list Real -> Real)
         (u : list Real -> Real) (delta : Real),
    (forall i : list Real,
       real_eq (real_list_sum (list Real) (K i) states) real_one) ->
    real_eq (real_list_sum (list Real) u states) real_one ->
    (forall i j : list Real, real_le (real_mult delta (u j)) (K i j)) ->
    real_le delta real_one.
Proof.
  intros states K u delta HKrow Hunorm Hmin.
  exact (@rta_delta_le_one_of_minorization states K u delta HKrow Hunorm Hmin).
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_tv_delta_le_one.
