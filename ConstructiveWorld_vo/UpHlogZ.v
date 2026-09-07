(* ============================================================ *)
(* UpHlogZ.v —— 根内 KLProjection 主定理 HlogZ 前提的 Real 层总放电   *)
(*                                                              *)
(* 目标：projected_distribution_minimizes_kl（KLProjection.v L189）  *)
(* 的显式前件 HlogZ : le (log Z_aud) zero 在 Real 层总是成立：        *)
(*   Z_aud ≤ 1（Z_aud_le_one，根内已证）                           *)
(*   ⟹ log Z_aud ≤ log 1 = 0                                      *)
(*     （log 单调 le 版 = UpLogMono.real_log_le_mono；              *)
(*       log 1 == 0 = real_log_one，根内已证）。                    *)
(*                                                              *)
(* 交付清单：                                                      *)
(*   hlogz_discharge       —— 主放电：0 < Z ≤ 1 ⟹ log Z ≤ 0        *)
(*   hlogz_discharge_full  —— 同型对齐版（走 UpLogMono 直用形态）    *)
(*   hlogz_strict          —— 严格版：0 < Z < 1 ⟹ log Z < 0         *)
(*                            （过滤器确实拦截了质量）               *)
(*   hlogz_opp_nonneg      —— KL 尾项形态：0 ≤ opp (log Z)          *)
(*                            （主定理证明中 opp_le_compat 的直接输入）*)
(*                                                              *)
(* 全部 Real 层、Set 层语句（real_lt / real_le / real_eq，Or 编码）、 *)
(* 纯构造、全 Qed 闭合、可提取。                                    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ================================================================ *)
(* 主交付 1：HlogZ 放电（log 单调 le 版直推）                          *)
(*   论证：0 < Za、Za ≤ 1 ⟹ real_log Za ≤ real_log 1 == 0。           *)
(*   real_log_le_mono : real_le a b -> real_le (log a) (log b)       *)
(*   （a b 皆正前提由 HZa 与 real_lt_zero_one 供给）。                 *)
(* ================================================================ *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* 经中项 real_log 1 的 le 链合成 *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* 单调 le 版：Za ≤ 1 ⟹ log Za ≤ log 1 *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* log 1 == 0 经 eq → le 桥（inr 支）升 le *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* ================================================================ *)
(* 主交付 2：HlogZ 放电完整版（与 KLProjection 前件对齐）               *)
(*   同型语句，走 UpLogMono 直用形态 real_log_le_zero_of_le_one，      *)
(*   双路互证（单调链合成 / 直用形态殊途同归）。                        *)
(* ================================================================ *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* ================================================================ *)
(* 附加交付 1：严格版——过滤器确实拦截了质量                            *)
(*   0 < Za < 1 ⟹ log Za < log 1 = 0（lt 严格链）。                   *)
(*   real_log_lt_mono 论 cw_log；real_log 定义性展开（:= cw_log）后    *)
(*   逐项对接，尾端经 real_lt_eq_lt 把 log 1 换成 0。                  *)
(* ================================================================ *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* 严格单调：Za < 1 ⟹ cw_log Za < cw_log 1 *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* cw_log 1 == 0 *)
    exact (real_log_one Hone).
Qed.

(* ================================================================ *)
(* 附加交付 2：KL 尾项形态——0 ≤ opp (log Z)                           *)
(*   主定理证明里「尾项 T == opp (log Z_aud) ≥ 0」的直接 Real 层供给：  *)
(*   log Z ≤ 0 经 opp 反变（real_opp_le_compat）→ opp 0 ≤ opp (log Z)，*)
(*   再用 opp 0 == 0 的 eq → le 桥（inl 支？否，inr 支）合成。          *)
(* ================================================================ *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* 0 ≤ opp 0：eq 对称后升 le *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* opp 0 ≤ opp (log Z)：反变 + 主交付 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* 提取探针（Warning 消音：透明度旁路访问清单提示，与 UpGRPO 同法） *)
Set Warnings "-extraction-opaque-accessed".
