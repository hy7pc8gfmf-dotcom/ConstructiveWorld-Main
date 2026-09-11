(* ============================================================ *)
(* UpReqFEPCanon.v —— 席X2：定理 4.1 Real 复刻「正典化对接」件        *)
(*   2026-09-11（后台独立席位，CoreN 5，预算 60 分钟单席闭合）        *)
(* ------------------------------------------------------------------ *)
(* 【使命】把 S08_RealMainlineDPO Section RealRLHFMain 内的诚实接口槽  *)
(*   real_kl_decomp_full（L2516；论文附录 B L1379 据此标「完整分解为  *)
(*   接口」）与已证件 UpReqRealFEP.rfep_real_kl_decomp_full（L805）   *)
(*   正典化对接：同语句、前提形态转换——下游不改 S08 分片，即可引用    *)
(*   到已证的完整分解 F[p] ≡ F[p_b] + D·Σ kl_term（real_eq 载体）。   *)
(*   席N1 判词承按：LogLinD 头注所判「现成件缺失」由本件补齐（正典化）。 *)
(* ------------------------------------------------------------------ *)
(* 【对接裁决（E403③：节泛化跨节消费全参显式）】探针实测（_x2_probe）  *)
(*   两语句结论面逐字同构（real_eq (F p) (F p_b + D·Σkl)，Σ 内        *)
(*   real_kl_term 具名形）；前提面两处错位，对位如下：                 *)
(*   ① rfep 版节接口多 real_sum_over_S_linear 一字段（UpReqRealFEP    *)
(*      头注已申报的诚实增量，S08 原节无此字段）→ 本件显式升参；       *)
(*   ② rfep 版残留前提 Hnormb（Σ p_b ≡ 1）→ 主件照单显式升参（同面    *)
(*      直喂）；                                                      *)
(*   ③ 分件 canon_partition 把 Hnormb 换为更原始的 partition 条件     *)
(*      Hpart（Σ exp(−e/D) ≡ Z），经 rfep_boltzmann_normalized_real   *)
(*      （L331）一步放电——即任务书「前提放电小链」的兑现形。          *)
(* ------------------------------------------------------------------ *)
(* 【诚实申报】本件为对接件（非新数学）：结论面与 S08 槽、rfep 已证件  *)
(*   逐字同构；证明 = rfep 主件部分应用直喂 + 一条归一化放电链。零新   *)
(*   环境前提；linear/Hnormb（或 Hpart）为 rfep 版自带前提的如实升参。 *)
(*   禁改红线：S08_RealMainlineDPO.v / UpReqRealFEP.v 全程只读零触碰。 *)
(* ------------------------------------------------------------------ *)
(* 【红线】Set 层零 Prop（real_eq/real_lt 全 Set 值）；全 Qed 闭合；   *)
(*   G1 禁词条目零命中（头注以中文转述，不引英文原词）；real_eq 非 Id  *)
(*   禁 rewrite，全链 real_eq_trans/RealSetoid compat（E393 纪律）。  *)
(* 编译配方：_x2_run.ps1 单一入口（E355 先例）+ cpu_guard CoreN 5      *)
(*   预审：coqc -vos（秒审）；全量：coqc -Q vo树 "" -Q 本目录 ""       *)
(*   前置 .vo 全在 D:/ComplexAnalysis/ConstructiveWorld-Main/         *)
(*   ConstructiveWorld_vo/（vo 树编译，S08/rfep 零重编）。            *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 主件：real_kl_decomp_full_canon                                   *)
(*   S08 槽 real_kl_decomp_full 的正典化放电形：结论面与 S08 槽逐字    *)
(*   同构（real_eq (F p) (F p_b + D·Σ kl_term)）；节接口按放电后全参   *)
(*   显式升参（含 rfep 版诚实增量 linear），残留前提 Hnormb 照单升参。 *)
(*   证明 = rfep_real_kl_decomp_full 部分应用直喂（一步 exact）。     *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hnormb.
  exact (rfep_real_kl_decomp_full
           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
           p Hp Hnormp Hnormb).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：real_kl_decomp_full_canon_partition（前提放电小链版）        *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart                  *)
(*   （Σ exp(−e/D) ≡ Z，物理配分函数账目），经 rfep_boltzmann_        *)
(*   normalized_real 一步放电补齐 Hnormb，再直喂 rfep 主件。           *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon_partition :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (fun s : S => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
          Z_align_r ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
         p Hp Hnormp Hpart.
  apply (rfep_real_kl_decomp_full
           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add
           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos
           p Hp Hnormp).
  exact (rfep_boltzmann_normalized_real
           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_linear
           real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart).
Qed.
