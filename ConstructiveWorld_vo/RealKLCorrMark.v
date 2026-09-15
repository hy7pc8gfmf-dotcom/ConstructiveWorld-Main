(* RealKLCorrMark.v
   目的：登记 real_kl_decomp_full 两个上游假设位按字面为假的勘误结论，
   并给出补入 p_b 侧归一化前提后的修正重述件（mend）。

   主件：rkc_real_kl_decomp_full_mend——假设位A（UpRealLeB.v:218）
   语句逐字同构 + 新增前提 Hnormb : Σ p_b == 1 + ext/add/linear
   三桥显式升参，一步 exact 直取 rfep_real_kl_decomp_full
   （UpReqRealFEP.v:805 节闭全参形）。伴节 RkcSlotAMendInSitu 为
   上游 Section 接口的镜像重述，新增归一化接口
   real_boltzmann_normalized_rkc : Σ p_b == 1。

   依赖：Stdlib Extraction、CW_ConstructiveWorld_219、UpReqRealFEP。

   备注（勘误结论）：两假设位前提仅 Hp + Hnormp（对 p 的 Σp == 1），
   结论却对任意正性证书 Z_align_r 断言
   F(p) == F(p_b) + D·Σ kl_term，缺 p_b 侧归一化 Σ p_b == 1（Z 须为
   配分函数）；一般 Z 下恒等式两边相差 D·log Z·(Σ p_b − 1)，其中
   p_b(s) = inv(Z)·exp(−e(s)/D)。单点反例：S 为单点，e = 0，D = 1，
   Z = 2，p = 1（Hnormp 成立），则 Σ p_b = 1/2 ≠ 1，LHS = 0，
   RHS = (1/2)·log 2 ≠ 0。缺口在 p_b 侧归一化而非 Σp == 1：
   Hnormp/Hnormpi 是对 p 的，类型不同，不能移作修正前提；可用
   供给源为 S08 节内 real_boltzmann_normalized（:2494，声明后零
   消费）或 partition 前提消解件 rfep_boltzmann_normalized_real
   （UpReqRealFEP.v:331）。假设位B（S08_RealMainlineDPO.v:2516）
   与假设位A 同构同假（同一数学命题，仅载体内联度不同），其修正形
   即正典件 real_kl_decomp_full_canon（UpReqFEPCanon.v:48，结论面
   与 S08 位逐字同构），本文件不重复立件。正典件下游消费位
   （UpReqMinUniqueTight.v:159/341、UpReqELBOStrict.v:152、
   UpReqMinFreeEps.v:167/251）语句面已自备 Hnormb/Hpart 前提，
   换用正典件后签名不变零改动。上游消费位、修正接线与增量桥的
   位址细节见下方各注释块。

   红线自检：本文件为对接件（非新数学），零新公理、零未闭合证明、
   零猜想、零中止；语句面全 Set 值（real_eq/real_lt，零 Prop 面）；
   证明体一步 exact 消费在盘全 Qed 件；文末提取探针 + 假设闭包检查。
   ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 修正主件：rkc_real_kl_decomp_full_mend                           *)
(*   假设位A（UpRealLeB.v:218）语句逐字同构 + Hnormb 前提。          *)
(*   前提面 = 位A 原前提 Hp/Hnormp + 新增 Hnormb : Σ p_b == 1        *)
(*   + ext/add/linear 三桥（rfep 节接口诚实增量，显式升参）。        *)
(*   证 = rfep_real_kl_decomp_full（UpReqRealFEP.v:805）节闭全参形   *)
(*   部分应用后一步 exact 直接提供。                                *)
(* ---------------------------------------------------------- *)

Theorem rkc_real_kl_decomp_full_mend :
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
                   (fun s : S =>
                    real_kl_term (p s)
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
(* 假设位A 修正连锁镜像节：RkcSlotAMendInSitu                        *)
(*   逐位镜像 UpRealLeB Section RealRLHFLeB 的节接口面（:198-204     *)
(*   七参 + 两诚实位；本镜像只收修正相关面，gibbs 位与 decomp 原位    *)
(*   不入——回灌时原位由本镜像所证形态替换）。新增第 8 条接口：       *)
(*   real_boltzmann_normalized_rkc : Σ p_b == 1（即 S08:2494 同名    *)
(*   假设位的 UpRealLeB 侧对应位，对应上游审计建议「增 1 条归一化    *)
(*   Variable」的兑现形）。节内重申件 = 假设位A 修正后的语句原位形态。 *)
(* ---------------------------------------------------------- *)

Section RkcSlotAMendInSitu.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_base_loss : S -> Real.
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable Z_align_r : Real.
Variable Z_align_r_pos : real_lt real_zero Z_align_r.
(* 修正新增接口：p_b 侧归一化（Σ p_b == 1）——假设位A 原节所缺的一条 *)
Variable real_boltzmann_normalized_rkc :
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one.
(* 三桥：rfep 节接口诚实增量（假设位A 原节无此三字段，为消解所需的   *)
(* 最小增量） *)
Variable real_sum_over_S_ext : forall f g : S -> Real,
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall f g : S -> Real,
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* 假设位A 语句原位修正形：结论面与 UpRealLeB.v:218-231 逐字同构，     *)
(* 消费位 :247-248 的 exact 由此件 + real_boltzmann_normalized_rkc    *)
(* 承接（回灌时 :248 调用点 +1 实参，即本节接口位的传参方式）。        *)
Theorem rkc_slotA_kl_decomp_full_mend :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (real_sum_over_S p) real_one),
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S =>
                    real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros p Hp Hnormp.
  exact (rkc_real_kl_decomp_full_mend
           S real_sum_over_S
           real_sum_over_S_ext real_sum_over_S_add real_sum_over_S_linear
           real_base_loss D D_pos Z_align_r Z_align_r_pos
           p Hp Hnormp real_boltzmann_normalized_rkc).
Qed.

End RkcSlotAMendInSitu.

(* ============================================================ *)
(* 探针审计：提取 Obj.magic 计数应为 0 + 语句假设闭包               *)
(* ============================================================ *)

Extraction "rkc_G3.ml" rkc_real_kl_decomp_full_mend rkc_slotA_kl_decomp_full_mend.

Print Assumptions rkc_real_kl_decomp_full_mend.
Print Assumptions rkc_slotA_kl_decomp_full_mend.
