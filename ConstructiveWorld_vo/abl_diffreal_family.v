(* ============================================================ *)
(* abl_diffreal_family.v —— 抽象可微层 Real 脸实例族（opp/plus/affine/power_nat 四型对接） *)
(*                                                                          *)
(* 【件名】abl_diffreal_family.v（甲形态·新独立件·零级联：不改宿主、          *)
(*   零 Require 面变化、零注册面级联；照 AQ 件 abl_sumd_strict 同款先例）。   *)
(*  使命: AI 桥接件单 ①-A（AI 脸归一桥 §③件①-A）：  *)
(*   RealDifferentiable 记录（S08:3247 实拍，f : forall x:Real,              *)
(*   0<x -> Real、rdf_correct 逐 eps Bishop 形）的四缺型补全——               *)
(*   opp／plus／affine／power_nat，抽象可微层（S06 DifferentiableLemmas）     *)
(*   判例的 Real 脸实例族对接，件16 真空缺②的谓词面闭合位。                   *)
(*   首件策略（主会话令）：opp+plus 先闭合；affine/power_nat 按 AI 配方        *)
(*   「组装式」续闭合（与 AI 陈述草案的 diff 见 attn 交付报告）。              *)
(*  依赖: 全在册：S02_CauchyComplete（Real 载体/环件/real_eq 会计）；         *)
(*   S03_QExp（real_abs_opp:6550／real_inv_pos_pos）；                       *)
(*   S07_RealSetoidExpLog（RealSetoid 换形类/real_le_plus_compat:6679／      *)
(*   real_lt_zero_one:6967/real_mult_positive:6999/real_min:7214/            *)
(*   real_min_pos:7566/real_abs_triangle_le_eps:7414/real_opp_plus:7825）；  *)
(*   S08_RealMainlineDPO（RealDifferentiable 记录:3247/real_two_pos_local:   *)
(*   3373/real_half_plus_half:3554/real_min_lt_l:3979/real_min_lt_r／        *)
(*   real_opp_mult_r:48）；S09_EntropyReal（四判例 real_differentiable_      *)
(*   const:31/_id:87/_minus:157/_mult:2108、real_distrib_r:179/              *)
(*   real_plus_swap:133/real_r_pow:4961 载体具脸幂）。透传 Require 不导出     *)
(*   短名（AQ 坑卡①），本件自 Require Import 全链（S01–S09）。                *)
(*  构造性: 零承认语句、零经典逻辑、零未证前提位；语句面纯 Set           *)
(*   （RealDifferentiable : Set，S08:3247 实拍；real_le/real_lt 均 Or 形     *)
(*   Set 值谓词）。rdf 斜率逐型直构：opp 型 df 取 real_opp (rdf f)；plus 型   *)
(*   取 df+dg（real_min 分 delta＋half/quarter 逐 eps 预算，S09 minus 判例   *)
(*   同配方）；affine/power_nat 为六在役判例的组装件（exact 定义性转换闭合，  *)
(*   非单跳转发：类型族闭合由组装面承担，与 S09:4576 组装先例同档）。         *)
(*   AI 存疑表②（power_nat 的 Z.of_nat→Q 系数换算轨）按 fail-loud 禁硬供：   *)
(*   本件斜率不手写 n·x^(n-1) 显式系数，改走 mult(id,IH) 组装——存疑字段        *)
(*   整体绕开，未硬供任何未实拍引理（换形会计见 attn 交付报告）。              *)
(*   语句名 real_differentiable_opp/_plus/_affine/_power_nat（AI 陈述草案    *)
(*   逐字）：全库 grep（统一缓存根 *.v）0 命中（实拍防撞）；辅助件    *)
(*   前缀 drf_：全库 grep 0 命中（实拍防撞）。                       *)
(*  编译配方: 池内 rocq c 直编（绿判 EXIT=0｜无 Error｜魔数 436f712100015ff4）│ *)
(*   尾 Print Assumptions 四件全 Closed。                                    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
From Stdlib Require Import QArith.QArith Lists.List Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
Import PropositionConvergenceCore.

(* ============================================================ *)
(* 辅助件 1（drf_ 前缀）：opp 型增量恒等                                        *)
(*   −Fh − (−Fx + (−df)·h) == −(Fh − (Fx + df·h))                              *)
(*   （两侧各自化到规范形 −Fh + (Fx + df·h)；opp_plus/opp_opp/opp_mult_r 换形） *)
(* ============================================================ *)
Lemma drf_opp_incr_eq : forall (Fh Fx df h : Real),
  real_eq (real_plus (real_opp Fh)
                     (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h))))
          (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))).
Proof.
  intros Fh Fx df h.
  apply (real_eq_trans
           (real_plus (real_opp Fh)
                      (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h))))
           (real_plus (real_opp Fh) (real_plus Fx (real_mult df h)))
           (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))))).
  - (* 左侧 == 规范形：opp(−Fx + −df·h) == Fx + df·h *)
    apply (RealSetoid.real_eq_plus_compat (real_opp Fh)
             (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h)))
             (real_opp Fh) (real_plus Fx (real_mult df h))).
    + apply real_eq_refl.
    + apply (real_eq_trans
               (real_opp (real_plus (real_opp Fx) (real_mult (real_opp df) h)))
               (real_plus (real_opp (real_opp Fx)) (real_opp (real_mult (real_opp df) h)))
               (real_plus Fx (real_mult df h))).
      * apply (real_opp_plus (real_opp Fx) (real_mult (real_opp df) h)).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_opp (real_opp Fx)) (real_opp (real_mult (real_opp df) h))
                 Fx (real_mult df h)).
        -- apply (real_opp_opp Fx).
        -- apply (real_eq_trans
                    (real_opp (real_mult (real_opp df) h))
                    (real_opp (real_opp (real_mult df h)))
                    (real_mult df h)).
           ++ apply (RealSetoid.real_eq_opp_compat
                       (real_mult (real_opp df) h) (real_opp (real_mult df h))).
              ** apply real_eq_sym.
                 apply (real_opp_mult_r df h).
           ++ apply (real_opp_opp (real_mult df h)).
  - (* 规范形 == 右侧：规范形先拆 opp（opp_plus）再合拢（opp_opp） *)
    apply (real_eq_trans
             (real_plus (real_opp Fh) (real_plus Fx (real_mult df h)))
             (real_plus (real_opp Fh) (real_opp (real_opp (real_plus Fx (real_mult df h)))))
             (real_opp (real_plus Fh (real_opp (real_plus Fx (real_mult df h)))))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_opp Fh) (real_plus Fx (real_mult df h))
               (real_opp Fh) (real_opp (real_opp (real_plus Fx (real_mult df h))))).
      * apply real_eq_refl.
      * apply real_eq_sym.
        apply (real_opp_opp (real_plus Fx (real_mult df h))).
    + (* M == RHS：real_opp_plus 反向（RHS == opp Fh + opp(opp X) 即 M 本形） *)
      apply real_eq_sym.
      apply (real_opp_plus Fh (real_opp (real_plus Fx (real_mult df h)))).
Qed.

(* ============================================================ *)
(* 辅助件 2（drf_ 前缀）：plus 型增量恒等                                       *)
(*   (Fh+Gh) − ((Fx+Gx) + (df+dg)·h) == (Fh−(Fx+df·h)) + (Gh−(Gx+dg·h))        *)
(*   （distrib_r 换形 → real_plus_swap 重排 → opp_plus 拆开 → swap 合拢）       *)
(* ============================================================ *)
Lemma drf_plus_incr_eq : forall (Fh Gh Fx Gx df dg h : Real),
  real_eq (real_plus (real_plus Fh Gh)
                     (real_opp (real_plus (real_plus Fx Gx)
                                          (real_mult (real_plus df dg) h))))
          (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))
                     (real_plus Gh (real_opp (real_plus Gx (real_mult dg h))))).
Proof.
  intros Fh Gh Fx Gx df dg h.
  (* 链：D0 →(distrib_r 换形) M0 →(swap 重排) M0' →(opp_plus 拆开) M1 →(swap 合拢) T *)
  apply (real_eq_trans
           (real_plus (real_plus Fh Gh)
                      (real_opp (real_plus (real_plus Fx Gx)
                                           (real_mult (real_plus df dg) h))))
           (real_plus (real_plus Fh Gh)
                      (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                 (real_opp (real_plus Gx (real_mult dg h)))))
           (real_plus (real_plus Fh (real_opp (real_plus Fx (real_mult df h))))
                      (real_plus Gh (real_opp (real_plus Gx (real_mult dg h)))))).
  - (* D0 == M1：经 M0、M0' 两中间形 *)
    apply (real_eq_trans
             (real_plus (real_plus Fh Gh)
                        (real_opp (real_plus (real_plus Fx Gx)
                                             (real_mult (real_plus df dg) h))))
             (real_plus (real_plus Fh Gh)
                        (real_opp (real_plus (real_plus Fx Gx)
                                             (real_plus (real_mult df h) (real_mult dg h)))))
             (real_plus (real_plus Fh Gh)
                        (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                   (real_opp (real_plus Gx (real_mult dg h)))))).
    + (* D0 == M0：(df+dg)·h == df·h + dg·h（distrib_r 反向换形，opp 内） *)
      apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
               (real_opp (real_plus (real_plus Fx Gx)
                                    (real_mult (real_plus df dg) h)))
               (real_plus Fh Gh)
               (real_opp (real_plus (real_plus Fx Gx)
                                    (real_plus (real_mult df h) (real_mult dg h))))).
      * apply real_eq_refl.
      * apply (RealSetoid.real_eq_opp_compat
                 (real_plus (real_plus Fx Gx) (real_mult (real_plus df dg) h))
                 (real_plus (real_plus Fx Gx)
                            (real_plus (real_mult df h) (real_mult dg h)))).
        apply (RealSetoid.real_eq_plus_compat (real_plus Fx Gx)
                 (real_mult (real_plus df dg) h)
                 (real_plus Fx Gx)
                 (real_plus (real_mult df h) (real_mult dg h))).
        -- apply real_eq_refl.
        -- apply real_eq_sym.
           apply (real_distrib_r df dg h).
    + (* M0 == M1：opp 内 swap 重排 → opp_plus 拆开 *)
      apply (real_eq_trans
               (real_plus (real_plus Fh Gh)
                          (real_opp (real_plus (real_plus Fx Gx)
                                               (real_plus (real_mult df h) (real_mult dg h)))))
               (real_plus (real_plus Fh Gh)
                          (real_opp (real_plus (real_plus Fx (real_mult df h))
                                               (real_plus Gx (real_mult dg h)))))
               (real_plus (real_plus Fh Gh)
                          (real_plus (real_opp (real_plus Fx (real_mult df h)))
                                     (real_opp (real_plus Gx (real_mult dg h)))))).
      * apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx Gx)
                                      (real_plus (real_mult df h) (real_mult dg h))))
                 (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx (real_mult df h))
                                      (real_plus Gx (real_mult dg h))))).
        -- apply real_eq_refl.
        -- apply (RealSetoid.real_eq_opp_compat
                    (real_plus (real_plus Fx Gx)
                               (real_plus (real_mult df h) (real_mult dg h)))
                    (real_plus (real_plus Fx (real_mult df h))
                               (real_plus Gx (real_mult dg h)))).
           apply (real_plus_swap Fx Gx (real_mult df h) (real_mult dg h)).
      * apply (RealSetoid.real_eq_plus_compat (real_plus Fh Gh)
                 (real_opp (real_plus (real_plus Fx (real_mult df h))
                                      (real_plus Gx (real_mult dg h))))
                 (real_plus Fh Gh)
                 (real_plus (real_opp (real_plus Fx (real_mult df h)))
                            (real_opp (real_plus Gx (real_mult dg h))))).
        -- apply real_eq_refl.
        -- apply (real_opp_plus (real_plus Fx (real_mult df h))
                                (real_plus Gx (real_mult dg h))).
  - (* M1 == T：外侧 real_plus_swap 合拢 *)
    apply (real_plus_swap Fh Gh (real_opp (real_plus Fx (real_mult df h)))
                             (real_opp (real_plus Gx (real_mult dg h)))).
Qed.

(* ============================================================ *)
(* 主件 1：opp 型（AI 配方开工序首件：斜率 df := −rdf f，eps 预算原额直通）      *)
(* ============================================================ *)
Lemma real_differentiable_opp : forall (f : forall x : Real, real_lt real_zero x -> Real)
  (Hf : RealDifferentiable f),
  RealDifferentiable (fun x Hx => real_opp (f x Hx)).
Proof.
  intros f Hf.
  exists (fun x Hx => real_opp (rdf f Hf x Hx)).
  intros x Hx eps Heps.
  destruct (rdf_correct f Hf x Hx eps Heps) as [delta_f [Hdf Hf_corr]].
  exists delta_f.
  split.
  - exact Hdf.
  - intros h Hh Hxh eps' Heps'.
    apply (real_le_trans
             (real_abs (real_plus (real_opp (f (real_plus x h) Hxh))
                                  (real_opp (real_plus (real_opp (f x Hx))
                                                       (real_mult (real_opp (rdf f Hf x Hx)) h)))))
             (real_abs (real_plus (f (real_plus x h) Hxh)
                                  (real_opp (real_plus (f x Hx)
                                                       (real_mult (rdf f Hf x Hx) h)))))
             (real_plus (real_mult eps (real_abs h)) eps')).
    + (* |E| ≤ |A|：E == −A（drf_opp_incr_eq）且 |−A| == |A|（real_abs_opp，S03:6550） *)
      apply RealSetoid.real_eq_le.
      apply (real_eq_trans
               (real_abs (real_plus (real_opp (f (real_plus x h) Hxh))
                                    (real_opp (real_plus (real_opp (f x Hx))
                                                         (real_mult (real_opp (rdf f Hf x Hx)) h)))))
               (real_abs (real_opp (real_plus (f (real_plus x h) Hxh)
                                              (real_opp (real_plus (f x Hx)
                                                                   (real_mult (rdf f Hf x Hx) h))))))
               (real_abs (real_plus (f (real_plus x h) Hxh)
                                    (real_opp (real_plus (f x Hx)
                                                         (real_mult (rdf f Hf x Hx) h)))))).
      * apply (real_abs_eq_compat
                 (real_plus (real_opp (f (real_plus x h) Hxh))
                            (real_opp (real_plus (real_opp (f x Hx))
                                                 (real_mult (real_opp (rdf f Hf x Hx)) h))))
                 (real_opp (real_plus (f (real_plus x h) Hxh)
                                      (real_opp (real_plus (f x Hx)
                                                           (real_mult (rdf f Hf x Hx) h)))))).
        apply drf_opp_incr_eq.
      * apply (real_abs_opp (real_plus (f (real_plus x h) Hxh)
                                       (real_opp (real_plus (f x Hx)
                                                            (real_mult (rdf f Hf x Hx) h))))).
    + (* |A| ≤ eps|h| + eps'：rdf_correct 原额直通（eps 预算零分割） *)
      exact (Hf_corr h Hh Hxh eps' Heps').
Qed.

(* ============================================================ *)
(* 主件 2：plus 型（斜率 df+dg；delta := min δf δg；eps 预算 half/quarter 分割， *)
(*          S09 real_differentiable_minus 判例同配方降档——D == A+B 恒等更简：    *)
(*          minus 型需 opp 合拢穿线，plus 型纯 swap 重排）                       *)
(* ============================================================ *)
Lemma real_differentiable_plus : forall (f g : forall x : Real, real_lt real_zero x -> Real)
  (Hf : RealDifferentiable f) (Hg : RealDifferentiable g),
  RealDifferentiable (fun x Hx => real_plus (f x Hx) (g x Hx)).
Proof.
  intros f g Hf Hg.
  exists (fun (x : Real) (Hx : real_lt real_zero x) =>
            real_plus (rdf f Hf x Hx) (rdf g Hg x Hx)).
  intros x Hx eps Heps.
  set (half := real_inv_pos (real_plus real_one real_one) real_two_pos_local).
  set (quarter := real_mult half half).
  set (eps_half := real_mult half eps).
  assert (Hhalf : real_lt real_zero half).
  { unfold half.
    apply (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local). }
  assert (Hquarter : real_lt real_zero quarter).
  { unfold quarter.
    apply real_mult_positive; [exact Hhalf | exact Hhalf]. }
  assert (Heps_half : real_lt real_zero eps_half).
  { unfold eps_half.
    apply real_mult_positive; [exact Hhalf | exact Heps]. }
  destruct (rdf_correct f Hf x Hx eps_half Heps_half) as [delta_f [Hdf Hf_corr]].
  destruct (rdf_correct g Hg x Hx eps_half Heps_half) as [delta_g [Hdg Hg_corr]].
  exists (real_min delta_f delta_g).
  split.
  - apply real_min_pos; [exact Hdf | exact Hdg].
  - intros h Hh Hxh eps' Heps'.
    set (epsq := real_mult quarter eps').
    set (eps_tri := real_mult half eps').
    assert (Hepsq : real_lt real_zero epsq).
    { unfold epsq.
      apply real_mult_positive; [exact Hquarter | exact Heps']. }
    assert (Heptr : real_lt real_zero eps_tri).
    { unfold eps_tri.
      apply real_mult_positive; [exact Hhalf | exact Heps']. }
    assert (Hhdf : real_lt (real_abs h) delta_f).
    { apply (real_min_lt_l h delta_f delta_g).
      exact Hh. }
    assert (Hhdg : real_lt (real_abs h) delta_g).
    { apply (real_min_lt_r h delta_f delta_g).
      exact Hh. }
    set (A := real_plus (f (real_plus x h) Hxh)
                        (real_opp (real_plus (f x Hx) (real_mult (rdf f Hf x Hx) h)))).
    set (B := real_plus (g (real_plus x h) Hxh)
                        (real_opp (real_plus (g x Hx) (real_mult (rdf g Hg x Hx) h)))).
    assert (HA : real_le (real_abs A) (real_plus (real_mult eps_half (real_abs h)) epsq)).
    { exact (Hf_corr h Hhdf Hxh epsq Hepsq). }
    assert (HB : real_le (real_abs B) (real_plus (real_mult eps_half (real_abs h)) epsq)).
    { exact (Hg_corr h Hhdg Hxh epsq Hepsq). }
    apply (real_le_trans
             (real_abs (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                                  (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                       (real_mult (real_plus (rdf f Hf x Hx)
                                                                             (rdf g Hg x Hx)) h)))))
             (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)
             (real_plus (real_mult eps (real_abs h)) eps')).
    + (* |D| ≤ |A|+|B|+eps_tri：|D| == |A+B|（drf_plus_incr_eq）+ eps 三角（S07:7414） *)
      apply (real_le_trans
               (real_abs (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                                    (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                         (real_mult (real_plus (rdf f Hf x Hx)
                                                                               (rdf g Hg x Hx)) h)))))
               (real_abs (real_plus A B))
               (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)).
      * apply RealSetoid.real_eq_le.
        apply (real_abs_eq_compat
                 (real_plus (real_plus (f (real_plus x h) Hxh) (g (real_plus x h) Hxh))
                            (real_opp (real_plus (real_plus (f x Hx) (g x Hx))
                                                 (real_mult (real_plus (rdf f Hf x Hx)
                                                                       (rdf g Hg x Hx)) h))))
                 (real_plus A B)).
        unfold A, B.
        apply drf_plus_incr_eq.
      * apply (real_abs_triangle_le_eps A B eps_tri).
        exact Heptr.
    + (* |A|+|B|+eps_tri ≤ eps|h| + eps'：先经 M2 中间项（minus 判例逐字同链） *)
      apply (real_le_trans
               (real_plus (real_plus (real_abs A) (real_abs B)) eps_tri)
               (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                     (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)
               (real_plus (real_mult eps (real_abs h)) eps')).
      * (* |A|+|B|+eps_tri ≤ M2：plus_compat（HA + HB）+ eps_tri 自反 *)
        apply (real_le_plus_compat (real_plus (real_abs A) (real_abs B))
                                     (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                                (real_plus (real_mult eps_half (real_abs h)) epsq))
                                     eps_tri eps_tri).
        -- apply (real_le_plus_compat (real_abs A)
                                        (real_plus (real_mult eps_half (real_abs h)) epsq)
                                        (real_abs B)
                                        (real_plus (real_mult eps_half (real_abs h)) epsq)).
           ++ exact HA.
           ++ exact HB.
        -- apply real_le_refl.
      * (* M2 == eps|h| + eps'：代数链（重排 + half 合并，minus 判例同配方） *)
        apply RealSetoid.real_eq_le.
        apply (real_eq_trans
                 (real_plus (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                       (real_plus (real_mult eps_half (real_abs h)) epsq)) eps_tri)
                 (real_plus (real_mult eps (real_abs h)) (real_plus (real_plus epsq epsq) eps_tri))
                 (real_plus (real_mult eps (real_abs h)) eps')).
        -- (* 重排 + A+C 合并：((A+B)+(C+D))+E == eps|h| + ((B+D)+E) *)
          apply (real_eq_trans _
                   (real_plus (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq)) eps_tri)
                   _).
          ++ (* ((A+B)+(C+D))+E == (eps|h|+(B+D))+E：swap + A+C 合并 *)
            apply (RealSetoid.real_eq_plus_compat
                     (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                (real_plus (real_mult eps_half (real_abs h)) epsq))
                     eps_tri
                     (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))
                     eps_tri).
            ** (* (A+B)+(C+D) == eps|h|+(B+D)：swap + A+C == eps|h| *)
              apply (real_eq_trans
                       (real_plus (real_plus (real_mult eps_half (real_abs h)) epsq)
                                  (real_plus (real_mult eps_half (real_abs h)) epsq))
                       (real_plus (real_plus (real_mult eps_half (real_abs h))
                                             (real_mult eps_half (real_abs h)))
                                  (real_plus epsq epsq))
                       (real_plus (real_mult eps (real_abs h)) (real_plus epsq epsq))).
              --- apply (real_plus_swap (real_mult eps_half (real_abs h)) epsq
                                          (real_mult eps_half (real_abs h)) epsq).
              --- apply (RealSetoid.real_eq_plus_compat
                           (real_plus (real_mult eps_half (real_abs h))
                                      (real_mult eps_half (real_abs h)))
                           (real_plus epsq epsq)
                           (real_mult eps (real_abs h))
                           (real_plus epsq epsq)).
              *** (* eps_half|h| + eps_half|h| == eps|h|：mult_assoc 换形 + real_half_plus_half *)
                apply (real_eq_trans
                         (real_plus (real_mult eps_half (real_abs h))
                                    (real_mult eps_half (real_abs h)))
                         (real_plus (real_mult half (real_mult eps (real_abs h)))
                                    (real_mult half (real_mult eps (real_abs h))))
                         (real_mult eps (real_abs h))).
                +++ apply (RealSetoid.real_eq_plus_compat
                             (real_mult eps_half (real_abs h)) (real_mult eps_half (real_abs h))
                             (real_mult half (real_mult eps (real_abs h)))
                             (real_mult half (real_mult eps (real_abs h)))).
                **** unfold eps_half.
                apply real_eq_sym.
                apply (real_mult_assoc half eps (real_abs h)).
                **** unfold eps_half.
                apply real_eq_sym.
                apply (real_mult_assoc half eps (real_abs h)).
                +++ apply (real_half_plus_half (real_mult eps (real_abs h))).
              *** apply real_eq_refl.
            ** apply real_eq_refl.
          ++ apply real_eq_sym.
            apply (real_plus_assoc (real_mult eps (real_abs h)) (real_plus epsq epsq) eps_tri).
        -- (* eps|h| + ((epsq+epsq)+eps_tri) == eps|h| + eps'：B+D+E == eps' *)
          apply (RealSetoid.real_eq_plus_compat (real_mult eps (real_abs h))
                   (real_plus (real_plus epsq epsq) eps_tri)
                   (real_mult eps (real_abs h))
                   eps').
          ++ apply real_eq_refl.
          ++ (* (epsq+epsq)+eps_tri == eps'：quarter+quarter == half、half+half == 1 *)
            apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)
                                   (real_plus (real_mult half eps') (real_mult half eps'))
                                   eps').
            ** (* (epsq+epsq)+eps_tri == half·eps' + half·eps'：quarter 合并 *)
              apply (real_eq_trans (real_plus (real_plus epsq epsq) eps_tri)
                                     (real_plus (real_mult (real_plus quarter quarter) eps')
                                                (real_mult half eps'))
                                     (real_plus (real_mult half eps') (real_mult half eps'))).
              --- unfold epsq, eps_tri.
                apply (RealSetoid.real_eq_plus_compat
                         (real_plus (real_mult quarter eps') (real_mult quarter eps'))
                         (real_mult half eps')
                         (real_mult (real_plus quarter quarter) eps')
                         (real_mult half eps')).
                +++ apply (real_distrib_r quarter quarter eps').
                +++ apply real_eq_refl.
              --- apply (RealSetoid.real_eq_plus_compat
                           (real_mult (real_plus quarter quarter) eps') (real_mult half eps')
                           (real_mult half eps') (real_mult half eps')).
                +++ apply (RealSetoid.real_eq_mult_compat (real_plus quarter quarter) eps' half eps'
                             (real_half_plus_half half) (real_eq_refl _)).
                +++ apply real_eq_refl.
            ** apply (real_half_plus_half eps').
Qed.

(* ============================================================ *)
(* 主件 3：affine 型（组装式：affine x = a·x + b 由 const/mult/id/plus 四判例   *)
(*          组装；exact 以 beta 定义性转换闭合——比 AI 草案直证 rdf:=a 更省，     *)
(*          且 real_differentiable_plus 即本件主件 2 的首个使用位）              *)
(* ============================================================ *)
Lemma real_differentiable_affine : forall (a b : Real),
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) =>
                        real_plus (real_mult a x) b).
Proof.
  intros a b.
  exact (real_differentiable_plus
           (fun (x : Real) (_ : real_lt real_zero x) => real_mult a x)
           (fun (x : Real) (_ : real_lt real_zero x) => b)
           (real_differentiable_mult
              (fun (x : Real) (_ : real_lt real_zero x) => a)
              (fun (x : Real) (_ : real_lt real_zero x) => x)
              (real_differentiable_const a) real_differentiable_id)
           (real_differentiable_const b)).
Qed.

(* ============================================================ *)
(* 主件 4：power_nat 型（组装式归纳：real_r_pow 0 ≡ 1（常数件）、                *)
(*          real_r_pow (S m) ≡ x·real_r_pow m（mult(id, IH)）；斜率由 mult 判例  *)
(*          自带——AI 存疑表② 的 Z.of_nat→Q 显式系数轨整体绕开，零硬供）          *)
(* ============================================================ *)
Lemma real_differentiable_power_nat : forall (n : nat),
  RealDifferentiable (fun (x : Real) (Hx : real_lt real_zero x) => real_r_pow x n).
Proof.
  intros n.
  induction n as [| m IHm].
  - (* n = 0：real_r_pow x 0 ≡ real_one（S09:4961 定义面 iota），常数判例直给 *)
    exact (real_differentiable_const real_one).
  - (* n = S m：real_r_pow x (S m) ≡ real_mult x (real_r_pow x m)（iota）， *)
    (* mult(恒等件, IHm) 组装（beta + fix iota 定义性转换闭合） *)
    exact (real_differentiable_mult
             (fun (x : Real) (_ : real_lt real_zero x) => x)
             (fun (x : Real) (_ : real_lt real_zero x) => real_r_pow x m)
             real_differentiable_id IHm).
Qed.

(* ============ 取证段 ============ *)
Print Assumptions real_differentiable_opp.
Print Assumptions real_differentiable_plus.
Print Assumptions real_differentiable_affine.
Print Assumptions real_differentiable_power_nat.
