(* UpReqCf2TvGenSupply — 使命：Fin2 总变差 general 位非负消解边界检验件：
   供给半边以显式假设位承载 plain 形逐点绝对值非负字段 Habs : forall x, le zero (abs x)，
   构造性推出零归一前件强形 general 位 TV₀≥0；反向半边以归一对见证（nu ≡ half、
   mu := half±x 摆动对）由 general 位消解复原 plain 字段。两半边合成真等价：
   「general 位 TV₀≥0 消解 ⟺ plain abs_nonneg 字段供给」。 *)
(* 依赖清单：全部只 Require 不改。CW_ConstructiveWorld_219（S01-S15 聚合 Export 链）、
   UpReqAlgebra（req_le_mult_compat_r / req_two_pos / req_plus_zero_r / req_plus_opp_r /
   req_mult_one_l / req_two_mult / req_mult_plus_distr_r / req_plus_swap_mid /
   req_minus_plus_cancel_r）、UpReqSumD（sumd_list_sum_nonneg / sumd_lt_le）、UpReqDist、
   UpReqConcSoftmax（csm_sumf）、UpReqSampling、UpReqConcMixSel、UpReqConcB1、UpReqConcB2、
   AttnDoeblin、UpReqConcFin2（cf2_tv / cf2_sumf / cf2_inv_two）。
   Import 不传递，故按使用位惯例补 Import RealInterfaceEnhancedMod 与 Import ListNotations；
   导入后 le_id_l / le_id_r / mult_zero / plus_zero / distrib / abs_opp / inv_pos_correct /
   inv_pos_pos 等名一律绑定 RealInterfaceEnhancedSetoid（req 层）投影。 *)
(* 对标行：
   cf2_tv       ≜ mult cf2_inv_two (cf2_sumf (fun s => abs (req_minus (mu s) (nu s))))
   cf2_inv_two  ≜ inv_pos (plus one one) req_two_pos
   cf2_sumf f   ≜ sumd_list_sum bool f [true; false]（定义性即列表和）
   已证结论对照：cf2_tv_nonneg（点质量位 concrete 形）为本件 general 位两半边的点位特例参照；
   本件零触碰上游任何接口与语句。 *)
(* 构造性注记：零承认件。全部语句落在 Set 层（le/lt/req/abs 均 Set 族接口面），
   无 Prop 泄露位、无经典逻辑。供给向全链：逐项消解（Habs 逐点）→ 列表和保持
   （sumd_list_sum_nonneg）→ 正系数乘 le 保持（req_le_mult_compat_r）→ 换轨闭合
   （le_id_l + mult_zero）。反向全链：归一对见证 → 归一前件以 req 代数链闭合
   （req_two_mult / inv_pos_correct）→ 逐项差实例化消解
   （req_minus_plus_cancel_r：req_minus (plus a b) a ≡ b）→ abs 字段回提
   （req_abs_compat / abs_opp）→ 半倍和闭合（distrib / req_mult_plus_distr_r /
   req_mult_one_l）→ le_id_r 换轨。 *)
(* 编译配方：Rocq 9.1，-Q . "" 空根映射；
   coqc -Q . "" UpReqCf2TvGenSupply.v *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqDist.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import UpReqConcB2.
Require Import AttnDoeblin.
Require Import UpReqConcFin2.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* 件一·供给向强形：零归一前件——对任意 mu nu，plain abs_nonneg 字段
   直接消解 general 位 TV₀≥0。 *)
Lemma uc2t_habs_cf2tv_nonneg : forall (mu nu : bool -> Real),
  (forall x : Real, le zero (abs x)) -> le zero (cf2_tv mu nu).
Proof.
  intros mu nu Habs.
  apply (le_id_l zero (mult cf2_inv_two zero) (cf2_tv mu nu)
           (req_sym (mult cf2_inv_two zero) zero (mult_zero cf2_inv_two))).
  unfold cf2_tv.
  apply (req_le_mult_compat_r cf2_inv_two zero
           (cf2_sumf (fun s : bool => abs (req_minus (mu s) (nu s))))).
  - (* cf2_inv_two = (1+1)⁻¹ > 0 升非负（req 层正性件） *)
    exact (sumd_lt_le cf2_inv_two (inv_pos_pos (plus one one) req_two_pos)).
  - (* 逐项 Habs → 列表和非负；cf2_sumf 定义性即 sumd_list_sum bool _ [true; false] *)
    exact (sumd_list_sum_nonneg bool
             (fun s : bool => abs (req_minus (mu s) (nu s))) [true; false]
             (fun s : bool => Habs (req_minus (mu s) (nu s)))).
Qed.

(* 件一·规格形：带归一前件口径，强形一行推论
   （归一前件对供给向不可达命题无贡献，此处如实登记其未被使用）。 *)
Lemma uc2t_habs_cf2tv_nonneg_norm : forall (mu nu : bool -> Real),
  (forall x : Real, le zero (abs x)) ->
  req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> le zero (cf2_tv mu nu).
Proof.
  intros mu nu Habs _ _.
  exact (uc2t_habs_cf2tv_nonneg mu nu Habs).
Qed.

(* 件二·反向半边：general 位 TV₀≥0 消解（带归一前件口径）复原 plain abs_nonneg 字段。 *)
Lemma uc2t_cf2tv_nonneg_habs_rev :
  (forall (mu nu : bool -> Real),
     req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> le zero (cf2_tv mu nu)) ->
  forall x : Real, le zero (abs x).
Proof.
  intros H x.
  (* nu ≡ half 归一：half + (half + 0) = (1+1)·half = 1 *)
  assert (Hnu : req (cf2_sumf (fun _ : bool => cf2_inv_two)) one).
  { exact (req_trans (plus cf2_inv_two (plus cf2_inv_two zero))
                     (plus cf2_inv_two cf2_inv_two) one
             (req_plus_compat cf2_inv_two cf2_inv_two (plus cf2_inv_two zero) cf2_inv_two
                              (req_refl cf2_inv_two) (plus_zero cf2_inv_two))
             (req_trans (plus cf2_inv_two cf2_inv_two)
                        (mult (plus one one) cf2_inv_two) one
                        (req_sym (mult (plus one one) cf2_inv_two)
                                 (plus cf2_inv_two cf2_inv_two)
                                 (req_two_mult cf2_inv_two))
                        (inv_pos_correct (plus one one) req_two_pos))). }
  (* mu ≡ half±x 摆动对归一：(half+x) + ((half−x)+0) = (half+half) + (x+(−x))
     = (half+half) + 0 = half+half = (1+1)·half = 1 *)
  assert (Hmu : req (cf2_sumf (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x))) one).
  { exact (req_trans (plus (plus cf2_inv_two x) (plus (plus cf2_inv_two (opp x)) zero))
                     (plus (plus cf2_inv_two x) (plus cf2_inv_two (opp x)))
                     one
                     (req_plus_compat (plus cf2_inv_two x) (plus cf2_inv_two x)
                                      (plus (plus cf2_inv_two (opp x)) zero) (plus cf2_inv_two (opp x))
                                      (req_refl (plus cf2_inv_two x))
                                      (plus_zero (plus cf2_inv_two (opp x))))
                     (req_trans (plus (plus cf2_inv_two x) (plus cf2_inv_two (opp x)))
                                (plus (plus cf2_inv_two cf2_inv_two) (plus x (opp x)))
                                one
                                (req_plus_swap_mid cf2_inv_two x cf2_inv_two (opp x))
                                (req_trans (plus (plus cf2_inv_two cf2_inv_two) (plus x (opp x)))
                                           (plus (plus cf2_inv_two cf2_inv_two) zero)
                                           one
                                           (req_plus_compat (plus cf2_inv_two cf2_inv_two) (plus cf2_inv_two cf2_inv_two)
                                                            (plus x (opp x)) zero
                                                            (req_refl (plus cf2_inv_two cf2_inv_two))
                                                            (req_plus_opp_r x))
                                           (req_trans (plus (plus cf2_inv_two cf2_inv_two) zero)
                                                      (plus cf2_inv_two cf2_inv_two)
                                                      one
                                                      (req_plus_zero_r (plus cf2_inv_two cf2_inv_two))
                                                      (req_trans (plus cf2_inv_two cf2_inv_two)
                                                                 (mult (plus one one) cf2_inv_two)
                                                                 one
                                                                 (req_sym (mult (plus one one) cf2_inv_two)
                                                                          (plus cf2_inv_two cf2_inv_two)
                                                                          (req_two_mult cf2_inv_two))
                                                                 (inv_pos_correct (plus one one) req_two_pos)))))). }
  (* 逐项差：(half+x)−half = x、(half−x)−half = −x（req_minus_plus_cancel_r）；
     abs 字段回提后 −x 支经 abs_opp 同归 abs x；半倍和 half·(|x|+|x|) = |x| 闭合 *)
  assert (Htv : req (cf2_tv (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x)) (fun _ : bool => cf2_inv_two)) (abs x)).
  { exact (req_trans
             (mult cf2_inv_two
                   (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                         (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero)))
             (mult cf2_inv_two (plus (abs x) (abs x)))
             (abs x)
             (req_mult_compat cf2_inv_two cf2_inv_two
                              (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                    (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero))
                              (plus (abs x) (abs x))
                              (req_refl cf2_inv_two)
                              (req_trans (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                               (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero))
                                         (plus (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                               (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)))
                                         (plus (abs x) (abs x))
                                         (req_plus_compat (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (plus (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two)) zero)
                                                          (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                          (req_refl (abs (req_minus (plus cf2_inv_two x) cf2_inv_two)))
                                                          (plus_zero (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))))
                                         (req_plus_compat (abs (req_minus (plus cf2_inv_two x) cf2_inv_two))
                                                          (abs x)
                                                          (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                          (abs x)
                                                          (req_abs_compat (req_minus (plus cf2_inv_two x) cf2_inv_two) x
                                                                          (req_minus_plus_cancel_r cf2_inv_two x))
                                                          (req_trans (abs (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two))
                                                                     (abs (opp x)) (abs x)
                                                                     (req_abs_compat (req_minus (plus cf2_inv_two (opp x)) cf2_inv_two) (opp x)
                                                                                     (req_minus_plus_cancel_r cf2_inv_two (opp x)))
                                                                     (abs_opp x)))))
             (req_trans (mult cf2_inv_two (plus (abs x) (abs x)))
                        (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                        (abs x)
                        (distrib cf2_inv_two (abs x) (abs x))
                        (req_trans (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                                   (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                   (abs x)
                                   (req_sym (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                            (plus (mult cf2_inv_two (abs x)) (mult cf2_inv_two (abs x)))
                                            (req_mult_plus_distr_r cf2_inv_two cf2_inv_two (abs x)))
                                   (req_trans (mult (plus cf2_inv_two cf2_inv_two) (abs x))
                                              (mult one (abs x)) (abs x)
                                              (req_mult_compat (plus cf2_inv_two cf2_inv_two) one (abs x) (abs x)
                                                               (req_trans (plus cf2_inv_two cf2_inv_two)
                                                                          (mult (plus one one) cf2_inv_two) one
                                                                          (req_sym (mult (plus one one) cf2_inv_two)
                                                                                   (plus cf2_inv_two cf2_inv_two)
                                                                                   (req_two_mult cf2_inv_two))
                                                                          (inv_pos_correct (plus one one) req_two_pos))
                                                               (req_refl (abs x)))
                                              (req_mult_one_l (abs x)))))). }
  exact (le_id_r zero
           (cf2_tv (fun s : bool => if s then plus cf2_inv_two x else plus cf2_inv_two (opp x))
                   (fun _ : bool => cf2_inv_two))
           (abs x) Htv (H _ _ Hmu Hnu)).
Qed.
