(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   attn_log_partition_bound_B（原 L505，3 句玩具证）                    *)
(*   attn_log_partition_bound_full（原 L388，2 句玩具证）                 *)
(* ============================================================ *)

(* ============================================================ *)
(* AttnLogSumExpBound.v — 施工席位 C12：注意力聚合 log-partition 上界  *)
(* （A2 组合榜组 6；S 链薄壳内 A×B 装配，零新公理）                   *)
(* ============================================================ *)
(* 目标定理（A2 席方案）：注意力聚合的 log-partition 型上界。          *)
(*   注意力聚合 Agg = Σ_s (e^s/Z)·f(s)（权重件 S12:13278              *)
(*   sf_attention_weights / sf_softmax 的点wise函数面）；配分          *)
(*   Z = sf_partition ss = Σ e^s（S12:11939）。                       *)
(*   主件：值域 [0,B] 正值场下                                        *)
(*     log(Z·Agg) ≤ log Z + log B           （log-partition 型上界）   *)
(*   即倾斜配分恒等 T = Σ e^s·f(s) = Z·Agg 的 log 放大界。             *)
(*                                                                   *)
(* A×B 装配（语句面均 grep 实测）：                                    *)
(*   · A 件 1 S12:13286 sf_attention_weights_sum_one（Σ w == 1，       *)
(*     map 面）→ attn_weights_sum_one_pt 桥到点wise函数面；            *)
(*   · A 件 2 S12:12017 sf_softmax_le_one（单权重 ≤ 1）→               *)
(*     attn_logit_le_log_partition（s ≤ log Z，配分控制逐 logit）；    *)
(*   · B 件 G08:192 gibbsd_p_mult_ratio（p·(q/p) == q）→              *)
(*     attn_tilted_eq（倾斜配分恒等 T == Z·Agg，逐项 ext 装配）        *)
(*     + attn_logit_le_log_partition 内 e^s == Z·w 第二消费位；        *)
(*   · 支撑 ≥2：attn_aggregate_le_bound（权重归一传递件，A1 消费）     *)
(*     + attn_wsum_le_scale（有界质量件：Σ w·f ≤ B·Σw，list 面）       *)
(*     + attn_sum_nonneg / attn_elem_le_sum（最大值控制件 max ≤ sum   *)
(*     型，list 面，InT 逐点受限版）+ attn_aggregate_pos /            *)
(*     attn_tilted_pos（聚合正性 = 逐点控制 + lt-le 传递）。           *)
(*                                                                   *)
(* log 墙策略（A4/E-STAGING-C1：log 反单调方向翻车前科规避）：          *)
(*   全链只走 log 单调升向 real_log_le_mono（G01:536，Or 编码逐支     *)
(*   放电，plain real_le）+ real_log_mult eq 重排（S07:7845）；        *)
(*   零反单调、零 plain 形硬攻；另出 real_le_b Bishop 形（            *)
(*   UpRealLeB:78 real_le_to_le_b 单向桥）作 eps/B 出口。             *)
(*                                                                   *)
(* 红线自审：①语句面全 Set（real_le/real_le_b/real_lt/real_eq；       *)
(*   real_le 为 Or 编码 Set 值和，前提位 Not/InT/real_lt 仅显式参）；  *)
(*   ②公理面零假设（无公理/自认/参数声明/猜想/中止/半途认输，零经典逻辑）*)
(*   （依赖全为库内闭合件）；③非平凡（B 件分式恒等逐项装配 + 权重归一  *)
(*   传导 + 有界质量换算 + InT 逐点 max≤sum + 正性 elt 支配链 +       *)
(*   正缩放保序 + log 单调/乘法重排 + A2 件 logit 支配）；             *)
(*   ④文末 Print Assumptions 审计口 5 处。                           *)
(* 已知坑规避：nat 加法不用（无 nat 面）；Datatypes.S 不触碰；apply    *)
(*   全显参；Qeq 不出现；类投影不出现。                                *)
(* ============================================================ *)

From Stdlib Require Import List.
Import ListNotations.

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import G01_CoreMicro.
Require Import G08_Gibbs.
Require Import S12_B5RecycleSF.
Require Import UpRealLeB.

(* ============================================================ *)
(* 0. 注意力聚合定义面（attn_aggregate：S12 sf_attention_weights       *)
(*    的点wise函数形；Wp 为配分正性证书）。                            *)
(* ============================================================ *)

(* 注意力权重（≡ sf_softmax ss Wp s；sf_attention_weights 的逐点形）。 *)
Definition attn_weight (ss : list Real)
  (Wp : real_lt real_zero (sf_partition ss)) (s : Real) : Real :=
  real_mult (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp).

(* 注意力聚合：值场 f 的权重平均 Σ_s w(s)·f(s)。 *)
Definition attn_aggregate (ss : list Real) (f : Real -> Real)
  (Wp : real_lt real_zero (sf_partition ss)) : Real :=
  real_list_sum Real (fun s => real_mult (attn_weight ss Wp s) (f s)) ss.

(* 倾斜配分（log-partition 分子面）：T = Σ_s e^s·f(s)。 *)
Definition attn_tilted (ss : list Real) (f : Real -> Real) : Real :=
  real_list_sum Real (fun s => real_mult (sf_exp_score s) (f s)) ss.

(* ============================================================ *)
(* 1. A 件 1 桥：权重和 == 1（map 面 → 点wise函数面）。                *)
(* ============================================================ *)

Lemma attn_weights_sum_one_pt :
  forall ss : list Real,
    Not (Id ss nil) ->
    forall Wp : real_lt real_zero (sf_partition ss),
      real_eq (real_list_sum Real (attn_weight ss Wp) ss) real_one.
Proof.
  intros ss Hnil Wp.
  apply (real_eq_trans
           (real_list_sum Real (attn_weight ss Wp) ss)
           (real_list_sum Real id (map (attn_weight ss Wp) ss))
           real_one).
  - apply real_eq_sym.
    exact (sf_rsum_map_id Real (attn_weight ss Wp) ss).
  - exact (sf_attention_weights_sum_one ss Hnil Wp).
Qed.

(* ============================================================ *)
(* 2. 支撑（最大值控制件，list 面）：有界质量件 Σ w·f ≤ B·Σw           *)
(*    （w 恒正、f 逐点 ≤ B；逐项正缩放保序 + 线性提取）。               *)
(* ============================================================ *)

Lemma attn_wsum_le_scale :
  forall (ss : list Real) (w f : Real -> Real) (B : Real),
    (forall s : Real, real_lt real_zero (w s)) ->
    (forall s : Real, real_le (f s) B) ->
    real_le (real_list_sum Real (fun s => real_mult (w s) (f s)) ss)
            (real_mult B (real_list_sum Real w ss)).
Proof.
  intros ss w f B Hw Hf.
  apply (real_le_trans
           _ (real_list_sum Real (fun s => real_mult (w s) B) ss)).
  - apply (real_list_sum_le Real).
    intro s.
    apply (real_le_trans
             (real_mult (w s) (f s))
             (real_mult (f s) (w s))
             (real_mult (w s) B)).
    + apply real_eq_le_bridge. apply real_mult_comm.
    + apply (real_le_trans
               (real_mult (f s) (w s))
               (real_mult B (w s))
               (real_mult (w s) B)).
      * exact (real_le_mult_compat (f s) B (w s) (Hw s) (Hf s)).
      * apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm.
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             (real_list_sum Real (fun s => real_mult (w s) B) ss)
             (real_list_sum Real (fun s => real_mult B (w s)) ss)
             (real_mult B (real_list_sum Real w ss))).
    + apply (real_list_sum_ext Real).
      intro s. apply real_mult_comm.
    + exact (real_list_sum_linear Real B w ss).
Qed.

(* ============================================================ *)
(* 3. 支撑（权重归一传递件，A 件 1 消费位）：值场逐点 ≤ B ⟹            *)
(*    聚合 ≤ B（Σw == 1 归一收口）。                                   *)
(* ============================================================ *)

Lemma attn_aggregate_le_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)) (B : Real),
    Not (Id ss nil) ->
    (forall s : Real, real_le (f s) B) ->
    real_le (attn_aggregate ss f Wp) B.
Proof.
  intros ss f Wp B Hnil Hub. unfold attn_aggregate.
  assert (Hwp : forall s : Real, real_lt real_zero (attn_weight ss Wp s)).
  { intro s. unfold attn_weight.
    exact (real_mult_positive
             (sf_exp_score s) (real_inv_pos (sf_partition ss) Wp)
             (real_exp_neg_pos (real_opp s))
             (real_inv_pos_pos (sf_partition ss) Wp)). }
  apply (real_le_trans
           _ (real_mult B (real_list_sum Real (attn_weight ss Wp) ss))).
  - exact (attn_wsum_le_scale ss (attn_weight ss Wp) f B Hwp Hub).
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             (real_mult B (real_list_sum Real (attn_weight ss Wp) ss))
             (real_mult B real_one)
             B).
    + apply (RealSetoid.real_eq_mult_compat
               B (real_list_sum Real (attn_weight ss Wp) ss) B real_one).
      * apply real_eq_refl.
      * exact (attn_weights_sum_one_pt ss Hnil Wp).
    + exact (real_mult_one B).
Qed.

(* ============================================================ *)
(* 4. 支撑（最大值控制件 max ≤ sum 型，list 面，InT 逐点受限版）：      *)
(*    逐点非负列表的非负和 + 任意元素 ≤ 全和。                          *)
(* ============================================================ *)

Lemma attn_sum_nonneg :
  forall (X : Set) (g : X -> Real) (l : list X),
    (forall w : X, InT w l -> real_le real_zero (g w)) ->
    real_le real_zero (real_list_sum X g l).
Proof.
  intros X g l Hnn. induction l as [| a rest IH].
  - cbn [real_list_sum]. apply real_le_refl.
  - cbn [real_list_sum].
    apply (RealSetoid.real_le_id_l real_zero (real_plus real_zero real_zero)).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply Hnn. apply InT_here.
      * apply IH. intros w Hw. apply Hnn. apply InT_next. exact Hw.
Qed.

Lemma attn_elem_le_sum :
  forall (X : Set) (g : X -> Real) (l : list X),
    (forall w : X, InT w l -> real_le real_zero (g w)) ->
    forall x : X, InT x l -> real_le (g x) (real_list_sum X g l).
Proof.
  intros X g l. induction l as [| a rest IH]; intros Hnn x Hin.
  - inversion Hin.
  - cbn [real_list_sum].
    assert (Hadd : forall z : Real,
              real_le z (real_plus z (real_list_sum X g rest))).
    { intro z. apply (RealSetoid.real_le_id_l z (real_plus z real_zero)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply real_le_plus_compat.
        + apply real_le_refl.
        + apply (attn_sum_nonneg X g rest).
          intros w Hw. apply Hnn. apply InT_next. exact Hw. }
    assert (Hnnr : forall w : X, InT w rest -> real_le real_zero (g w)).
    { intros w Hw. apply Hnn. apply InT_next. exact Hw. }
    inversion Hin as [Heq | y0 l0 Hrec]; subst.
    + apply Hadd.
    + apply (sf_smx_le_add_left (g a) (g x) (real_list_sum X g rest)).
      * apply Hnn. apply InT_here.
      * exact (IH Hnnr x Hrec).
Qed.

(* ============================================================ *)
(* 5. 聚合/倾斜配分正性（逐点正值 + 元素支配 + lt-le 传递）。           *)
(* ============================================================ *)

Lemma attn_aggregate_pos :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)),
    Not (Id ss nil) ->
    (forall s : Real, InT s ss -> real_lt real_zero (f s)) ->
    real_lt real_zero (attn_aggregate ss f Wp).
Proof.
  intros ss f Wp Hnil Hb. unfold attn_aggregate.
  destruct ss as [| a rest].
  - destruct (Hnil (id_refl : Id nil nil)).
  - apply (real_lt_le_trans
             real_zero
             (real_mult (attn_weight (a :: rest) Wp a) (f a))
             (real_list_sum Real
                (fun s => real_mult (attn_weight (a :: rest) Wp s) (f s))
                (a :: rest))).
    + apply (real_mult_positive
               (attn_weight (a :: rest) Wp a) (f a)).
      * unfold attn_weight.
        apply (real_mult_positive
                 (sf_exp_score a) (real_inv_pos (sf_partition (a :: rest)) Wp)
                 (real_exp_neg_pos (real_opp a))
                 (real_inv_pos_pos (sf_partition (a :: rest)) Wp)).
      * apply (Hb a). apply InT_here.
    + apply (attn_elem_le_sum Real
               (fun s => real_mult (attn_weight (a :: rest) Wp s) (f s))
               (a :: rest)).
      * intros w Hw. left.
        apply (real_mult_positive
                 (attn_weight (a :: rest) Wp w) (f w)).
        -- unfold attn_weight.
           apply (real_mult_positive
                    (sf_exp_score w) (real_inv_pos (sf_partition (a :: rest)) Wp)
                    (real_exp_neg_pos (real_opp w))
                    (real_inv_pos_pos (sf_partition (a :: rest)) Wp)).
        -- exact (Hb w Hw).
      * apply InT_here.
Qed.

Lemma attn_tilted_pos :
  forall (ss : list Real) (f : Real -> Real),
    Not (Id ss nil) ->
    (forall s : Real, InT s ss -> real_lt real_zero (f s)) ->
    real_lt real_zero (attn_tilted ss f).
Proof.
  intros ss f Hnil Hb. unfold attn_tilted.
  destruct ss as [| a rest].
  - destruct (Hnil (id_refl : Id nil nil)).
  - apply (real_lt_le_trans
             real_zero
             (real_mult (sf_exp_score a) (f a))
             (real_list_sum Real
                (fun s => real_mult (sf_exp_score s) (f s)) (a :: rest))).
    + apply (real_mult_positive (sf_exp_score a) (f a)).
      * apply (real_exp_neg_pos (real_opp a)).
      * apply (Hb a). apply InT_here.
    + apply (attn_elem_le_sum Real
               (fun s => real_mult (sf_exp_score s) (f s)) (a :: rest)).
      * intros w Hw. left.
        apply (real_mult_positive (sf_exp_score w) (f w)).
        -- apply (real_exp_neg_pos (real_opp w)).
        -- exact (Hb w Hw).
      * apply InT_here.
Qed.

(* ============================================================ *)
(* 6. B 件消费位（G08:192 gibbsd_p_mult_ratio）：倾斜配分恒等           *)
(*    T == Z·Agg（逐项 real_list_sum_ext 装配；B 件在 A×B 装配中的      *)
(*    主消费面）。                                                     *)
(* ============================================================ *)

Lemma attn_tilted_eq :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss)),
    real_eq (attn_tilted ss f)
            (real_mult (sf_partition ss) (attn_aggregate ss f Wp)).
Proof.
  intros ss f Wp. unfold attn_tilted, attn_aggregate.
  apply (real_eq_trans
           (real_list_sum Real (fun s => real_mult (sf_exp_score s) (f s)) ss)
           (real_list_sum Real
              (fun s => real_mult
                          (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s))
              ss)
           (real_mult (sf_partition ss)
              (real_list_sum Real
                 (fun s => real_mult (attn_weight ss Wp s) (f s)) ss))).
  - apply (real_list_sum_ext Real).
    intro s.
    apply (RealSetoid.real_eq_mult_compat
             (sf_exp_score s) (f s)
             (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s)).
    + apply real_eq_sym.
      exact (gibbsd_p_mult_ratio (sf_partition ss) (sf_exp_score s) Wp).
    + apply real_eq_refl.
  - apply (real_eq_trans
             (real_list_sum Real
                (fun s => real_mult
                            (real_mult (sf_partition ss) (attn_weight ss Wp s)) (f s))
                ss)
             (real_list_sum Real
                (fun s => real_mult (sf_partition ss)
                            (real_mult (attn_weight ss Wp s) (f s)))
                ss)
             (real_mult (sf_partition ss)
                (real_list_sum Real
                   (fun s => real_mult (attn_weight ss Wp s) (f s)) ss))).
    + apply (real_list_sum_ext Real).
      intro s. apply real_eq_sym.
      exact (real_mult_assoc (sf_partition ss) (attn_weight ss Wp s) (f s)).
    + exact (real_list_sum_linear Real (sf_partition ss)
               (fun s => real_mult (attn_weight ss Wp s) (f s)) ss).
Qed.

(* ============================================================ *)
(* 7. 主件：注意力聚合的 log-partition 型上界（plain real_le；          *)
(*    单调升向，零反单调硬攻）。                                        *)
(*    Z·Agg ≤ Z·B（聚合界 + 正缩放保序）⟹ log(Z·Agg) ≤ log Z + log B。 *)
(* ============================================================ *)

Theorem attn_log_partition_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                       (real_mult_positive (sf_partition ss)
                          (attn_aggregate ss f Wp) Wp HposAgg))
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposAgg HAggB.
  assert (Hscale : real_le (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                           (real_mult (sf_partition ss) B)).
  { apply (real_le_trans
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             (real_mult (attn_aggregate ss f Wp) (sf_partition ss))
             (real_mult (sf_partition ss) B)).
    - apply real_eq_le_bridge. apply real_mult_comm.
    - apply (real_le_trans
               (real_mult (attn_aggregate ss f Wp) (sf_partition ss))
               (real_mult B (sf_partition ss))
               (real_mult (sf_partition ss) B)).
      + exact (real_le_mult_compat
                 (attn_aggregate ss f Wp) B (sf_partition ss) Wp HAggB).
      + apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm. }
  apply (real_le_trans
           (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                     (real_mult_positive (sf_partition ss)
                        (attn_aggregate ss f Wp) Wp HposAgg))
           (real_log (real_mult (sf_partition ss) B)
                     (real_mult_positive (sf_partition ss) B Wp HB))
           (real_plus (real_log (sf_partition ss) Wp) (real_log B HB))).
  - apply (real_log_le_mono
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             (real_mult (sf_partition ss) B)
             (real_mult_positive (sf_partition ss)
                (attn_aggregate ss f Wp) Wp HposAgg)
             (real_mult_positive (sf_partition ss) B Wp HB)).
    exact Hscale.
  - apply real_eq_le_bridge.
    exact (real_log_mult (sf_partition ss) B Wp HB).
Qed.

(* ============================================================ *)
(* 8. 主件诚实接口全形：正性/聚合界证书由本文件支撑件放电。             *)
(* ============================================================ *)

Theorem attn_log_partition_bound_full :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B),
    forall (Hnil : Not (Id ss nil)),
    forall (Hb : forall s : Real, InT s ss -> real_lt real_zero (f s)),
    forall (Hub : forall s : Real, real_le (f s) B),
    real_le (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                       (real_mult_positive (sf_partition ss)
                          (attn_aggregate ss f Wp) Wp
                          (attn_aggregate_pos ss f Wp Hnil Hb)))
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB Hnil Hb Hub.
  apply (attn_log_partition_bound ss f Wp B HB           (attn_aggregate_pos ss f Wp Hnil Hb)           (attn_aggregate_le_bound ss f Wp B Hnil Hub)).
Qed.

(* ============================================================ *)
(* 9. 倾斜配分面：log(Σ e^s·f(s)) ≤ log Z + log B                      *)
(*    （B 件恒等 attn_tilted_eq 运输 + 主件）。                         *)
(* ============================================================ *)

Theorem attn_tilted_le_log_bound :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposT : real_lt real_zero (attn_tilted ss f))
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le (real_log (attn_tilted ss f) HposT)
            (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposT HposAgg HAggB.
  apply (real_le_trans
           (real_log (attn_tilted ss f) HposT)
           (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                     (real_mult_positive (sf_partition ss)
                        (attn_aggregate ss f Wp) Wp HposAgg))
           (real_plus (real_log (sf_partition ss) Wp) (real_log B HB))).
  - apply real_eq_le_bridge.
    exact (real_log_wd (attn_tilted ss f)
             (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
             HposT
             (real_mult_positive (sf_partition ss)
                (attn_aggregate ss f Wp) Wp HposAgg)
             (attn_tilted_eq ss f Wp)).
  - exact (attn_log_partition_bound ss f Wp B HB HposAgg HAggB).
Qed.

(* ============================================================ *)
(* 10. A 件 2 消费位（S12:12017 sf_softmax_le_one）+ B 件第二消费位：   *)
(*     逐 logit 配分控制 s ≤ log Z（log-partition 支配下界面）。        *)
(* ============================================================ *)

Theorem attn_logit_le_log_partition :
  forall (ss : list Real) (Wp : real_lt real_zero (sf_partition ss))
         (s : Real),
    InT s ss ->
    real_le s (real_log (sf_partition ss) Wp).
Proof.
  intros ss Wp s Hin.
  assert (Hw1 : real_le (attn_weight ss Wp s) real_one).
  { unfold attn_weight. exact (sf_softmax_le_one ss s Wp Hin). }
  assert (H1 : real_eq (real_mult (sf_partition ss) (attn_weight ss Wp s))
                       (sf_exp_score s)).
  { exact (gibbsd_p_mult_ratio (sf_partition ss) (sf_exp_score s) Wp). }
  assert (H2 : real_le (real_mult (sf_partition ss) (attn_weight ss Wp s))
                       (real_mult (sf_partition ss) real_one)).
  { apply (real_le_trans
             (real_mult (sf_partition ss) (attn_weight ss Wp s))
             (real_mult (attn_weight ss Wp s) (sf_partition ss))
             (real_mult (sf_partition ss) real_one)).
    - apply real_eq_le_bridge. apply real_mult_comm.
    - apply (real_le_trans
               (real_mult (attn_weight ss Wp s) (sf_partition ss))
               (real_mult real_one (sf_partition ss))
               (real_mult (sf_partition ss) real_one)).
      + exact (real_le_mult_compat
                 (attn_weight ss Wp s) real_one (sf_partition ss) Wp Hw1).
      + apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_comm. }
  assert (HewZ : real_le (sf_exp_score s) (sf_partition ss)).
  { apply (real_le_trans
             (sf_exp_score s)
             (real_mult (sf_partition ss) (attn_weight ss Wp s))
             (sf_partition ss)).
    - apply real_eq_le_bridge. apply real_eq_sym. exact H1.
    - apply (real_le_trans
               (real_mult (sf_partition ss) (attn_weight ss Wp s))
               (real_mult (sf_partition ss) real_one)
               (sf_partition ss)).
      + exact H2.
      + apply real_eq_le_bridge. exact (real_mult_one (sf_partition ss)). }
  apply (real_le_trans
           s
           (real_log (sf_exp_score s) (real_exp_neg_pos (real_opp s)))
           (real_log (sf_partition ss) Wp)).
  - apply real_eq_le_bridge.
    apply (real_eq_trans
             s
             (real_opp (real_opp s))
             (real_log (sf_exp_score s) (real_exp_neg_pos (real_opp s)))).
    + apply real_eq_sym. exact (real_opp_opp s).
    + apply real_eq_sym. exact (real_log_exp_neg (real_opp s)).
  - exact (real_log_le_mono
             (sf_exp_score s)
             (sf_partition ss)
             (real_exp_neg_pos (real_opp s))
             Wp
             HewZ).
Qed.

(* ============================================================ *)
(* 11. B 形出口（UpRealLeB real_le_to_le_b 单向桥；eps/B 面零硬攻）。   *)
(* ============================================================ *)

Corollary attn_log_partition_bound_B :
  forall (ss : list Real) (f : Real -> Real)
         (Wp : real_lt real_zero (sf_partition ss))
         (B : Real) (HB : real_lt real_zero B)
         (HposAgg : real_lt real_zero (attn_aggregate ss f Wp))
         (HAggB : real_le (attn_aggregate ss f Wp) B),
    real_le_b (real_log (real_mult (sf_partition ss) (attn_aggregate ss f Wp))
                        (real_mult_positive (sf_partition ss)
                           (attn_aggregate ss f Wp) Wp HposAgg))
              (real_plus (real_log (sf_partition ss) Wp) (real_log B HB)).
Proof.
  intros ss f Wp B HB HposAgg HAggB.
  apply real_le_to_le_b.
  exact (attn_log_partition_bound ss f Wp B HB HposAgg HAggB).
Qed.

(* ============================================================ *)
(* 12. 假设审计（文末 Print Assumptions ≥1）。                          *)
(* ============================================================ *)

Print Assumptions attn_log_partition_bound.
Print Assumptions attn_log_partition_bound_full.
Print Assumptions attn_tilted_le_log_bound.
Print Assumptions attn_logit_le_log_partition.
Print Assumptions attn_log_partition_bound_B.
