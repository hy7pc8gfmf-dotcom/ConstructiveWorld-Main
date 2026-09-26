(* ============================================================ *)
(* UpAblT12_UpRealLeB2.v —— 假设消融战役 T12 扫尾席（sumf 零头 5 位之 UpRealLeB2  *)
(* 1 位，Real 载体）                                                          *)
(* 辖区：UpRealLeB2.v RealKVQuantLeB 节（L464-616）求和正性假设位               *)
(*   L482-483 real_evicted_partition_pos（一位）                                *)
(* 放电母本：正和族 sumd_list_sum_pos@UpReqSumD:224（同构自持升 Type 层）        *)
(*   + real_exp_neg_pos@S07_RealSetoidExpLog:7774                               *)
(*                                                              *)
(* 目的：real_evicted_partition_pos（Z=逐出配分函数 > 0）在具体有限和实例        *)
(*   real_sum_over_S := fun g => uabT12_rsum S g enum 上无条件成立——            *)
(*   前提减薄为纯数据槽（枚举清单 + 保留元证书），假设位消除。                   *)
(*                                                              *)
(* 主件清单（1 件，前缀 uabT12_）：                                             *)
(*    A1 uabT12_rl2_evicted_partition_pos ←L482-483                             *)
(*        放电：正和族同构自持机械（本节 uabT12_rsum_pos，逐腿同                 *)
(*        sumd_list_sum_pos_cons@UpReqSumD 款式）× real_exp_neg_pos 直喂。       *)
(*                                                              *)
(* 升层申报（诚实口径，非降档）：                                               *)
(*   ① 被消融位所在节 S : Type（UpRealLeB2 L466 逐字），而 sumd_list_sum/in      *)
(*     机械钉 S : Set（UpReqSumD 出节签名 Check 实测）——照搬即隐性降档。        *)
(*     本件同构自持本节机械于 S : Type 层，零降格零窄化；归纳链逐腿复刻           *)
(*     sumd_list_sum_pos_cons/nonneg 款式（纯接口字段组装）。                   *)
(*   ② 数据槽显式参（移交单预告「列表级 pos 形，非 sumf 槽形」实测核实）：        *)
(*     被消融函数对非保留元取值 real_zero（非严格正），全列表逐项严格正不可得——  *)
(*     pos 面须加强为「保留元证书」槽 uabT12_find_kept（枚举清单携带保留元）      *)
(*     + 逐点两支（保留支严格正 × 非保留支非负）。槽形变化如实登记。             *)
(*                                                              *)
(* 分级：N2（由库内已证件 sumd 正和族同构导出 + real_exp_neg_pos 直喂；           *)
(*   witness 归纳链为本件独立构造内容，非 trivial 直连）。                       *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219（real_evicted_      *)
(*   partition/real_kv_boltzmann_factor/real_exp_neg_pos 经其 Export 链供给）、  *)
(*   UpReqSumD（sumd_lt_le 抬升腿）。                                           *)
(*   语句面逐字抽取自现档 UpRealLeB2.v L482-483（两树逐字节同验：Main/Live_X    *)
(*   md5 同 3655bc7f，667 行）；real_evicted_partition 七参形经 Check 轮实测。   *)
(*                                                              *)
(* 备注：语句面全集合层；公理面零新增；文尾 Print Assumptions 收尾。              *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblT12_UpRealLeB2.log。               *)
(*   G3 预期：Real 载体树拉入 S07_RealSetoidExpLog，inherent 伪影按 T6a 登记口径  *)
(*   放行（T6a 同形先例 71 处，实例记录字段打包位，与被消融语句零涉）。          *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ 正和机械（S : Type 层，sumd 同构自持） ============ *)
(* 与 UpReqSumD SumDischarge 节的 sumd_list_sum/sumd_in 同构，S 升 Type 层       *)
(* （被消融位所在节 S : Type 逐字对齐）；接口字段纯组装，零新公理。              *)
Section UabT12RListPos.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Type.
Variable keep : S -> Set.

(* 列表和机器（sumd_list_sum 同构，Type 层） *)
Fixpoint uabT12_rsum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => zero
  | y :: t => plus (f y) (uabT12_rsum f t)
  end.

(* 保留元证书（sumd_in 同构换 keep 形：免等词、免成员归纳，证书即保留元本体） *)
Fixpoint uabT12_find_kept (l : list S) : Set :=
  match l with
  | nil => Empty_set
  | y :: t => (keep y) + (uabT12_find_kept t)
  end.

(* 非负腿（sumd_list_sum_nonneg 同构） *)
Lemma uabT12_rsum_nonneg : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) -> le zero (uabT12_rsum f l).
Proof.
  intros f l Hnn. induction l as [| y t IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus (f y) (uabT12_rsum f t))
             (req_sym (plus zero zero) zero (plus_zero zero))
             (le_plus_compat zero (f y) zero (uabT12_rsum f t)
                (Hnn y) IH)).
Qed.

(* 正和腿（保留元证书形；归纳链逐腿同 sumd_list_sum_pos_cons 款式） *)
Lemma uabT12_rsum_pos : forall (f : S -> R) (l : list S),
  (forall s : S, le zero (f s)) ->
  (forall s : S, keep s -> lt zero (f s)) ->
  uabT12_find_kept l ->
  lt zero (uabT12_rsum f l).
Proof.
  intros f l Hnn Hpos. induction l as [| y t IH]; intro Hw.
  - destruct Hw.
  - destruct Hw as [Hy | Hwt].
    + (* 头元保留：f y > 0 抬全和（pos_cons 同构） *)
      exact (lt_le_trans zero (f y) (plus (f y) (uabT12_rsum f t)) (Hpos y Hy)
               (le_id_l (f y) (plus (f y) zero) (plus (f y) (uabT12_rsum f t))
                  (req_sym (plus (f y) zero) (f y) (plus_zero (f y)))
                  (le_plus_compat (f y) (f y) zero (uabT12_rsum f t)
                     (le_refl (f y))
                     (uabT12_rsum_nonneg f t Hnn)))).
    + (* 尾段携带证书：和尾 > 0，头项非负抬全和（comm 换位后 pos_cons 同构；
         接口 plus_zero 为右零形，左零经 plus_comm+req_lt_compat 换轨） *)
      exact (req_lt_compat zero zero
               (plus (uabT12_rsum f t) (f y)) (plus (f y) (uabT12_rsum f t))
               (req_refl zero) (plus_comm (uabT12_rsum f t) (f y))
               (lt_le_trans zero (uabT12_rsum f t)
                  (plus (uabT12_rsum f t) (f y))
                  (IH Hwt)
                  (le_id_l (uabT12_rsum f t) (plus (uabT12_rsum f t) zero)
                     (plus (uabT12_rsum f t) (f y))
                     (req_sym (plus (uabT12_rsum f t) zero) (uabT12_rsum f t)
                        (plus_zero (uabT12_rsum f t)))
                     (le_plus_compat (uabT12_rsum f t) (uabT12_rsum f t) zero (f y)
                        (le_refl (uabT12_rsum f t)) (Hnn y))))).
Qed.

End UabT12RListPos.

(* ============ A1 ←UpRealLeB2.v L482-483（逐字语句面，实例位换装） ============ *)
(* 原位：Variable real_evicted_partition_pos : real_lt real_zero
   (real_evicted_partition S keep keep_dec real_energy D D_pos real_sum_over_S).
   本件：real_sum_over_S 换具体实例 fun g => uabT12_rsum S g enum，
   并以数据槽（enum + 保留元证书）替代原假设位。 *)
Theorem uabT12_rl2_evicted_partition_pos :
  forall (S : Type) (keep : S -> Set)
    (keep_dec : forall s : S, Or (keep s) (Not (keep s)))
    (real_energy : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (enum : list S) (Hkept : uabT12_find_kept S keep enum),
    real_lt real_zero
      (real_evicted_partition S keep keep_dec real_energy D D_pos
         (fun g : S -> Real => uabT12_rsum S g enum)).
Proof.
  intros S keep keep_dec real_energy D D_pos enum Hkept.
  assert (Hnn : forall s : S,
    le real_zero
      (if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                     else real_zero)).
  { intro s. destruct (keep_dec s) as [Hk | Hc].
    - exact (sumd_lt_le (real_kv_boltzmann_factor S real_energy D D_pos s)
               (real_exp_neg_pos
                  (real_mult (real_inv_pos D D_pos) (real_energy s)))).
    - exact (le_refl real_zero). }
  assert (Hpos : forall s : S, keep s ->
    lt real_zero
      (if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                     else real_zero)).
  { intros s Hk. destruct (keep_dec s) as [Hk' | Hc].
    - exact (real_exp_neg_pos
               (real_mult (real_inv_pos D D_pos) (real_energy s))).
    - destruct (Hc Hk). }
  unfold real_evicted_partition.
  exact (uabT12_rsum_pos S keep
           (fun s : S => if keep_dec s then real_kv_boltzmann_factor S real_energy D D_pos s
                                     else real_zero)
           enum Hnn Hpos Hkept).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT12_rl2_evicted_partition_pos.
