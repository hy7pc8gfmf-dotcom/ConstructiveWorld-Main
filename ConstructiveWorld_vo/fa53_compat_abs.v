(* ============================================================ *)
(* fa53_compat_abs.v — T40 消融50 席位VC（E-STAGING-VC）C 类施工件 *)
(*                                                               *)
(* 对账面（详见 T40-VC-对账.md §11）：消融辖区两族"诚实接口槽"，  *)
(*   族1 加法保序严格×非严（lt a b -> le c d -> lt (a+c) (b+d)）： *)
(*     槽位 S13_NLiveAudit:2349 / AttnDoeblin:158（bs_lpc 同语句  *)
(*     AttnDoeblin:476 / S13:2667）；辖区外同语句槽 S04:285、      *)
(*     UpFirewall:107、SqrtfCauchy:73、UpEntropyGainReq:91 同受益。 *)
(*   族2 le 版 abs 恒等（le zero a -> Id (abs a) a）：             *)
(*     槽位 S13:2348 / AttnDoeblin:157（bs_abs 同语句 :475/S13:2666）； *)
(*     S06_DiffSamplingGibbs:4031 挂账"诚实缺口"同语句受益。        *)
(*                                                               *)
(* 收口原理：两族槽在 RealInterfaceEnhanced 纯字段内不可直接导出   *)
(*   （缺单侧严格平移），但 S01_BaseRing:329 已有 DecidableOrder   *)
(*   可判定序扩展类（Set 层 Or 三分），本件五步收口：              *)
(*   ① le 加法右消去（le_plus_compat 加 -c + 环归一位运河）；      *)
(*   ② 单侧严格平移（Not(le) 经 not_le_lt 翻转，矛盾支撞 irrefl）  *)
(*      ——此件为接口层新果实（S07:6118 配套 translate 件此前仅     *)
(*      具体 Real 层）；                                           *)
(*   ③④ 族1/族2 主件：三分分解，双严走 lt_plus_compat 字段，      *)
(*      eq 支走 id_cong 运河 + ②平移，反侧支撞 lt_irrefl 归谬；    *)
(*   ⑤ abs 恒等：lt 支走 abs_pos 字段（S01:293），eq 支走          *)
(*      id_cong abs + abs_zero 的 id 链，反侧支同归谬。            *)
(*   ——前提可由库内件构造兑现，条件可收口：C 类消融定谳。          *)
(*                                                               *)
(* 纪律：语句面全 Set 层（Or/Not/Empty_set 均为 S01 Set 层定义），  *)
(*   零 Prop 泄露；无 Axiom/Admitted/Parameter/Conjecture/Abort；  *)
(*   非平凡真证（消去/平移/三分/归谬四段字段链）。原树零改。       *)
(* ============================================================ *)

Require Import S01_BaseRing.

Section Fa53CompatAbs.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 投影别名：类字段名 lt_dec 被 Stdlib Compare_dec.lt_dec 遮蔽；
   not_le_lt 一并解构防同类遮蔽（S06_DiffSamplingGibbs:5157 定式） *)
Definition fa53_lt_dec : forall a b : R, Or (lt a b) (Or (Id a b) (lt b a)) :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => lt_d
  end.

Definition fa53_not_le_lt : forall a b : R, Not (le a b) -> lt b a :=
  match DO with
  | Build_DecidableOrder _ ord lt_d eqd nll lti => nll
  end.

(* ---- 支撑①：x + (c + -c) 归一位（环恒等运河，S01 关联方向：     *)
(*      plus_assoc 为 LHS 右结合向 RHS 左结合） ---- *)
Lemma fa53_plus_assoc_opp_r :
  forall x c : R, Id (plus (plus x c) (opp c)) x.
Proof.
  intros x c.
  exact (id_trans (id_sym (plus_assoc x c (opp c)))
                  (id_trans (id_cong (fun w => plus x w) (plus_opp c))
                            (plus_zero x))).
Qed.

(* ---- 支撑②：le 加法右消去（消去严格化的前置件） ---- *)
Lemma fa53_le_plus_cancel_r :
  forall a b c : R, le (plus b c) (plus a c) -> le b a.
Proof.
  intros a b c H.
  apply (le_id_r b (plus (plus a c) (opp c)) a).
  - exact (fa53_plus_assoc_opp_r a c).
  - apply (le_id_l b (plus (plus b c) (opp c)) (plus (plus a c) (opp c))).
    + exact (id_sym (fa53_plus_assoc_opp_r b c)).
    + exact (le_plus_compat (plus b c) (plus a c) (opp c) (opp c) H
                            (le_refl (opp c))).
Qed.

(* ---- 支撑③（新果实）：单侧严格平移（接口 + 可判定序层） ----
   lt a b ⟹ ¬(le (b+c) (a+c))（否则右消去得 le b a，与 lt a b
   撞 le_lt_trans + lt_irrefl）⟹ not_le_lt 翻转出严格。 *)
Lemma fa53_lt_plus_translate_r :
  forall a b c : R, lt a b -> lt (plus a c) (plus b c).
Proof.
  intros a b c Hab.
  apply (fa53_not_le_lt (plus b c) (plus a c)).
  intro Hle.
  destruct (lt_irrefl b
    (le_lt_trans b a b (fa53_le_plus_cancel_r a b c Hle) Hab)).
Qed.

(* ---- 支撑③'：单侧严格平移（左前置形，由③经两次交换运河） ---- *)
Lemma fa53_lt_plus_translate_l :
  forall a b c : R, lt a b -> lt (plus c a) (plus c b).
Proof.
  intros a b c Hab.
  apply (lt_id_r (plus c a) (plus b c) (plus c b)).
  - exact (plus_comm b c).
  - apply (lt_id_l (plus c a) (plus a c) (plus b c)).
    + exact (plus_comm c a).
    + exact (fa53_lt_plus_translate_r a b c Hab).
Qed.

(* ---- 件1：严格×非严加法保序（族1 槽位消融主件） ----
   三分 c d：inl 双严走 lt_plus_compat；inr-eq 走 id_cong 运河 +
   ③平移；inr-gt 与 le c d 撞 irrefl。 *)
Theorem fa53_lt_plus_compat_lt_le_dec :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct (fa53_lt_dec c d) as [Hcd_lt | [Hcd_eq | Hcd_gt]].
  - (* c < d：双严相加 *)
    exact (lt_plus_compat a b c d Hab Hcd_lt).
  - (* c == d：b+d 归 b+c，严格性由平移件供给 *)
    apply (lt_id_r (plus a c) (plus b c) (plus b d)).
    + exact (id_cong (fun x => plus b x) Hcd_eq).
    + exact (fa53_lt_plus_translate_r a b c Hab).
  - (* d < c：与 le c d 冲突 ⟹ lt d d ⟹ irrefl 归谬 *)
    destruct (lt_irrefl d (lt_le_trans d c d Hcd_gt Hcd)).
Qed.

(* ---- 件2：镜像非严×严格加法保序（族1 对偶槽位） ----
   三分 a b：inl 双严；inr-eq 走 id_cong 运河 + ③平移（b 侧）；
   inr-gt 与 le a b 撞 irrefl。与件1 对称，同为无条件件。 *)
Theorem fa53_lt_plus_compat_le_lt_dec :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  destruct (fa53_lt_dec a b) as [Hab_lt | [Hab_eq | Hab_gt]].
  - (* a < b：双严相加 *)
    exact (lt_plus_compat a b c d Hab_lt Hcd).
  - (* a == b：a+c 归 b+c，严格性由平移件供给 *)
    apply (lt_id_l (plus a c) (plus b c) (plus b d)).
    + exact (id_cong (fun x => plus x c) Hab_eq).
    + exact (fa53_lt_plus_translate_l c d b Hcd).
  - (* b < a：与 le a b 冲突 ⟹ lt a a ⟹ irrefl 归谬 *)
    destruct (lt_irrefl a (le_lt_trans a b a Hab Hab_gt)).
Qed.

(* ---- 件3：le 版 abs 恒等（族2 槽位消融主件） ----
   三分 zero a：lt 支走 abs_pos 字段（S01:293）；eq 支走
   id_cong abs + abs_zero 的 id 链；反侧支撞 irrefl。
   —— abs_ge_zero_id_cc 全体槽位的接口级完整消解形：
      库内此前仅有 lt 版 abs_pos 字段与具体 Real 层佐证组合。 *)
Theorem fa53_abs_ge_zero_id_dec :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  destruct (fa53_lt_dec zero a) as [Hza | [Hza_eq | Haz]].
  - (* 0 < a：正保持字段直给 *)
    exact (abs_pos a Hza).
  - (* 0 == a：|a| == |0| == 0 == a（id 链三步） *)
    exact (id_trans (id_cong abs (id_sym Hza_eq))
                    (id_trans abs_zero Hza_eq)).
  - (* a < 0：与 le zero a 冲突 ⟹ lt a a ⟹ irrefl 归谬 *)
    destruct (lt_irrefl a (lt_le_trans a zero a Haz Ha)).
Qed.

(* ---- 件4：族2 的 bs 形状直配（改喂锚定形） ----
   AttnDoeblin:475 / S13:2666 的 bs_abs 槽位与件3 逐字同语句，
   此处给显式改喂形（对账坐标锚定）。 *)
Corollary fa53_bs_abs_shape :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  exact (fun a Ha => fa53_abs_ge_zero_id_dec a Ha).
Qed.

End Fa53CompatAbs.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明） ---- *)
Print Assumptions fa53_le_plus_cancel_r.
Print Assumptions fa53_lt_plus_translate_r.
Print Assumptions fa53_lt_plus_translate_l.
Print Assumptions fa53_lt_plus_compat_lt_le_dec.
Print Assumptions fa53_lt_plus_compat_le_lt_dec.
Print Assumptions fa53_abs_ge_zero_id_dec.
Print Assumptions fa53_bs_abs_shape.
