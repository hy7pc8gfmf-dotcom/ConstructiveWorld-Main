(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   upreq_exp_pos（原 L148，2 句玩具证）                                 *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T339 恒等守恒更正注记】2026-09-22 包AW十四 台账席（恒等头注更正第四批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337／T339 台账。 *)
(* 附记：T277 判级全文恒等；Y 域收尾＋AB 域收尾＋AD 域直推第四批（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqExpPos.v *)
(* *)
(* 目的： 指数函数的构造性正性：e^x > 0 五步链。 *)
(* 主件： upreq_exp_pos：指数逐点正性；upreq_exp_neg_ne_zero / upreq_real_zero_ne_one 链节。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 五步链逐节对应，判定面为诚实裁决表；纯构造性。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqExpPos.v —— 席T42：eˣ > 0 构造性正性证明专席（2026-09-11）  *)
(*                                                                *)
(* 目标定理：forall x : Real, real_lt real_zero (real_exp_neg      *)
(*   (real_opp x))——即 0 < eˣ（对全部实数 x 无条件；real_exp_neg    *)
(*   (real_opp x) = e^{−(−x)} = eˣ，real_lt 为 sigT 见证形：需显式  *)
(*   ε>0 一致分离见证，非平凡正性）。                              *)
(*                                                                *)
(* 起步四读裁决（关键现态）：库内 exp_neg_pos 在 Real 层已有证明链： *)
(*   S03_QExp:6412 cauchy_real_exp_pos（幂级数 ε-见证构造：         *)
(*   exp_series_arch 取 C、偶截断 ≥ 1/C、奇截断 ≥ 1/(2C)、         *)
(*   ε := 1/(2C)、N := 2·m0+1；Qed 闭合）                          *)
(*   → S07:7766 real_exp_neg_pos（unfold 后 cauchy_real_exp_pos     *)
(*   直连）。故目标定理一步实例化闭合（件 4），本件结果按任务书     *)
(*   预案改做「接口字段 Real 实例化验证」+ 五步链可结果腿全量落件。 *)
(*                                                                *)
(* 五步链逐步对应表（诚实裁决）：                                  *)
(*   步骤1 eˣ·e⁻ˣ=eˣ⁺⁽⁻ˣ⁾=e⁰=1   → 件 2 upreq_exp_neg_unit         *)
(*     （exp_neg_plus 反向 + real_plus_opp + real_eq_opp_compat    *)
(*     + cauchy_real_exp_wd + exp_neg_zero；新建）                *)
(*   步骤2 ∴ eˣ ≠ 0（有逆元）    → 件 3 upreq_exp_neg_ne_zero      *)
(*     + 件 1 upreq_real_zero_ne_one（Real 层 0≠1 底座，库内缺位   *)

(*   步骤3 eˣ=(eˣᐟ²)²            → 未落件：halving 件库内缺位      *)

(*     平方形态在本库 Or 编码下并不能推进闭合，见下）              *)
(*   步骤4 所有平方 ≥ 0（Or 形） → 不可证裁决：本库 real_le 为      *)
(*     Or 编码（S02:460），平方非负库内现态是否定式                 *)
(*     real_square_not_negative : Not (a·a < 0)（S02:802），其自注  *)
(*     明示「信息性 real_le 的全称形式不可证（需判定 a 的符号）」   *)
(*     ——Or 左支需真实 ε 见证，平方表示不产出见证，右支排除后      *)
(*     取左支即等价于判定符号（LPO 等价面）。修正路线：Or 的左支    *)
(*     由级数 ε-见证直供（cauchy_real_exp_pos），此即件 4。        *)
(*   步骤5 Or 两支消解           → 件 5 upreq_exp_pos_or_destruct   *)
(*     （destruct Or：左支 Hpos 直达目标；右支 0==eˣ 经件 3 归谬    *)
(*     得 Empty_set 消去——False_rect 工艺的 Set 层等价形态，       *)
(*     标准构造性反证，不触判定公理面）                            *)
(*                                                                *)
(* 库件消费清单（零新假设位）：cauchy_real_exp_pos / real_exp_neg_  *)
(*   pos / real_exp_neg_zero / real_exp_neg_plus /                 *)
(*   cauchy_real_exp_wd / real_eq_opp_compat / real_eq_mult_compat *)
(*   （S07）；real_eq_refl/sym/trans、real_plus_opp、real_mult_comm *)
(*   、real_mult_zero、qltT_0_1、real_lt/real_le 定义（S02）；      *)
(*   NatLe_lift、Id、Not、Or（S01）；Nat.le_refl（vendored）。     *)
(*                                                                *)
(* 红线自查：Set 层语句（real_lt/real_eq/real_le/Not/Id 皆 Set 值， *)
(*   零 Prop 表出面）；纯项式组装（exact 供给项）；全 Qed 闭合；    *)
(*   前缀 upreq_exp/upreq_real_zero 全库防撞已核（grep 零命中）；   *)
(*   既有文件零改，仅新建本件。                                    *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.

(* ============================================================ *)
(* 件 1：Real 层 0 ≠ 1（五步链步骤 2 的矛盾底座，库内缺位补建）      *)
(*   工艺：real_eq 取 ε := 1 得逐项分离 QltT |0−1| 1，逐点计算      *)
(*   化归 Id false true（Qlt_bool 1 1 = false），索引不可统一消去。 *)
(* ============================================================ *)
Lemma upreq_real_zero_ne_one : Not (real_eq real_zero real_one).
Proof.
  intro H.
  destruct (H 1%Q qltT_0_1) as [N HN].
  assert (Hline : QltT (Qabs (projT1 real_zero N - projT1 real_one N)) 1%Q).
  { apply HN. apply NatLe_lift. apply Nat.le_refl. }
  assert (Hft : Id false true).
  { exact Hline. }
  (* Id false true 空型消去：依值 match，真支（索引 true）返回型化为
     Empty_set，id_refl 支（索引 false）返回型化为 unit 供 tt。 *)
  exact (match Hft in Id _ y
         return (match y with true => Empty_set | false => unit end) with
         | id_refl => tt
         end).
Qed.

(* ============================================================ *)
(* 件 2（五步链步骤 1）：单位元 eˣ·e⁻ˣ == 1                         *)
(*   eˣ·e⁻ˣ == e^{x+(−x)}（exp_neg_plus 反向）== e^{−0}（参数        *)
(*   real_eq 运输：plus_opp → opp_compat → cauchy_real_exp_wd）     *)
(*   == 1（real_exp_neg_zero）。                                   *)
(* ============================================================ *)
Lemma upreq_exp_neg_unit : forall x : Real,
  real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one.
Proof.
  intro x.
  apply (real_eq_trans
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_exp_neg (real_plus x (real_opp x)))
           real_one).
  - exact (real_eq_sym _ _ (real_exp_neg_plus x (real_opp x))).
  - apply (real_eq_trans
           (real_exp_neg (real_plus x (real_opp x)))
           (real_exp_neg real_zero)
           real_one).
    + unfold real_exp_neg.
      apply cauchy_real_exp_wd.
      apply RealSetoid.real_eq_opp_compat.
      exact (real_plus_opp x).
    + exact real_exp_neg_zero.
Qed.

(* ============================================================ *)
(* 件 3（五步链步骤 2）：eˣ ≠ 0（乘法逆元存在性推论）                *)
(*   eˣ==0 ⟹ eˣ·e⁻ˣ == 0·e⁻ˣ == 0（eq_mult_compat + mult_comm      *)
(*   + mult_zero）⟹ 0 == 1（件 1）⟹ Empty_set 消去。               *)
(* ============================================================ *)
Lemma upreq_exp_neg_ne_zero : forall x : Real,
  Not (real_eq (real_exp_neg x) real_zero).
Proof.
  intro x. intro Hzero.
  assert (Hstep : real_eq
           (real_mult (real_exp_neg x) (real_exp_neg (real_opp x)))
           (real_mult real_zero (real_exp_neg (real_opp x))))
    by exact (RealSetoid.real_eq_mult_compat (real_exp_neg x) (real_exp_neg (real_opp x))
                                  real_zero (real_exp_neg (real_opp x))
                                  Hzero (real_eq_refl (real_exp_neg (real_opp x)))).
  assert (Hzl : real_eq (real_mult real_zero (real_exp_neg (real_opp x))) real_zero).
  { apply (real_eq_trans
             (real_mult real_zero (real_exp_neg (real_opp x)))
             (real_mult (real_exp_neg (real_opp x)) real_zero)
             real_zero).
    - exact (real_mult_comm real_zero (real_exp_neg (real_opp x))).
    - exact (real_mult_zero (real_exp_neg (real_opp x))). }
  assert (Hunit : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_one)
    by exact (upreq_exp_neg_unit x).
  assert (Hm0 : real_eq (real_mult (real_exp_neg x) (real_exp_neg (real_opp x))) real_zero)
    by exact (real_eq_trans _ _ _ Hstep Hzl).
  exact (upreq_real_zero_ne_one
           (real_eq_sym _ _ (real_eq_trans _ _ _ (real_eq_sym _ _ Hunit) Hm0))).
Qed.

(* ============================================================ *)
(* 件 4（目标定理，主结果）：0 < eˣ 对全部实数 x                     *)
(*   real_exp_neg (real_opp x) = cauchy_real_exp (real_opp          *)
(*   (real_opp x)) = eˣ；库内 real_exp_neg_pos 于 real_opp x 一词    *)
(*   实例化——即 exp_neg_pos 接口字段的 Real 层实例化验证：其 ε 见证   *)
(*   由 S03 幂级数战役构造（ε := 1/(2C)，构造性 sigT 形态）。        *)
(* ============================================================ *)
Theorem upreq_exp_pos : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof. intro x. exact (real_exp_neg_pos (real_opp x)). Qed.

(* ============================================================ *)
(* 件 5（五步链步骤 5 的 Or 消解形态）：目标定理的 Or 编码演绎        *)
(*   real_le real_zero eˣ = Or (real_lt real_zero eˣ) (real_eq       *)
(*   real_zero eˣ)（S02:460 编码展开）；左支由级数 ε-见证直供（件 4  *)
(*   同源），右支 0==eˣ 经件 3 归谬得 Empty_set、任意 Set 目标消去    *)
(*   ——destruct-Or + 右支归谬的标准构造性结构，纯项式组装。          *)
(* ============================================================ *)
Theorem upreq_exp_pos_or_destruct : forall x : Real,
  real_lt real_zero (real_exp_neg (real_opp x)).
Proof.
  intro x.
  assert (Hle : real_le real_zero (real_exp_neg (real_opp x))).
  { apply inl. exact (real_exp_neg_pos (real_opp x)). }
  destruct Hle as [Hpos | Heq].
  - exact Hpos.
  - destruct (upreq_exp_neg_ne_zero (real_opp x) (real_eq_sym _ _ Heq)).
Qed.

Print Assumptions upreq_real_zero_ne_one.
Print Assumptions upreq_exp_neg_unit.
Print Assumptions upreq_exp_neg_ne_zero.
Print Assumptions upreq_exp_pos.
Print Assumptions upreq_exp_pos_or_destruct.
