(* ============================================================ *)
(* AbsLeIdReal53.v — T40 消融50 席位T53B（批次 E-STAGING-T53B）   *)
(* Real 具体层兑现独立稿件                                        *)
(*                                                               *)
(* 使命：CYB6 的 AbsLeId.v 已在抽象层（DecidableOrder 桥）消解    *)
(*   abs_ge_zero_id_cc 槽（S06_DiffSamplingGibbs:4035）。本席把   *)
(*   其 Real 具体层兑现路径 ali_real_abs_ge_zero_id 扩展为独立    *)
(*   四关稿件：消费 fa53 系基座件与 S07 Real 层三件               *)
(*   （real_lt_plus_translate S07:6086 + real_abs_pos_req         *)
(*   S07:7289 + real_abs_zero_req S07:7266），零依赖 AbsLeId.v    *)
(*   （减少依赖面；AbsLeId.v 不在被消费集）。                     *)
(*                                                               *)
(* 侦查对照（防重复施工）：                                       *)
(*   - CYB6 AbsLeId.v 件5 ali_real_abs_ge_zero_id：同路径首次     *)
(*     施工（lt 支 real_abs_pos_req；eq 支 real_eq_abs_compat     *)
(*     + real_abs_zero_req + sym/trans 链）。本件独立重铸主件，   *)
(*     另交付三件 CYB6 未有的扩展：                               *)
(*     (a) r53_real_abs_lt_translate——strict 平移形：消费         *)
(*         real_lt_plus_translate（左加法平移 S07:6086）把        *)
(*         0<a 搬到 b+0 < b+|a|，右端点经 ≈ 运河换装 |a|          *)
(*         （RealSetoid.real_lt_id_r S07:456）；                  *)
(*     (b) r53_real_abs_eq_translate——eq 支平移形：消费           *)
(*         real_abs_zero_req + real_eq_plus_compat（S07:219，     *)
(*         参序 (a,c)/(b,d) 配对）；                              *)
(*     (c) r53_real_abs_plus_translate——le 版 Or 编码打包         *)
(*         （real_le = Or real_lt real_eq，S02:469，Set 层 Or     *)
(*         S01:67-68=A+B，inl/inr 构造）；及 r53_real_abs_mult_id *)
(*         Real 层乘位打包（镜像 CYB6 抽象层 ali_abs_id_mult_l，  *)
(*         RealSetoid.real_eq_mult_compat S07:282）。             *)
(*   - DPOLip 卡判词“库内 abs 引理全 eps/strict 型无 le 版        *)
(*     abs==self”——le 版真引理族仅 fa53（抽象）/AbsLeId（抽象     *)
(*     +本路径），本件 Real 层平移形为净新增，零占用。            *)
(*                                                               *)
(* 纪律：语句面全 Set 层（Or/Not 用 S01:67-68 Set 层定义）；       *)
(*   零 Prop 泄露；无 Axiom/Admitted/Parameter/Conjecture/Abort； *)
(*   非平凡真证（三分/平移/≈运河/配对 compat 四段字段链）；       *)
(*   fa53_compat_abs 只 Require 消费零改；原树零改。              *)
(*   前缀 r53_ 全库防撞已 grep 核（消融50/vo_901/Live/build       *)
(*   零命中，20260918 06:04 实测）。                              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import fa53_compat_abs.

(* ============ 第一层：抽象桥（fa53 系基座件直配，槽语句同面） ==== *)
(* 与 fa53 同款上下文；@ 全显消费（DO 为证明体消费的节参，CYB6    *)
(* 定谳：省略写法赌类型类解析不如显式喂）。                        *)
Section R53AbsBridge.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Theorem r53_abs_ge_zero_id : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI DO a Ha).
Qed.

End R53AbsBridge.

(* ============ 第二层：Real 具体层兑现（本件主体） ================ *)
(* 柯西实数层（S02 Real := sigT (fun u : Qseq => cauchy u)）；     *)
(* real_le = Or real_lt real_eq（S02:469）两支分决。               *)
(* Require 置于抽象节之后（CYB6 坑谱：具体层名隔离，防遮蔽接口     *)
(* 投影名解析）。real_abs 定义在 S03_QExp:6510——语句面用到，       *)
(* 须显式 Require（Require Import 不传递）。                       *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.

(* ---- 主件：CYB6 路径独立重铸（real_abs_pos_req +               *)
(*      real_abs_zero_req 双消费） ---- *)
Theorem r53_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - (* 0 < a：严格版逐点件直给（S07:7289） *)
    exact (real_abs_pos_req a Hlt).
  - (* 0 == a：|a| ≈ |0| ≈ 0 ≈ a（compat + zero_req + sym/trans 链；
       real_eq_trans 三显参 _ MID _ 留洞式，Q18C 卡定式） *)
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + apply (real_eq_trans _ real_zero).
      * exact real_abs_zero_req.
      * exact Heq.
Qed.

(* ---- 扩展件1（消费 real_lt_plus_translate S07:6086）：strict 平移形
   real_lt_plus_translate 只做左加法平移（b+c < b+d），此处先把
   0 < a 搬成 b+0 < b+a，再用 ≈ 运河把右端点 b+a 换装 b+|a|
   （|a| ≈ a 来自主件 lt 支；real_lt_id_r S07:456：req y z ->
   lt x y -> lt x z）。 ---- *)
Theorem r53_real_abs_lt_translate :
  forall a b : Real, real_lt real_zero a ->
    real_lt (real_plus b real_zero) (real_plus b (real_abs a)).
Proof.
  intros a b Hlt.
  apply (RealSetoid.real_lt_id_r (real_plus b real_zero) (real_plus b a)
                                 (real_plus b (real_abs a))).
  - apply (RealSetoid.real_eq_plus_compat b a b (real_abs a)).
    + apply real_eq_refl.
    + apply real_eq_sym.
      exact (r53_real_abs_ge_zero_id a (inl Hlt)).
  - exact (real_lt_plus_translate b real_zero a Hlt).
Qed.

(* ---- 扩展件2（消费 real_abs_zero_req）：eq 支平移形 ----
   0 == a 时 b+0 ≈ b+|a|：sym 逆行后 |a| ≈ |0|（compat，a≈0 由
   Heq sym 供给）+ |0| ≈ 0（zero_req）单层 trans 即达；加法位经
   real_eq_plus_compat（参序 (a,c)/(b,d) 配对，交接文档 §4.2.15
   口诀）。坑记：嵌套 trans 尾段中项被 zero_req 定死为 real_zero
   后 Heq 对不上（首跑实撞，见本席经验卡）。 ---- *)
Theorem r53_real_abs_eq_translate :
  forall a b : Real, real_eq real_zero a ->
    real_eq (real_plus b real_zero) (real_plus b (real_abs a)).
Proof.
  intros a b Heq.
  apply (RealSetoid.real_eq_plus_compat b real_zero b (real_abs a)).
  - apply real_eq_refl.
  - apply real_eq_sym.
    apply (real_eq_trans _ (real_abs real_zero)).
    + apply (RealSetoid.real_eq_abs_compat a real_zero).
      apply real_eq_sym.
      exact Heq.
    + exact real_abs_zero_req.
Qed.

(* ---- 扩展件3：le 版 Or 编码打包（S02:469 两支分决到件1/件2） ----
   语句面 Or = S01:67-68 Set 层（A + B），inl/inr 构造。 ---- *)
Theorem r53_real_abs_plus_translate :
  forall a b : Real, real_le real_zero a ->
    Or (real_lt (real_plus b real_zero) (real_plus b (real_abs a)))
       (real_eq (real_plus b real_zero) (real_plus b (real_abs a))).
Proof.
  intros a b H.
  unfold real_le in H.
  destruct H as [Hlt | Heq].
  - exact (inl (r53_real_abs_lt_translate a b Hlt)).
  - exact (inr (r53_real_abs_eq_translate a b Heq)).
Qed.

(* ---- 扩展件4：Real 层乘位打包（镜像 CYB6 抽象层 ali_abs_id_mult_l）
   real_eq_mult_compat（S07:282）参序 (a,c)/(b,d) 配对：
   |a| ≈ a 喂 Hac 槽，b ≈ b 喂 Hbd 槽。 ---- *)
Theorem r53_real_abs_mult_id :
  forall a b : Real, real_le real_zero a ->
    real_eq (real_mult (real_abs a) b) (real_mult a b).
Proof.
  intros a b H.
  apply (RealSetoid.real_eq_mult_compat (real_abs a) b a b).
  - exact (r53_real_abs_ge_zero_id a H).
  - apply real_eq_refl.
Qed.

(* ---- G1 内嵌自检段（文件内显式 PA 声明，min-pa≥1） ---- *)
Print Assumptions r53_abs_ge_zero_id.
Print Assumptions r53_real_abs_ge_zero_id.
Print Assumptions r53_real_abs_lt_translate.
Print Assumptions r53_real_abs_eq_translate.
Print Assumptions r53_real_abs_plus_translate.
Print Assumptions r53_real_abs_mult_id.
