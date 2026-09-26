(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* SqrtfCauchyDischarge.v                                        *)
(*                                                               *)
(* 目的：消解宿主 SqrtfCauchy.v 四个节参数假设中可消解的两位，      *)
(*       宿主本体零改动，以同语句替换件 + 接口补装段给出。          *)
(* 主件：sfcx_abs_le_plus_eps_real——|t| ≤ t + eps（0 ≤ t、         *)
(*       0 < eps，real_le 素颜面）；接口投影形                     *)
(*       sfcx_abs_le_plus_eps_slot。sfcx_metric_abs_real——         *)
(*       metric a b 与 real_abs (real_plus a (real_opp b)) 定义性   *)
(*       重合，real_eq_refl 一步；接口投影形 sfcx_metric_abs_slot。  *)
(*       接口补装：ReqMetricAbs mixin Class + RealEnhancedReal      *)
(*       实例 ReqMetricAbsReal。                                   *)
(* 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、               *)
(*       S07_RealSetoidExpLog、UpReqAlgebra、CW_ConstructiveWorld_219； *)
(*       Stdlib Extraction。                                       *)
(* 备注（逐位判定）：                                              *)
(*   假设位1 sfc_square_nonneg（宿主 :76 Hypothesis）＝结构性永久    *)
(*     （与 SqWall 定义性相同，构造性不可供给）——本件不消解，仅     *)
(*     尾附 §C 判定标注段（注释形式，非证题）。                     *)
(*   假设位2 sfc_metric_abs（宿主 :78 Variable）＝可消解（零成本）   *)
(*     ——接口 RealInterfaceEnhancedSetoid（S07:7906）无 metric_abs  *)
(*     字段（仅 metric_sym/metric_pos/metric_zero/metric_triangle）， *)
(*     但实例层定义性重合：RealEnhancedReal（S07:8557）metric :=     *)
(*     real_metric、S03:6518 real_metric x y := real_abs            *)
(*     (real_plus x (real_opp y))、UpReqAlgebra:58 req_minus a b :=  *)
(*     plus a (opp b)（δ 透明）⟹ delta 展开逐字相等，req_refl        *)
(*     （real_eq_refl）一步完成。接口缺位按 UpReqSLM:133             *)
(*     ReqNonnegPlain 样板立 ReqMetricAbs mixin Class +              *)
(*     RealEnhancedReal 实例补装段（本件 §A2）。                     *)
(*   假设位3 sfc_arch_decay（宿主 :80，S07:2762 real_arch 种子）      *)
(*     ＝可消解但最重，划归独立后续件，本件不涉及。                  *)
(*   假设位4 sfc_abs_le_plus_eps（宿主 :83）＝可消解（最轻，首推）    *)
(*     ——RealEnhancedReal 字段 le := real_le ＝ Or (real_lt)         *)
(*     (real_eq)（S02:460，全库唯一实例）；前提位 Or 是情形数据，     *)
(*     构造性分解无碍：lt 支 real_abs_pos_req（S07:7280）+ eq 支     *)
(*     real_abs_zero_req（S07:7257）。证见本件 §A1。                 *)
(*   命名：前缀 sfcx_（全库实扫零撞名）。                           *)
(*   纪律：纯构造性零承认；语句全 Set 层                            *)
(*   （real_eq/real_lt/real_le/sigT）；零 Prop 泄露；全 Qed；         *)
(*   宿主与只读树零改。                                             *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import UpReqAlgebra.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §A1 假设位4 消解（最轻首推）：|t| ≤ t + eps（0 ≤ t, 0 < eps）      *)
(*   宿主位语句逐字（R:=Real 实例 RealEnhancedReal，素颜面）：          *)
(*   le zero t 在实例 δ 展开＝Or (real_lt real_zero t) (real_eq …)，    *)
(*   前提位情形数据构造性分解——lt 支 |t|==t、eq 支 |t|==0。             *)
(* ============================================================ *)
Theorem sfcx_abs_le_plus_eps_real :
  forall t : Real, real_le real_zero t ->
  forall eps : Real, real_lt real_zero eps ->
  real_le (real_abs t) (real_plus t eps).
Proof.
  intros t Hle eps Heps.
  unfold real_le in Hle.
  destruct Hle as [Hlt | Heq].
  - (* lt 支：0 < t ⟹ |t| == t（real_abs_pos_req, S07:7280）；
       0 < eps 经加性平移（real_lt_plus_translate, S07:6077）得
       t+0 < t+eps，右零形换形得 t < t+eps，abs 换头后
       lt_le_iff（RealSetoid.real_lt_le_iff_req，S07:105）取 Or 左支完成。 *)
    assert (Habs : real_eq (real_abs t) t)
      by exact (real_abs_pos_req t Hlt).
    assert (Htz : real_lt (real_plus t real_zero) (real_plus t eps))
      by exact (real_lt_plus_translate t real_zero eps Heps).
    assert (Hte : real_lt t (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l t (real_plus t real_zero)
                  (real_plus t eps)
                  (real_eq_sym (real_plus t real_zero) t (real_plus_zero t))
                  Htz).
    assert (Habslt : real_lt (real_abs t) (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l (real_abs t) t
                  (real_plus t eps) Habs Hte).
    apply (RealSetoid.real_lt_le_iff_req (real_abs t) (real_plus t eps)).
    left. exact Habslt.
  - (* eq 支：t == 0 ⟹ |t| == 0（real_eq_abs_compat + real_abs_zero_req,
       S07:7257）；t+eps 归拢到 eps（real_eq_plus_compat + plus_comm/
       plus_zero），0 < eps 换形 0 < t+eps 后 lt_id_l 一步完成。 *)
    assert (Hsym : real_eq t real_zero)
      by exact (real_eq_sym real_zero t Heq).
    assert (Habs0 : real_eq (real_abs t) real_zero)
      by exact (real_eq_trans (real_abs t) (real_abs real_zero) real_zero
                  (RealSetoid.real_eq_abs_compat t real_zero Hsym)
                  real_abs_zero_req).
    assert (Hpt : real_eq (real_plus t eps) (real_plus real_zero eps))
      by exact (RealSetoid.real_eq_plus_compat t eps real_zero eps Hsym
                  (real_eq_refl eps)).
    assert (Hpt2 : real_eq (real_plus t eps) eps)
      by exact (real_eq_trans (real_plus t eps)
                  (real_plus real_zero eps) eps Hpt
                  (real_eq_trans (real_plus real_zero eps)
                     (real_plus eps real_zero) eps
                     (real_plus_comm real_zero eps) (real_plus_zero eps))).
    assert (Hlt1 : real_lt real_zero (real_plus t eps))
      by exact (RealSetoid.real_lt_id_r real_zero eps (real_plus t eps)
                  (real_eq_sym (real_plus t eps) eps Hpt2) Heps).
    assert (Habslt : real_lt (real_abs t) (real_plus t eps))
      by exact (RealSetoid.real_lt_id_l (real_abs t) real_zero
                  (real_plus t eps) Habs0 Hlt1).
    apply (RealSetoid.real_lt_le_iff_req (real_abs t) (real_plus t eps)).
    left. exact Habslt.
Qed.

(* 假设位4 替换桥（宿主位语句逐字，接口投影面；使用位 SqrtfCauchy.v:1143）
   ——素颜面到接口面的转换只走实例 delta/iota（同 swc_interface_slot_face
   式，exact 一行）。替换：sfc_abs_le_plus_eps 参数位 ← 本件。 *)
Theorem sfcx_abs_le_plus_eps_slot :
  forall t : Real,
  @le Real RealEnhancedReal (@zero Real RealEnhancedReal) t ->
  forall eps : Real,
  @lt Real RealEnhancedReal (@zero Real RealEnhancedReal) eps ->
  @le Real RealEnhancedReal (@abs Real RealEnhancedReal t)
      (@plus Real RealEnhancedReal t eps).
Proof. exact sfcx_abs_le_plus_eps_real. Qed.

(* ============================================================ *)
(* §A2 假设位2 消解（零成本）+ 接口补装段                              *)
(*   metric a b ＝ real_metric a b ＝ real_abs (real_plus a (real_opp b)) *)
(*   （S03:6518）；req_minus a b ＝ plus a (opp b)（UpReqAlgebra:58 δ   *)
(*   透明）；两者定义性重合 ⟹ real_eq_refl 一步。                       *)
(* ============================================================ *)
Theorem sfcx_metric_abs_real : forall a b : Real,
  real_eq (real_metric a b) (real_abs (real_plus a (real_opp b))).
Proof.
  intros a b.
  exact (real_eq_refl (real_metric a b)).
Qed.

(* 假设位2 替换桥（宿主位语句逐字，使用位 SqrtfCauchy.v:1137）。 *)
Theorem sfcx_metric_abs_slot :
  forall a b : Real,
  @req Real RealEnhancedReal (@metric Real RealEnhancedReal a b)
       (@abs Real RealEnhancedReal
             (@req_minus Real RealEnhancedReal a b)).
Proof. exact sfcx_metric_abs_real. Qed.

(* 接口缺位补装：ReqMetricAbs mixin Class（样板 UpReqSLM:133
   ReqNonnegPlain 同形：R 显参 + 基接口 {RIS} 隐参）+ RealEnhancedReal
   实例补装。下游泛型文件可 {RIS} 上挂本 mixin 使用 req_metric_abs 位。 *)
Class ReqMetricAbs (R : Set) {RIS : RealInterfaceEnhancedSetoid R} := {
  req_metric_abs : forall a b : R, req (metric a b) (abs (req_minus a b))
}.

Instance ReqMetricAbsReal : @ReqMetricAbs Real RealEnhancedReal := {
  req_metric_abs := sfcx_metric_abs_slot
}.

(* ============================================================ *)
(* §A3 假设位5 消解（1 < 2 严格档）：宿主假设位5 Hlt_one_two        *)
(*   （lt one sfc_two，sfc_two δ 展开 = real_plus real_one            *)
(*   real_one）实例面逐字。0 < 1（one_pos）经 real_lt_plus_translate  *)
(*   单侧平移 +one，plus_zero 换形收 1 < 1+1（SCFIX ）。      *)
(* ============================================================ *)
Theorem sfcx_lt_one_two_slot :
  @lt Real RealEnhancedReal (@one Real RealEnhancedReal)
      (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
             (@one Real RealEnhancedReal)).
Proof.
  apply (RealSetoid.real_lt_id_l
           (@one Real RealEnhancedReal)
           (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
                  (@zero Real RealEnhancedReal))
           (@plus Real RealEnhancedReal (@one Real RealEnhancedReal)
                  (@one Real RealEnhancedReal))
           (real_eq_sym (@plus Real RealEnhancedReal
                                (@one Real RealEnhancedReal)
                                (@zero Real RealEnhancedReal))
                        (@one Real RealEnhancedReal)
                        (real_plus_zero (@one Real RealEnhancedReal)))).
  exact (real_lt_plus_translate (@one Real RealEnhancedReal)
           (@zero Real RealEnhancedReal) (@one Real RealEnhancedReal)
           (@one_pos Real RealEnhancedReal)).
Qed.

(* ============================================================ *)
(* 自证面：提取检验（KLWallClosed.v:447 / SqWallCorrMark.v:210        *)
(* 同式，Obj.magic 计数应为 0）+ 假设闭包审计。两主件证明体全走        *)
(* real_* 素颜顶层函数链，不触 RealEnhancedReal 类实例封装常量，       *)
(* 预判 Obj.magic=0。                                                *)
(* ============================================================ *)
Extraction "sfcx_G3.ml" sfcx_abs_le_plus_eps_real sfcx_metric_abs_real.

Print Assumptions sfcx_abs_le_plus_eps_real.
Print Assumptions sfcx_abs_le_plus_eps_slot.
Print Assumptions sfcx_metric_abs_real.
Print Assumptions sfcx_metric_abs_slot.
Print Assumptions sfcx_lt_one_two_slot.

(* ============================================================ *)
(* §C 假设位1 永久判定标注段（非证题，注释形式）                         *)
(* ============================================================ *)
(* 假设位1 sfc_square_nonneg（SqrtfCauchy.v:76 Hypothesis）：
      forall t : R, le zero (mult t t)
   【结构性永久判定】本位面在 Real 实例（RealEnhancedReal，S07:8557，
      le := real_le = Or (real_lt, real_eq)，S02:460）下与 SqWall
      （UpReqLpoEquiv:230）定义性相同——「全称平方非负」的
      Or 编码数据形即逐实数符号判定器，构造性不可供给；假设位1 永久，
      不消解、不降级、保持诚实前提位（与假设位4 的「前提位 Or 可消」
      分水岭：假设位4 的 Or 是单点前提情形数据，假设位1 的 Or 藏在全称
      供给面）。五指针（均已实扫）：
   ① UpReqLpoEquiv.v（机器判定）：SqWall:230 / rLPO:234 /
      lpn_forward:249 / lpn_backward:342 / lpn_equivalence:429。
      同位升参形 sfc_square_nonneg 登记，使用位 :560/:827；
      供给方式 = swc_lpn_backward_slot（rLPO 证书 → 位面，一行替换）。
   ③ S02:802（同源注记）：real_square_not_negative（:804）自注
      「信息性 real_le 的全称形式不可证（需判定 a 的符号）」。
   ④ UpRealLeB.v:424 real_square_nonneg_B：B 形（real_le_b，Bishop
      逐 eps）可达替代，全称可证、Closed（假设审计见 UpRealLeB:814）——
      同数学内容换编码后可全称供给（SqWallCorrMark 重述件
      swc_sq_wall_b_reachable / swc_sq_ge_a_b_form 可达链）。
   ⑤ UpReqSLM.v:133 ReqNonnegPlain：plain 非负假设位组
      （abs_nonneg_plain / metric_pos_plain）的 mixin 诚实前置先例——
      假设位1 同判据下不内证、只保留为显式前提。 *)
(* ============================================================ *)
(* 本件内容清单：                                                     *)
(*   假设位4 sfcx_abs_le_plus_eps_real + 替换桥 sfcx_abs_le_plus_eps_slot *)
(*   假设位2 sfcx_metric_abs_real + 替换桥 sfcx_metric_abs_slot          *)
(*   接口补装 ReqMetricAbs mixin Class + ReqMetricAbsReal 实例           *)
(*   假设位3 未动（独立后续件，S07:2762 real_arch 种子已登记）           *)
(*   假设位1 未动（本 §C 判定标注段）                                    *)
(*   假设位5 sfcx_lt_one_two_slot（1 < 2 严格档，§A3，SCFIX ）   *)
(* ============================================================ *)
