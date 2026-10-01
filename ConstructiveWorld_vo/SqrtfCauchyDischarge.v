(* ==========================================================================)
   SqrtfCauchyDischarge —— sfcx_abs_le_plus_eps_real / sfcx_abs_le_plus_eps_slot / sfcx_metric_abs_real 语句面；同域语句面
   使命：本件形式化sfcx_abs_le_plus_eps_real / sfcx_abs_le_plus_eps_slot / sfcx_metric_abs_real 语句面。
   本件并载：三件逐字语句重申件（req_entropy_temp_explicit / req_relative_entropy_temp_decomp / req；ibw_bnorm_opp（‖−a‖ == ‖a‖，Id 形）与 ibw_bnorm_opp_qeqt（QeqT 形）两件；qd_r_max_le_r_plain / qd_hsc_a3 / qd_b5b_hsc_general 语句面。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO
     S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpReqAlgebra,
     UpReqDist, UpReqTempEntropy, UpFirewallReq, UpReqBanachInstB, UpReqBanachInstReal, QArith.QArith, QArith.Qabs, Extraction,
     UpReqRDF, RMaxSwap。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 三件逐字语句重申件（req_entropy_temp_explicit / req_relative_entropy_temp_decomp / req ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section FrdTempDischarge：宿主 Section FirewallReq 见证面与          *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。见证每型     *)
(*   一个，宿主位/消解位同喂（重述桥判定见头注）。                      *)
(* ============================================================ *)
Section FrdTempDischarge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis frd_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis frd_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis frd_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis frd_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis frd_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis frd_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

(* ---- log 桥面（消解面需求；宿主同位 :98-102 同型） ---- *)
Hypothesis frd_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis frd_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis frd_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis frd_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis frd_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

(* ============================================================ *)
(* 重申件 A（槽A :122 逐字）：证 = 主路 :90 同名定理同见证实例。        *)
(* ============================================================ *)
Theorem frd_req_entropy_temp_explicit :
  forall (t : R) (Ht : lt zero t),
  req (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss Z_temp
                           frd_Z_temp_spec t Ht)
      (plus (mult (inv_pos t Ht)
                  (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos base_loss
                                        Z_temp frd_Z_temp_spec t Ht))
            (log (Z_temp t)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t Ht))).
Proof.
  intros t Ht.
  exact (UpReqTempEntropy.req_entropy_temp_explicit           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t Ht).
Qed.

(* ============================================================ *)
(* 重申件 B（槽B :128 逐字）：证 = 主路 :225，载体现身 fw_bt/fw_bt_pos， *)
(*   归一化证人 = fw_norm（fw_ 见证同喂）。                              *)
(* ============================================================ *)
Theorem frd_req_relative_entropy_temp_decomp :
  forall (t2 : R) (Ht2 : lt zero t2) (t1 : R) (Ht1 : lt zero t1),
  req (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss Z_temp
                            frd_Z_temp_spec t1 t2 Ht1 Ht2)
      (plus (plus (opp (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos
                                            base_loss Z_temp
                                            frd_Z_temp_spec t1 Ht1))
                  (mult (inv_pos t2 Ht2)
                        (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                              base_loss Z_temp
                                              frd_Z_temp_spec t1 Ht1)))
            (log (Z_temp t2)
                 (req_Z_temp_pos S sumf frd_sum_pos base_loss Z_temp
                                 frd_Z_temp_spec t2 Ht2))).
Proof.
  intros t2 Ht2 t1 Ht1.
  exact (UpReqTempEntropy.req_relative_entropy_temp_decomp           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t2 Ht2           (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss Z_temp                                 frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss                                    Z_temp frd_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_norm R RIS S sumf frd_sum_linear frd_sum_pos                                   base_loss Z_temp frd_Z_temp_spec t1 Ht1)).
Qed.

(* ============================================================ *)
(* 重申件 C（槽C :144 逐字）：证 = 主路 :1208（其证内依存 :225 两例 +   *)
(*   A_chain2 交叉，装配链完备）。                                       *)
(* ============================================================ *)
Theorem frd_req_temp_strict_ident2 :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (plus (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                   Z_temp frd_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2))
      (mult (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2))
            (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                       (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpReqTempEntropy.req_temp_strict_ident2           S sumf frd_sum_ext frd_sum_add frd_sum_linear frd_sum_pos           base_loss           frd_dist_log_inv_one_inv frd_dist_log_exp_neg           Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2).
Qed.

(* ============================================================ *)
(* 下游替换演示一：宿主件4（:187 依存位 :201/:203）零假设位可达——      *)
(*   槽A/槽B 参位实喂上面两重申件。                                     *)
(* ============================================================ *)
Theorem frd_recovery_entropy_gain :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (plus (mult (inv_pos t2 Ht2)
                  (req_minus (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                    base_loss Z_temp
                                                    frd_Z_temp_spec t2 Ht2)
                             (@UpFirewallReq.fw_et R RIS S sumf frd_sum_pos
                                                   base_loss Z_temp
                                                   frd_Z_temp_spec t1 Ht1)))
            (@UpFirewallReq.fw_kl R RIS S sumf frd_sum_pos base_loss
                                  Z_temp frd_Z_temp_spec t1 t2 Ht1 Ht2)).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           t1 t2 Ht1 Ht2).
Qed.

(* ============================================================ *)
(* 下游替换演示二：宿主件7 对偶形（:437 依存位 :458）——槽C 参位实喂     *)
(*   重申件 C（槽A/槽B 经件4 链式带入）。三槽替换至此全闭环。           *)
(* ============================================================ *)
Theorem frd_recovery_entropy_gain_alt :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  req (req_minus (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t2 Ht2)
                 (@UpFirewallReq.fw_h R RIS S sumf frd_sum_pos base_loss
                                      Z_temp frd_Z_temp_spec t1 Ht1))
      (req_minus (mult (inv_pos t1 Ht1)
                       (req_minus (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t2 Ht2)
                                  (@UpFirewallReq.fw_et R RIS S sumf
                                                        frd_sum_pos
                                                        base_loss Z_temp
                                                        frd_Z_temp_spec
                                                        t1 Ht1)))
                 (req_relative_entropy S sumf
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt R RIS S sumf frd_sum_pos base_loss
                                          Z_temp frd_Z_temp_spec t1 Ht1)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t2 Ht2)
                    (@UpFirewallReq.fw_bt_pos R RIS S sumf frd_sum_pos
                                             base_loss Z_temp
                                             frd_Z_temp_spec t1 Ht1))).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (UpFirewallReq.req_recovery_entropy_gain_alt           S sumf frd_sum_pos base_loss Z_temp frd_Z_temp_spec           frd_req_entropy_temp_explicit           frd_req_relative_entropy_temp_decomp           frd_req_temp_strict_ident2           t1 t2 Ht1 Ht2).
Qed.

End FrdTempDischarge.

(* ============================================================ *)
(* Print Assumptions 假设审计（五件全量；与 bbd/enp 文末同款惯例），     *)
(* 语句面零改动、零新增假设位。                                          *)
(* ============================================================ *)
Print Assumptions frd_req_entropy_temp_explicit.
Print Assumptions frd_req_relative_entropy_temp_decomp.
Print Assumptions frd_req_temp_strict_ident2.
Print Assumptions frd_recovery_entropy_gain.
Print Assumptions frd_recovery_entropy_gain_alt.

(* ============================ §2 ibw_bnorm_opp（‖−a‖ == ‖a‖，Id 形）与 ibw_bnorm_opp_qeqt（QeqT 形）两件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* 主件：bnorm_opp 位（E-载体面字段，UpReqBanachInstB.v:573 声明）   *)
(* 语句面逐字对齐冻结类字段 bxin_bnorm_opp 形（载体 bxib_E 面）。    *)
(* ============================================================ *)
Theorem ibw_bnorm_opp : forall a : bxib_E,
  Id (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. unfold bxib_bnorm.
  change (bxib_ev (bxib_eopp a)) with (Qopp (bxib_ev a)).
  exact (bxra_qabs_opp_norm (bxib_ev a)).
Qed.

(* QeqT 面（bxip_norm_wd_qeqt 同款派生形，供 QeqT 使用位） *)
Lemma ibw_bnorm_opp_qeqt : forall a : bxib_E,
  QeqT (bxib_bnorm (bxib_eopp a)) (bxib_bnorm a).
Proof.
  intro a. apply bxib_qeqT_of_id. apply ibw_bnorm_opp.
Qed.

(* ============================================================ *)
(* 既有供给指针（零新件；对应语句位的使用位直取下列已证引理）：       *)
(*   bplus_wd 位 := bxem_bplus_wd（EMult:242，逐位同语句）          *)
(*   bopp_wd  位 := bxem_bopp_wd （EMult:260，逐位同语句）          *)
(*   Q 面引理位 := bxra_qabs_opp_norm（InstReal，逐字同语句）。      *)
(* ============================================================ *)

(* ============================================================ *)
(* 假设审计：文末对全件执行 Print Assumptions。                     *)
(* ============================================================ *)
Print Assumptions ibw_bnorm_opp.
Print Assumptions ibw_bnorm_opp_qeqt.

From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
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

(* ============================ §3 qd_r_max_le_r_plain / qd_hsc_a3 / qd_b5b_hsc_general 语句面 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqRDF.
Require Import RMaxSwap.
From Stdlib Require Import QArith.QArith.
Import RealInterfaceEnhancedMod.
Open Scope Q_scope.

(* ===================================================================== *)
(* 一、A#1 qd_r_max_le_r_plain —— r_max 右参 plain 槽一般转发出口            *)
(* ===================================================================== *)
(*   槽坐标：UpReqPPOPlain.v:107 r_max_le_r_plain（节1 ReqPPOPlainObj）。  *)
(*   原留记：forall a b : R, le b (r_max a b) 零跨文件使用、零证明体，       *)
(*     req 层接口 r_max_le_r 仅逐 eps 形（「序无消去」，判例卡缺口）。      *)
(*   实例化消解路径：RMaxSwap.v 桥 B rms_le_r_of_ge（左参 plain 槽经 req_le_compat *)
(*     y 肢交换运输）实例化 Hge := @r_max_ge_plain R RIS RDP（UpReqRDF:117  *)
(*     左参 plain 槽）——一击 exact，零新数学。                              *)
(*   定理引用：qd_r_max_le_r_plain（本件），使用 rms_le_r_of_ge +          *)
(*     r_max_ge_plain；RMaxSwap 头注第 4 条预留槽兑现登记。                 *)
(* ===================================================================== *)
Theorem qd_r_max_le_r_plain :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (RDP : ReqDiffPlain R),
    (forall a b : R, req (r_max a b) (r_max b a)) ->
    forall a b : R, le b (r_max a b).
Proof.
  intros R RIS RDP rcomm a b.
  exact (@rms_le_r_of_ge R RIS rcomm (@r_max_ge_plain R RIS RDP) a b).
Qed.

(* ===================================================================== *)
(* 二、A#17 qd_hsc_a3 —— Hsc 槽连接（证后忘连接型滞后槽已连接）              *)
(* ===================================================================== *)
(*   槽坐标：S11_TP3B5.v:1598 HscA3（节 A3HscToF1 Hypothesis）。           *)
(*   原留记：real_eq (cauchy_real_sin arctan_one_real)                      *)
(*     (cauchy_real_cos arctan_one_real) 零跨文件使用——同文件 :11795        *)
(*     Lemma b5b_hsc_theorem（B5b 主链：b5b_hsc_main ∘ b5b_endpoint）已证   *)
(*   实例化消解路径：本件 Require S11_TP3B5 后 exact b5b_hsc_theorem 一击连接；    *)
(*     S11 原树只读，连接以转发件形态落在消融50。                            *)
(*   定理引用：qd_hsc_a3（本件），使用 S11_TP3B5.b5b_hsc_theorem（:11795）。 *)
(* ===================================================================== *)
Theorem qd_hsc_a3 :
  real_eq (cauchy_real_sin arctan_one_real)
          (cauchy_real_cos arctan_one_real).
Proof.
  exact (b5b_hsc_theorem b5dS_E_zero_on_unit).
Qed.

(* ===================================================================== *)
(* 三、A#18 qd_b5b_hsc_general —— 节假设泛化形平凡关闭                      *)
(* ===================================================================== *)
(*   槽坐标：S11_TP3B5.v:11070 b5b_hsc_theorem（节 B5bEndpointBridge      *)
(*     Hypothesis 泛化形）。                                                *)
(*   原留记：forall x Hx, real_lt real_zero x -> real_lt x (real_const 1)  *)
(*     -> real_eq (real_E x Hx) real_zero -> Hsc 结论——零跨文件使用。       *)
(*   实例化消解路径：结论与 x 无关（泛化形后件不依赖任何前提），已证 :11795 件     *)
(*     平凡关闭泛化形（fun x Hx _ _ _ => b5b_hsc_theorem 型）——数学必然的   *)
(*     平凡性（非降级：该槽语义即「有任一 Hsc 见证即弃前提」），零新数学。   *)
(*   定理引用：qd_b5b_hsc_general（本件），使用 S11_TP3B5.b5b_hsc_theorem    *)
(*     （:11795）；即 :11810 b5b_f1_closure' 之 Hsc 消去方向的一般化登记。   *)
(* ===================================================================== *)
Theorem qd_b5b_hsc_general :
  forall (x : Real) (Hx : cw_unit x),
    real_lt real_zero x -> real_lt x (real_const 1) ->
    real_eq (real_E x Hx) real_zero ->
    real_eq (cauchy_real_sin arctan_one_real)
            (cauchy_real_cos arctan_one_real).
Proof.
  intros x Hx Hlt0 Hlt1 HEz.
  exact (b5b_hsc_theorem b5dS_E_zero_on_unit).
Qed.

Print Assumptions qd_r_max_le_r_plain.
Print Assumptions qd_hsc_a3.
Print Assumptions qd_b5b_hsc_general.
