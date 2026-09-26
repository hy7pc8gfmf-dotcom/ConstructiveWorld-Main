(* ==========================================================================)
   UpAblP2FeedSumLe.v — 序面原生折叠传输、拼接可加性与折叠和的三角不等式（单余量 ε 形）
   使命: p2fl_lsum_app（拼接可加性）、p2fl_le_transport（序面两世界运输）、p2fl_abs_split_eps（主件）三全局件，加 Section 实例三件与 bool 具体层两件。
   依赖: CW_ConstructiveWorld_219、S02_CauchyComplete、S03_QExp、S07_RealSetoidExpLog、S08_RealMainlineDPO、UpReqSumD、UpAblEps66Sum、UpAblP2FeedMix、UpAblLeEqCompat、List、Extraction。
   对标: 有限和三角不等式（|Σ f| ≤ Σ|f| + ε）与求和算子序传输。
   构造性: 零承认词面、纯构造性（零经典逻辑）；全 Set 层语句；全 Qed 闭合；末段 Print Assumptions 审计全 Closed。
   编译配方: coqc 9.1 直调，cpu_guard 包裹（-LoadLimit 85 -CoreN 2）；编译输出经 -o 写临时目录，树内 .vo 一律不动。
   ========================================================================== *)

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
Require Import UpReqSumD.
Require Import UpAblEps66Sum.
Require Import UpAblP2FeedMix.
Require Import UpAblLeEqCompat.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 拼接可加性 p2fl_lsum_app：表拼接情形下原生折叠的可加性（对 l1 归纳  *)
(*   新证——三角和主件的拼接前提，折叠核心体的等词见证面）                 *)
(* ============================================================ *)
Lemma p2fl_lsum_app :
  forall (X : Set) (l1 l2 : list X) (f : X -> Real),
    real_eq (real_list_sum X f (l1 ++ l2))
            (real_plus (real_list_sum X f l1) (real_list_sum X f l2)).
Proof.
  intros X l1.
  induction l1 as [| w t IH]; intros l2 f; simpl.
  - (* 情形 l1 = []：化简后待证 real_plus real_zero (Σ l2) 与 Σ l2 等词——左零经 real_plus_comm、右零经 real_plus_zero 两步合成。 *)
    apply real_eq_sym.
    apply (real_eq_trans (real_plus real_zero (real_list_sum X f l2))
                         (real_plus (real_list_sum X f l2) real_zero)
                         (real_list_sum X f l2)).
    + apply (real_plus_comm real_zero (real_list_sum X f l2)).
    + apply (real_plus_zero (real_list_sum X f l2)).
  - (* 归纳步：由 l1 到 w :: t——头项 f w 与自身等词（real_eq_refl），尾部由归纳假设 IH，经 real_eq_plus_compat，再由 real_plus_assoc 重排结合。 *)
    apply (real_eq_trans
             (real_plus (f w) (real_list_sum X f (t ++ l2)))
             (real_plus (f w)
                        (real_plus (real_list_sum X f t)
                                   (real_list_sum X f l2)))
             (real_plus (real_plus (f w) (real_list_sum X f t))
                        (real_list_sum X f l2))).
    + apply (RealSetoid.real_eq_plus_compat (f w)
               (real_list_sum X f (t ++ l2)) (f w)
               (real_plus (real_list_sum X f t) (real_list_sum X f l2))).
      * apply real_eq_refl.
      * exact (IH l2 f).
    + apply (real_plus_assoc (f w) (real_list_sum X f t)
                             (real_list_sum X f l2)).
Qed.

(* ============================================================ *)
(* §2 序面两世界运输 p2fl_le_transport：e66s_sumf（sumd 折叠）世界        *)
(*   上的序关系经折叠桥 p2f_lsum_bridge（逐点等词）与兼容件               *)
(*   lec_le_eq_eq 运到原生折叠世界                                        *)
(* ============================================================ *)
Theorem p2fl_le_transport :
  forall (X : Set) (l : list X) (f g : X -> Real),
    real_le (e66s_sumf X l f) (e66s_sumf X l g) ->
    real_le (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X l f g Hle.
  exact (lec_le_eq_eq (e66s_sumf X l f) (e66s_sumf X l g)
                      (real_list_sum X f l) (real_list_sum X g l)
                      Hle
                      (p2f_lsum_bridge X l f)
                      (p2f_lsum_bridge X l g)).
Qed.

(* ============================================================ *)
(* §3 三角和主件 p2fl_abs_split_eps：拼接和的绝对值不超过两段绝对值和     *)
(*   加单份余量 ε（ε > 0）。三步合成：S07 逐项三角                        *)
(*   real_abs_triangle_le_eps 给 |Σ段一 + Σ段二| 的序，面一可加性经       *)
(*   real_abs_eq_compat 把和的绝对值换成拼接和的绝对值，最后由            *)
(*   lec_le_eq_eq 沿等词双侧收尾。                                        *)
(* ============================================================ *)
Theorem p2fl_abs_split_eps :
  forall (X : Set) (l1 l2 : list X) (f : X -> Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_abs (real_list_sum X f (l1 ++ l2)))
            (real_plus (real_plus (real_abs (real_list_sum X f l1))
                                  (real_abs (real_list_sum X f l2))) eps).
Proof.
  intros X l1 l2 f eps Heps.
  apply (lec_le_eq_eq
           (real_abs (real_plus (real_list_sum X f l1)
                                (real_list_sum X f l2)))
           (real_plus (real_plus (real_abs (real_list_sum X f l1))
                                 (real_abs (real_list_sum X f l2))) eps)
           (real_abs (real_list_sum X f (l1 ++ l2)))
           (real_plus (real_plus (real_abs (real_list_sum X f l1))
                                 (real_abs (real_list_sum X f l2))) eps)).
  - exact (real_abs_triangle_le_eps (real_list_sum X f l1)
                                    (real_list_sum X f l2) eps Heps).
  - exact (real_abs_eq_compat
             (real_plus (real_list_sum X f l1) (real_list_sum X f l2))
             (real_list_sum X f (l1 ++ l2))
             (real_eq_sym (real_list_sum X f (l1 ++ l2))
                          (real_plus (real_list_sum X f l1)
                                     (real_list_sum X f l2))
                          (p2fl_lsum_app X l1 l2 f))).
  - exact (real_eq_refl
             (real_plus (real_plus (real_abs (real_list_sum X f l1))
                                   (real_abs (real_list_sum X f l2))) eps)).
Qed.

(* ============================================================ *)
(* §4 Section P2FeedSumLe：载体（S0, enum0）上的实例三件                 *)
(* ============================================================ *)
Section P2FeedSumLe.

Context (S0 : Set).
Context (enum0 : list S0).

(* 求和算子实例 p2fl_sumf：原生折叠 real_list_sum 特化到（S0, enum0） *)
Definition p2fl_sumf (f : S0 -> Real) : Real := real_list_sum S0 f enum0.

(** p2fl_le·序面折叠传输：逐点序不降⟹p2fl_sumf 和序不降——经              *)
(*   e66s_real_sum_over_S_le、p2f_lsum_bridge 与 lec_le_eq_eq 三步。       *)
Theorem p2fl_le :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (p2fl_sumf f) (p2fl_sumf g).
Proof.
  intros f g H.
  apply (lec_le_eq_eq (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)
                      (p2fl_sumf f) (p2fl_sumf g)).
  - exact (e66s_real_sum_over_S_le S0 enum0 f g H).
  - exact (p2f_lsum_bridge S0 enum0 f).
  - exact (p2f_lsum_bridge S0 enum0 g).
Qed.

(** p2fl_le_native_direct·对照件：同一语句形由 S08 原生件                 *)
(*   real_list_sum_le 一步给出（对照注记见头部）。                        *)
Theorem p2fl_le_native_direct :
  forall (f g : S0 -> Real),
    (forall s : S0, real_le (f s) (g s)) ->
    real_le (p2fl_sumf f) (p2fl_sumf g).
Proof.
  intros f g H.
  exact (real_list_sum_le S0 f g enum0 H).
Qed.

(** p2fl_abs_split_slot：三角和主件 p2fl_abs_split_eps 的（S0, enum0）实例。 *)
Theorem p2fl_abs_split_slot :
  forall (l1 l2 : list S0) (f : S0 -> Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_abs (real_list_sum S0 f (l1 ++ l2)))
            (real_plus (real_plus (real_abs (real_list_sum S0 f l1))
                                  (real_abs (real_list_sum S0 f l2))) eps).
Proof.
  intros l1 l2 f eps Heps.
  exact (p2fl_abs_split_eps S0 l1 l2 f eps Heps).
Qed.

End P2FeedSumLe.

(* ============================================================ *)
(* §5 bool 具体层两件（柯西实数层 fully concrete：枚举                    *)
(*   e66s_flag_enum＝true::false::nil，零残留抽象参数）                   *)
(* ============================================================ *)

(** p2fl_flag_le：p2fl_le 的 bool 载体实例（逐点序不降⟹折叠序不降）。 *)
Theorem p2fl_flag_le :
  forall (f g : bool -> Real),
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (real_list_sum bool f e66s_flag_enum)
            (real_list_sum bool g e66s_flag_enum).
Proof.
  intros f g H.
  exact (p2fl_le bool e66s_flag_enum f g H).
Qed.

(** p2fl_flag_abs_split_eps：三角和主件的 bool 载体实例——                *)
(*   |Σ_flag f| ≤ |f true| + |f false| + ε：在 [true]/[false] 双段拆分    *)
(*   上实例化；单点折叠化简（Σ[w] f 与 f w 的等词）与枚举表展开           *)
(*   （e66s_flag_enum 定义性等于 true::false::nil）由等词件合成。          *)
Theorem p2fl_flag_abs_split_eps :
  forall (f : bool -> Real) (eps : Real),
    real_lt real_zero eps ->
    real_le (real_abs (real_list_sum bool f e66s_flag_enum))
            (real_plus (real_plus (real_abs (f true))
                                  (real_abs (f false))) eps).
Proof.
  intros f eps Heps.
  apply (lec_le_eq_eq
           (real_abs (real_list_sum bool f ([true] ++ [false])))
           (real_plus (real_plus (real_abs (real_list_sum bool f [true]))
                                 (real_abs (real_list_sum bool f [false]))) eps)
           (real_abs (real_list_sum bool f e66s_flag_enum))
           (real_plus (real_plus (real_abs (f true))
                                 (real_abs (f false))) eps)).
  - exact (p2fl_abs_split_eps bool [true] [false] f eps Heps).
  - (* [true] ++ [false] 与 e66s_flag_enum 经 app 计算与枚举表展开同为 true::false::nil，由 real_eq_refl。 *)
    exact (real_abs_eq_compat (real_list_sum bool f ([true] ++ [false]))
                              (real_list_sum bool f e66s_flag_enum)
                              (real_eq_refl
                                 (real_list_sum bool f e66s_flag_enum))).
  - (* 单点折叠：Σ[true] f 与 f true、Σ[false] f 与 f false 分别等词（real_plus_zero）——经 real_eq_plus_compat 合成。 *)
    apply (RealSetoid.real_eq_plus_compat
             (real_plus (real_abs (real_list_sum bool f [true]))
                        (real_abs (real_list_sum bool f [false])))
             eps
             (real_plus (real_abs (f true)) (real_abs (f false)))
             eps).
    + apply (RealSetoid.real_eq_plus_compat
               (real_abs (real_list_sum bool f [true]))
               (real_abs (real_list_sum bool f [false]))
               (real_abs (f true))
               (real_abs (f false))).
      * exact (real_abs_eq_compat (real_list_sum bool f [true]) (f true)
                 (real_plus_zero (f true))).
      * exact (real_abs_eq_compat (real_list_sum bool f [false]) (f false)
                 (real_plus_zero (f false))).
    + apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 应全部 Closed（零外部未证假设）       *)
(* ============================================================ *)
Print Assumptions p2fl_lsum_app.
Print Assumptions p2fl_le_transport.
Print Assumptions p2fl_abs_split_eps.
Print Assumptions p2fl_le.
Print Assumptions p2fl_le_native_direct.
Print Assumptions p2fl_abs_split_slot.
Print Assumptions p2fl_flag_le.
Print Assumptions p2fl_flag_abs_split_eps.

(* ============================================================ *)
(* 提取区：可计算件 p2fl_sumf 与 p2fl_lsum_app（拼接可加性等词见证，      *)
(*   真折叠链）提取；序谓词与三角桥面件以假设审计替代提取。               *)
(*                                                                      *)
(* ============================================================ *)
Set Extraction Output Directory "_tf1_g3out".
Separate Extraction p2fl_sumf p2fl_lsum_app.
