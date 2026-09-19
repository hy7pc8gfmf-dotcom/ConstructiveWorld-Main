(* ===================================================================== *)
(* SumDCarrierFeed.v — E-STAGING-CZC12 / T62 §3-P1 sumd 改喂总件            *)
(* A 类零引用槽（T62 表 A#2–16）一稿收编：sumd 载体改喂消解宣言               *)
(*                                                                       *)
(* 依据（消融50/T62-零引用47枚triage.md §1 判词 + §3-P1 方案）：A 类槽全是   *)
(*   UpReqSumD / UpReqAlgebra 已证放电资产的「未回喂面」，改喂即闭、零新数学、  *)
(*   零涟漪（47 枚本就零跨文件消费，改喂不触任何活消费链）。                  *)
(*   计数勘误登记：任务书名义「14 槽」沿袭 T62 §3-P1「一件收 14 枚（A#2-16）」  *)
(*   旧账；A#2–16 逐名清单实测 15 槽，本件全收 15/15（下表 15 行）。          *)
(* 改喂式：宿主槽均为节内假设位（零跨文件消费者），本件以                    *)
(*   sumf := sumd_sumf S enum（UpReqSumD 具体有限和载体）逐槽直喂：              *)
(*   Theorem 语句 = 宿主原语句[sumf:=sumd_sumf S enum]，证明项 = sumd_ 一击件。 *)
(* 逐槽消解宣言（宿主坐标经 CZC12 逐一 grep 核行号实证）：                    *)
(*   1. UpReqPPOPlain::rpli_sum_le     (:392) ⟵ sumd_sum_le      （A#2）    *)
(*   2. UpReqPPOPlain::rpli_sum_ext    (:394) ⟵ sumd_sum_ext     （A#3）    *)
(*   3. UpReqPPOPlain::rpli_sum_add    (:396) ⟵ sumd_sum_add     （A#4）    *)
(*   4. UpReqPPOPlain::rpli_sum_linear (:399) ⟵ sumd_sum_linear  （A#5）    *)
(*   5. UpSigMigrate2::asum_ext        (:875) ⟵ sumd_sum_ext     （A#6）    *)
(*   6. UpSigMigrate2::asum_add        (:877) ⟵ sumd_sum_add     （A#7）    *)
(*   7. UpSigMigrate2::asum_linear     (:880) ⟵ sumd_sum_linear  （A#8）    *)
(*   8. UpSigMigrate2::b_mult_cancel   (:919) ⟵ req_mult_cancel_l            *)
(*        c:=zero 实例 + mult_zero 归一步（A#9，T62 §2 一击引用）             *)
(*   9. UpReqDist::psum_linear         (:3133)⟵ sumd_sum_linear  （A#10）   *)
(*  10. UpReqDist::psum_add            (:3134)⟵ sumd_sum_add     （A#11）   *)
(*  11. UpReqDist::sumf_pos            (:3438)⟵ sumd_sum_pos     （A#12）   *)
(*        诚实偏差登记：宿主语句无前提位，改喂形增补 enum 非空显式前提          *)
(*        Not (enum = nil)（T62 §4.5 风险位：漏带即 G2 假红；sumd_sum_pos      *)
(*        显式前提同形同阶，UpReqSampling 签名变化 7 口径）                   *)
(*  12. UpFirewallReq::ssum_add        (:81)  ⟵ sumd_sum_add     （A#13）   *)
(*  13. UpFirewallReq::ssum_le         (:87)  ⟵ sumd_sum_le      （A#14）   *)
(*  14. UpReqAlignRestA::ralt_sum_ext  (:70)  ⟵ sumd_sum_ext     （A#15）   *)
(*  15. UpReqAttnIter::sum_nonneg_h    (:111) ⟵ sumd_list_sum_nonneg         *)
(*        @ l:=enum 一步特化（A#16）；实测 nil 支由 le_refl 闭合，宿主语句      *)
(*        逐字同形改喂零偏差（非空见证仅 sumf_pos 数学必需，此槽无需）          *)
(* 形式注记：逐槽以 Definition 直喂形落盘（E370 T2② 配方：语句 Set 值，       *)
(*   Definition := 成品全参 与定理声明同义且提取透明——对接件提取产物字面       *)
(*   = 被喂件，零计算零魔法）；R/RIS 隐式位一律 @ 全参形（E397 定式）。        *)
(* CZJ14 签名漂移适配登记（T98，20260919）：alignb 波 UpReqSumD 节泛化后       *)
(*   sumd_sumf/sumd_list_sum 系显式 (S : Set) 首位（About 探针：               *)
(*   forall {R} {RIS} (S : Set) (enum : list S) (f ...)；sumd_list_sum_nonneg  *)
(*   不带 enum 位）。适配仅两处引用形：①语句面 22 处 sumd_sumf enum →          *)
(*   sumd_sumf S enum（补显式 S 实参，谓词/量词/前提面零改动）；②槽 15 喂形    *)
(*   @sumd_list_sum_nonneg R RIS S f enum Hnn（删多余 enum 位——新签名无该      *)
(*   形参）。十五槽结论面与宿主语句逐字同形，零改弱；喂件数学面零增补前提。      *)
(* 纪律：纯构造性；Set 层语句（req/le/lt 均 Set 值谓词，非空前提 Not 位与      *)
(*   基座签名变化 7 同形同阶）；纯项式组装零重写层；宿主原树零改；             *)
(*   全链可提取（Extraction 探针 Obj.magic 计数 = 0）。                       *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqPPOPlain.
Require Import UpSigMigrate2.
Require Import UpReqDist.
Require Import UpFirewallReq.
Require Import UpReqAlignRestA.
Require Import UpReqAttnIter.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* Section SumDCarrierFeed：宿主节参同位（R/RIS/S/enum 与各宿主      *)
(*   求和节同形；enum 即 sumd 具体载体）                            *)
(* ============================================================ *)
Section SumDCarrierFeed.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable enum : list S.

(* ---- 槽组一：UpReqPPOPlain ReqPPOPlainImprove（A#2–5） ---- *)

Definition feed_rpli_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_le R RIS S enum.

Definition feed_rpli_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext R RIS S enum.

Definition feed_rpli_sum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add R RIS S enum.

Definition feed_rpli_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear R RIS S enum.

(* ---- 槽组二：UpSigMigrate2 ReqAlignCore（A#6–9） ---- *)

Definition feed_asum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext R RIS S enum.

Definition feed_asum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add R RIS S enum.

Definition feed_asum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear R RIS S enum.

(* A#9：宿主槽 a>0 ∧ a·x==0 ⟹ x==0；放电 = req_mult_cancel_l（UpReqAlgebra
   :422，b:=x / c:=zero 实例）+ mult_zero 归一步（req_sym 运输）。 *)
Definition feed_b_mult_cancel :
  forall (a x : R), lt zero a -> req (mult a x) zero -> req x zero
  := fun (a x : R) (Ha : lt zero a) (Hax : req (mult a x) zero) =>
       @req_mult_cancel_l R RIS a x zero Ha
         (req_trans (mult a x) zero (mult a zero) Hax
            (req_sym (mult a zero) zero (mult_zero a))).

(* ---- 槽组三：UpReqDist ReqProbDist + ReqSoftmaxDual（A#10–12） ---- *)

Definition feed_psum_linear :
  forall (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f))
  := @sumd_sum_linear R RIS S enum.

Definition feed_psum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add R RIS S enum.

(* A#12：宿主语句无前提位（UpReqDist:3438），改喂形按 T62 §4.5 风险位
   增补 enum 非空显式前提 Not (enum = nil)（sumd_sum_pos 槽形同位直喂；
   空载体支和 = zero，lt zero zero 构造性不可证，故该前提为数学必需
   非装饰）。 *)
Definition feed_sumf_pos :
  forall f : S -> R,
    Not (enum = nil) -> (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f)
  := @sumd_sum_pos R RIS S enum.

(* ---- 槽组四：UpFirewallReq（A#13–14） + UpReqAlignRestA（A#15） ---- *)

Definition feed_ssum_add :
  forall f g : S -> R,
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g))
  := @sumd_sum_add R RIS S enum.

Definition feed_ssum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_le R RIS S enum.

Definition feed_ralt_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g)
  := @sumd_sum_ext R RIS S enum.

(* ---- 槽组五：UpReqAttnIter（A#16） ---- *)

(* 宿主语句逐字同形改喂零偏差：sumd_list_sum_nonneg @ l:=enum 一步特化；
   nil 支由 le_refl zero 闭合，非空前提数学不必需（头注宣言槽 15）。 *)
Definition feed_sum_nonneg_h :
  forall f : S -> R, (forall s : S, le zero (f s)) -> le zero (sumd_sumf S enum f)
  := fun (f : S -> R) (Hnn : forall s : S, le zero (f s)) =>
       @sumd_list_sum_nonneg R RIS S f enum Hnn.

End SumDCarrierFeed.

(* ---- G4 自检留痕：15 槽逐条假设闭包打印（应全 Closed） ---- *)

Print Assumptions feed_rpli_sum_le.
Print Assumptions feed_rpli_sum_ext.
Print Assumptions feed_rpli_sum_add.
Print Assumptions feed_rpli_sum_linear.
Print Assumptions feed_asum_ext.
Print Assumptions feed_asum_add.
Print Assumptions feed_asum_linear.
Print Assumptions feed_b_mult_cancel.
Print Assumptions feed_psum_linear.
Print Assumptions feed_psum_add.
Print Assumptions feed_sumf_pos.
Print Assumptions feed_ssum_add.
Print Assumptions feed_ssum_le.
Print Assumptions feed_ralt_sum_ext.
Print Assumptions feed_sum_nonneg_h.
