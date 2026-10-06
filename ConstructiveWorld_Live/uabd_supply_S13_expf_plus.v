(* ==========================================================================
   uabd_supply_S13_expf_plus.v

   使命：BoundedSoftmax 型指数接口 expf 的加法同态槽供给。对任意增强实数
         接口 RI，具名见证 c1_expf RI := fun x => exp_neg (opp x)（递增指数）
         满足 expf (a + b) == expf a · expf b（Id 面）。

   依赖：S01_BaseRing（opp_plus 负号对加法分配、exp_neg_plus 指数加法同态、
         id_trans／id_cong 组合子）；abl_c1_lohi（c1_expf 见证定义）。

   对标：S13_NLiveAudit.v BoundedSoftmax 节 expf_plus 槽语句
         （forall a b, Id (expf (plus a b)) (mult (expf a) (expf b))
           @ expf := c1_expf 应用形）；
         abl_c1_lohi.v c1_expf_zero／c1_expf_pos／c1_expf_mono_lt 同族补全件。

   构造性：全件 Qed 真构造，零承认式语句、零经典逻辑、零公理；
         语句面全 Set 层（Id 为 Set 值等词，零 Prop 泄露）。

   编译配方：coqc -q -native-compiler no -Q <主vo树> "" -Q . ""
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import abl_c1_lohi.

Existing Instance RI_base.

Theorem uabd_supply_S13_expf_plus : forall (RI : RealInterfaceEnhanced) (a b : R),
  Id (c1_expf RI (plus a b)) (mult (c1_expf RI a) (c1_expf RI b)).
Proof.
  intros RI a b.
  (* 负号先对加法分配，再由 exp_neg 的加法同态闭合。 *)
  apply (id_trans (id_cong exp_neg (opp_plus a b))).
  exact (exp_neg_plus (opp a) (opp b)).
Qed.

Print Assumptions uabd_supply_S13_expf_plus.
