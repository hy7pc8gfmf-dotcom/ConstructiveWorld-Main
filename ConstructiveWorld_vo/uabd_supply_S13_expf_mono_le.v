(* ==========================================================================
   uabd_supply_S13_expf_mono_le.v

   使命：BoundedSoftmax 型指数接口 expf 的非严格单调槽供给。对任意增强实数
         接口 RI，具名见证 c1_expf RI := fun x => exp_neg (opp x)（递增指数）
         满足 a ≤ b ⟹ expf a ≤ expf b（弱序面）。

   依赖：S01_BaseRing（opp_le_compat 弱序负号反变、exp_neg_le_decr 递减、
         id 组合子）；abl_c1_lohi（c1_expf 见证定义）。

   对标：S13_NLiveAudit.v BoundedSoftmax 节 expf_mono_le 槽语句
         （forall a b, le a b -> le (expf a) (expf b) @ expf := c1_expf 应用形）；
         abl_c1_lohi.v c1_expf_mono_lt（严格对偶，经 opp_lt_compat +
         exp_neg_decr 双反变合成）的弱序对偶补全件。

   构造性：全件 Qed 真构造，零承认式语句、零经典逻辑、零公理；
         语句面全 Set 层（le 为 Set 值弱序，零 Prop 泄露）。
         非平凡性注记：结论由双反变方向合成承载（负号反变换向一次、
         递减函数再换向一次，两次反变合成正变），与在库严格对偶件同族，
         弱序面此前缺位。

   编译配方：coqc -q -native-compiler no -Q <主vo树> "" -Q . ""
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import abl_c1_lohi.

Existing Instance RI_base.

Theorem uabd_supply_S13_expf_mono_le : forall (RI : RealInterfaceEnhanced) (a b : R),
  le a b -> le (c1_expf RI a) (c1_expf RI b).
Proof.
  intros RI a b H.
  (* a ≤ b 经负号反变得 -b ≤ -a，再经 exp_neg 递减得 exp_neg(-a) ≤ exp_neg(-b)。 *)
  exact (exp_neg_le_decr (opp b) (opp a) (opp_le_compat a b H)).
Qed.

Print Assumptions uabd_supply_S13_expf_mono_le.
