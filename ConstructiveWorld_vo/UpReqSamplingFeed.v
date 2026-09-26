(* ============================================================
   UpReqSamplingFeed —— 使命行：本件形式化 UpReqSampling 两节求和诚实接口与
(*   配套前提位的实现化给出：sumf 取 csm_sumf 折叠读法（载体 Real），        *)
(*   求和四件与 sum_eq_list/bs_swap/lt_plus 混合保序经 ConcMixSelFeed       *)
(*   cms 系已证件以显式实参供给；abs 非负恒等就地复演；sum_pos 以 sigT      *)
(*   非空见证加列表头证书供给；温度/Delta 取单位元实例、z 取 ±1 对称对、    *)
(*   enum 取二元表给 Set 层 sigT 见证。                                      *)
(* 依赖：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、                *)
(*   UpReqConcSoftmax、UpReqSampling、ConcMixSelFeed。                      *)
(* 对标：mathlib 有限和线性/单调/次可加性质的构造性 Set 层对应物。          *)
(* 构造性注记：Set 层承载，零承认；供给定理全由库内已证件显式实参或         *)
(*   结构化分情形构造，可提取面零 Prop 残留；plain 形逐项三角               *)
(*   （abs_sum_le_h 同语句位）属墙族永久位，本件只供逐 eps 邻接形，         *)
(*   不越界硬证。                                                            *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)

From Stdlib Require Import List.
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
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import ConcMixSelFeed.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ################ 块一：ReqUContraction 节求和接口实现化读法 ############ *)
(* 对应 UpReqSampling Section ReqUContraction 的求和诚实接口五假设位：      *)
(*   四件折叠面直供，另供同节配套三件 sum_swap_cc/abs 非负恒等/lt_plus      *)
(*   混合保序。abs_sum_le_h 同语句位不在供给面：plain 形对混合号函数        *)
(*   无构造性路线（UpReqConcSoftmax 头注与 ConcMixSelFeed 同判），          *)
(*   真前提保留；逐 eps 邻接形见块二 usrq_bs_abs_sum_le_eps_supply          *)
(*   （同一实现化读法下语句面相同）。                                        *)

Section UsrqUContractionResolved.

Variable S : Set.
Variable en : list S.

Let sumf : (S -> Real) -> Real := csm_sumf S en.

(* sum_ext 位（UpReqSampling :132 同语句）：逐点 req 前提经 cms_sum_ext *)
Theorem usrq_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S en f g H).
Qed.

(* sum_linear 位（:134 同语句）：单位数乘线性经 cms_sum_linear *)
Theorem usrq_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S en a f).
Qed.

(* sum_add 位（:137 同语句）：逐点和可加性经 cms_sum_add *)
Theorem usrq_sum_add_supply : forall f g : S -> Real,
  req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S en f g).
Qed.

(* sum_le 位（:140 同语句）：逐点 le 保序经 cms_sum_le *)
Theorem usrq_sum_le_supply : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_le S en f g H).
Qed.

(* sum_swap_cc 位（:159 同语句）：双重列表和换序，cms_bs_swap 泛型直引 *)
Theorem usrq_sum_swap_cc_supply : forall f : S -> S -> Real,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Proof.
  intros f.
  exact (cms_bs_swap S en f).
Qed.

(* abs 非负恒等位（:162 同语句）：正支取 real_abs_pos_req，相等支经        *)
(*   abs 对相等的相容与 abs zero = zero 归零（实数层已证件就地复演）       *)
Theorem usrq_abs_ge_zero_req_supply : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Qed.

(* lt_plus 混合保序位（:163 同语句）：严格支 real_lt_plus_compat、        *)
(*   相等支经加法相容与交换重排（cms_lt_plus_compat_lt_le_time 同款分情形） *)
Theorem usrq_lt_plus_compat_lt_le_h_supply :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (cms_lt_plus_compat_lt_le_time a b c d Hab Hcd).
Qed.

End UsrqUContractionResolved.

(* ################ 块二：ReqBoundedSoftmax 节求和接口实现化读法 ########## *)
(* 对应 UpReqSampling Section ReqBoundedSoftmax 的求和诚实接口六假设位：    *)
(*   五件折叠面直供；sum_pos 以 sigT 非空见证为显式读法义务（折叠机在      *)
(*   空表上无逐点正性和），列表分情形后头见证经 sumd_list_sum_pos_cons；   *)
(*   abs_sum_le_h 同语句位真前提保留，另供逐 eps 邻接形。                   *)

Section UsrqBoundedSoftmaxResolved.

Variable S : Set.
Variable en : list S.

Let sumf : (S -> Real) -> Real := csm_sumf S en.

(* sum_ext 位（UpReqSampling :734 同语句） *)
Theorem usrq_bs_sum_ext_supply : forall f g : S -> Real,
  (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_ext S en f g H).
Qed.

(* sum_linear 位（:736 同语句） *)
Theorem usrq_bs_sum_linear_supply : forall (a : Real) (f : S -> Real),
  req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Proof.
  intros a f.
  exact (cms_sum_linear S en a f).
Qed.

(* sum_add 位（:741 同语句） *)
Theorem usrq_bs_sum_add_supply : forall f g : S -> Real,
  req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Proof.
  intros f g.
  exact (cms_sum_add S en f g).
Qed.

(* sum_le 位（:744 同语句） *)
Theorem usrq_bs_sum_le_supply : forall f g : S -> Real,
  (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Proof.
  intros f g H.
  exact (cms_sum_le S en f g H).
Qed.

(* sum_pos 位（:739 同语句＋非空读法义务显式化）：非空性取 sigT InT        *)
(*   见证（Set 层承载），枚举分情形，空表支由 InT 空归纳型构造性关闭，     *)
(*   非空支取头见证加 sumd_list_sum_pos_cons 的头尾分解                     *)
Theorem usrq_bs_sum_pos_supply : forall (f : S -> Real),
  sigT (fun t : S => InT t en) ->
  (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Proof.
  intros f Hne H.
  destruct Hne as [x Hx].
  destruct en as [| y t].
  - exact (match Hx with end).
  - exact (sumd_list_sum_pos_cons S f y t H).
Qed.

(* abs_sum_le_h 位（:746 同语句）保留注记之后的逐 eps 邻接形供给：        *)
(*   |Σf| ≤ Σ|f| + eps（0 < eps），经 csm_abs_sum_le_eps 直引               *)
Theorem usrq_bs_abs_sum_le_eps_supply : forall (f : S -> Real) (eps : Real),
  lt zero eps ->
  le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).
Proof.
  intros f eps Heps.
  exact (csm_abs_sum_le_eps S en f eps Heps).
Qed.

(* bs_swap 位（:761 同语句）：双重列表和换序，cms_bs_swap 泛型直引 *)
Theorem usrq_bs_swap_supply : forall f : S -> S -> Real,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Proof.
  intros f.
  exact (cms_bs_swap S en f).
Qed.

(* bs_abs 位（:764 同语句）：块一 abs 非负恒等同款证明链就地复演 *)
Theorem usrq_bs_abs_supply : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Qed.

(* bs_lpc 位（:765 同语句）：lt/le 混合加法严格保序经 cms 系分情形件 *)
Theorem usrq_bs_lpc_supply :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (cms_lt_plus_compat_lt_le_time a b c d Hab Hcd).
Qed.

(* sum_eq_list 位（:774 同语句）：折叠和与枚举列表和一致，cms_sum_eq_list *)
Theorem usrq_sum_eq_list_supply : forall g : S -> Real,
  req (sumf g) (rsq_bs_list_sum S g en).
Proof.
  intro g.
  exact (cms_sum_eq_list S en g).
Qed.

End UsrqBoundedSoftmaxResolved.

(* ################ 块三：世界数据参数位单位元实例读法 #################### *)
(* temp/Delta/z/enum 四参数位在 bool 二点非退化实例下的证书：温度与         *)
(*   Delta 取单位元 one（cf2_temp_pos@UpReqConcFin2:100 同款方向，          *)
(*   one_pos 直出）；z 取 ±1 对称对，内界证书 rsq_bs_opp_lt（本件已         *)
(*   Require 的 UpReqSampling 自有件）；enum 取二元表给 sigT InT 见证       *)
(*   （Set 层重述，对应 :751 等词否定形的构造性替代读法）。                 *)

Definition usrq_temp : Real := one.

Theorem usrq_temp_pos_supply : lt zero usrq_temp.
Proof.
  unfold usrq_temp.
  exact one_pos.
Qed.

Definition usrq_Delta : Real := one.

Theorem usrq_Delta_pos_supply : lt zero usrq_Delta.
Proof.
  unfold usrq_Delta.
  exact one_pos.
Qed.

Definition usrq_z (s s' : bool) : Real := if s then one else opp one.

Theorem usrq_z_lb_supply : forall s s' : bool, le (opp usrq_Delta) (usrq_z s s').
Proof.
  intros s s'. destruct s as [ | ].
  - exact (inl (@rsq_bs_opp_lt Real RealEnhancedReal usrq_Delta usrq_Delta_pos_supply)).
  - exact (le_refl (opp usrq_Delta)).
Qed.

Theorem usrq_z_ub_supply : forall s s' : bool, le (usrq_z s s') usrq_Delta.
Proof.
  intros s s'. destruct s as [ | ].
  - exact (le_refl usrq_Delta).
  - exact (inl (@rsq_bs_opp_lt Real RealEnhancedReal usrq_Delta usrq_Delta_pos_supply)).
Qed.

Definition usrq_enum : list bool := [true; false].

Theorem usrq_enum_nonempty_supply : sigT (fun t : bool => InT t usrq_enum).
Proof.
  exact (existT _ true (InT_here true (false :: nil))).
Qed.

(* ============ 供给定理假设面核验（预期全 Closed） ==================== *)

Print Assumptions usrq_sum_ext_supply.
Print Assumptions usrq_sum_linear_supply.
Print Assumptions usrq_sum_add_supply.
Print Assumptions usrq_sum_le_supply.
Print Assumptions usrq_sum_swap_cc_supply.
Print Assumptions usrq_abs_ge_zero_req_supply.
Print Assumptions usrq_lt_plus_compat_lt_le_h_supply.
Print Assumptions usrq_bs_sum_ext_supply.
Print Assumptions usrq_bs_sum_linear_supply.
Print Assumptions usrq_bs_sum_add_supply.
Print Assumptions usrq_bs_sum_le_supply.
Print Assumptions usrq_bs_sum_pos_supply.
Print Assumptions usrq_bs_abs_sum_le_eps_supply.
Print Assumptions usrq_bs_swap_supply.
Print Assumptions usrq_bs_abs_supply.
Print Assumptions usrq_bs_lpc_supply.
Print Assumptions usrq_sum_eq_list_supply.
Print Assumptions usrq_temp_pos_supply.
Print Assumptions usrq_Delta_pos_supply.
Print Assumptions usrq_z_lb_supply.
Print Assumptions usrq_z_ub_supply.
Print Assumptions usrq_enum_nonempty_supply.
