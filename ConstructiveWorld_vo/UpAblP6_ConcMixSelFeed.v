(* ==========================================================================)
   UpAblP6_ConcMixSelFeed.v — 单点载体上的 conc/mix/select 接口实例件
   使命: uacms_ 系十九件：单位枚举世界（en_unit/en_bool/mix_f）上求和接口（sumf_unit_eval/norm、sum_ext/linear/add/le_unit）、lt_plus 选择（lt_plus_sel_unit/lt_plus_time_point）、bs_swap 与 sum_eq_list 的 bool 实例闭合。
   依赖: CW_ConstructiveWorld_219、UpReqSumD、UpReqConcSoftmax、UpReqSampling、UpReqConcMixSel、UpReqConcB1、ConcMixSelFeed；Stdlib List。
   对标: 求和/混合/选择接口的单点具体实例层（接口实例化方法论）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import ConcMixSelFeed.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ §0 具体数据（枚举与被折函数构造） ======================= *)

(* 单点枚举：S0 := unit、en := [tt]——最小非空枚举。 *)
Definition uacms_en_unit : list unit := [tt].

(* 二点枚举：S0 := bool、en := [true; false]——最小多点枚举， *)
(* 供 bs_swap/sum_eq_list 实例非退化（单点会退化平凡）。 *)
Definition uacms_en_bool : list bool := [true; false].

(* 双变量非对称被折函数：true 位出 one、false 位出 zero—— *)
(* 双折两臂（f s s' 与 f s' s）非可转换，防 swap 实例退化为自反平凡。 *)
Definition uacms_mix_f (b1 b2 : bool) : Real := if b1 then one else zero.

(* ============ §1 求值伴随引理组（具体值实算；如实注记） ================= *)

(* 单点折叠和定义性展开＝plus one zero（csm_sumf 以 sumd_list_sum 为折叠   *)
(* 体，沿具体数据点 iota/beta 透明展开）。 *)
Theorem uacms_sumf_unit_eval :
  Id (csm_sumf unit uacms_en_unit (fun _ : unit => one)) (plus one zero).
Proof.
  exact id_refl.
Qed.

(* 具体折叠和经代数场归一：req (plus one zero) one（plus_zero 字段）       *)
(* 在展开后的具体和上实例化消解——单点枚举有限和的规范值。 *)
Theorem uacms_sumf_unit_norm :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => one)) one.
Proof.
  exact (plus_zero one).
Qed.

(* 二点折叠和真算＝plus one (plus one zero)。 *)
Theorem uacms_sumf_bool_eval :
  Id (csm_sumf bool uacms_en_bool (fun _ : bool => one))
     (plus one (plus one zero)).
Proof.
  exact id_refl.
Qed.

(* 两折叠之一的具体求值实证：rsq_bs_list_sum 逐构造子同形展开至同一        *)
(* 字面和——cms_sum_eq_list 两折叠相等的两臂在此自证。 *)
Theorem uacms_rsq_bool_eval :
  Id (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool)
     (plus one (plus one zero)).
Proof.
  exact id_refl.
Qed.

(* ============ §2 序关系证书的具体构造 ================================== *)

(* le zero one 具体证书：lt_le_iff 左支注入 one_pos（单位点正性）。 *)
Theorem uacms_zero_le_one : le zero one.
Proof.
  exact (lt_le_iff zero one (inl one_pos)).
Qed.

(* ============ §3 csm_sumf 折叠四性质实例（外延/线性/可加/单调） ========== *)

(* cms_sum_ext：逐点 req 前提（one 与 plus one zero 经 req_sym+plus_zero   *)
(* 合成）给出，结论为两折叠和的外延 req 实例——两臂展开后非可转换           *)
(* （plus one zero 对 plus (plus one zero) zero），经该引理实例化消解。 *)
Theorem uacms_sum_ext_unit_one :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => one))
      (csm_sumf unit uacms_en_unit (fun _ : unit => plus one zero)).
Proof.
  exact (cms_sum_ext unit uacms_en_unit
           (fun _ : unit => one) (fun _ : unit => plus one zero)
           (fun _ : unit => req_sym (plus one zero) one (plus_zero one))).
Qed.

(* cms_sum_linear：a := one 单位点数乘线性在该点实例化——结论两臂           *)
(* （折叠（mult one（常一））对 mult one（折叠（常一）））非平凡。         *)
Theorem uacms_sum_linear_unit :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => mult one one))
      (mult one (csm_sumf unit uacms_en_unit (fun _ : unit => one))).
Proof.
  exact (cms_sum_linear unit uacms_en_unit one (fun _ : unit => one)).
Qed.

(* cms_sum_add：常一自加的可加性在该点实例化——LHS 展开＝                  *)
(* plus (plus one one) zero、RHS＝plus (plus one zero) (plus one zero)。 *)
Theorem uacms_sum_add_unit :
  req (csm_sumf unit uacms_en_unit (fun _ : unit => plus one one))
      (plus (csm_sumf unit uacms_en_unit (fun _ : unit => one))
            (csm_sumf unit uacms_en_unit (fun _ : unit => one))).
Proof.
  exact (cms_sum_add unit uacms_en_unit
           (fun _ : unit => plus one one) (fun _ : unit => one)).
Qed.

(* cms_sum_le：零和 ≤ 单和（逐点 le zero one 证书常值）在该点实例化——      *)
(* 具体有限和单调性实例。                                               *)
Theorem uacms_sum_le_unit :
  le (csm_sumf unit uacms_en_unit (fun _ : unit => zero))
     (csm_sumf unit uacms_en_unit (fun _ : unit => one)).
Proof.
  exact (cms_sum_le unit uacms_en_unit
           (fun _ : unit => zero) (fun _ : unit => one)
           (fun _ : unit => uacms_zero_le_one)).
Qed.

(* ============ §4 lt_plus 两节同型实例（sel 节与 time 节各一具体点） ====== *)

(* cms_lt_plus_compat_lt_le_sel（CmkMixSelect 节）：a b c d := zero one    *)
(* zero zero，证书 one_pos × le_refl zero——lt (plus zero zero) (plus one zero)。 *)
Theorem uacms_lt_plus_sel_unit :
  lt (plus zero zero) (plus one zero).
Proof.
  exact (cms_lt_plus_compat_lt_le_sel zero one zero zero
           one_pos (le_refl zero)).
Qed.

(* cms_lt_plus_compat_lt_le_time（CmkMixTime 节同型）：异点 c d := one     *)
(* one（le_refl one）——具体点 lt (plus zero one) (plus one one)，与上一    *)
(* 实例取不同点，以证两节同型结论各自可达。 *)
Theorem uacms_lt_plus_time_point :
  lt (plus zero one) (plus one one).
Proof.
  exact (cms_lt_plus_compat_lt_le_time zero one one one
           one_pos (le_refl one)).
Qed.

(* ============ §5 双换位与两折叠相等实例（bool 二点枚举） ================ *)

(* cms_bs_swap：bool 二点枚举＋uacms_mix_f 双变量非对称函数——双折两臂      *)
(* 项不可转换，经 cb1_swap_lists 泛型双折归纳引理实例化消解。 *)
Theorem uacms_bs_swap_bool :
  req (csm_sumf bool uacms_en_bool
         (fun s : bool => csm_sumf bool uacms_en_bool
            (fun s' : bool => uacms_mix_f s s')))
      (csm_sumf bool uacms_en_bool
         (fun s' : bool => csm_sumf bool uacms_en_bool
            (fun s : bool => uacms_mix_f s s'))).
Proof.
  exact (cms_bs_swap bool uacms_en_bool uacms_mix_f).
Qed.

(* cms_sum_eq_list：bool 二点枚举常一函数——csm_sumf 折叠和与              *)
(* rsq_bs_list_sum 折叠和的 req 桥接在该点实例化（§1 求值伴随引理已示两臂  *)
(* 同归 plus one (plus one zero)）。 *)
Theorem uacms_sum_eq_list_bool :
  req (csm_sumf bool uacms_en_bool (fun _ : bool => one))
      (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool).
Proof.
  exact (cms_sum_eq_list bool uacms_en_bool (fun _ : bool => one)).
Qed.

(* cms_fold_req_list_sum：两折叠的适配引理在具体列表上直接应用——两折叠    *)
(* 逐构造子同形（nil 支同归 zero、cons 支同 plus 头尾折）在 bool 二点列实证。 *)
Theorem uacms_fold_shim_bool :
  req (sumd_list_sum bool (fun _ : bool => one) uacms_en_bool)
      (rsq_bs_list_sum bool (fun _ : bool => one) uacms_en_bool).
Proof.
  exact (cms_fold_req_list_sum bool (fun _ : bool => one) uacms_en_bool).
Qed.

(* ============ §6 伴随引理实例（abs 与 lt_plus 的具体点） ================ *)

(* cms_bs_abs：req (abs one) one 在单位点实例化消解（前提＝具体证书        *)
(* uacms_zero_le_one）。 *)
Theorem uacms_bs_abs_one : req (abs one) one.
Proof.
  exact (cms_bs_abs one uacms_zero_le_one).
Qed.

(* cms_bs_lpc：与 cms_lt_plus_compat_lt_le_sel 同型（UpReqConcB1 头注在案）， *)
(* 伴生引理实例可达性实证。 *)
Theorem uacms_bs_lpc_unit :
  lt (plus zero zero) (plus one zero).
Proof.
  exact (cms_bs_lpc zero one zero zero one_pos (le_refl zero)).
Qed.

(* ============ 收尾核验（Print Assumptions 逐件 Closed） ================ *)

Print Assumptions uacms_sumf_unit_eval.
Print Assumptions uacms_sumf_unit_norm.
Print Assumptions uacms_sumf_bool_eval.
Print Assumptions uacms_rsq_bool_eval.
Print Assumptions uacms_zero_le_one.
Print Assumptions uacms_sum_ext_unit_one.
Print Assumptions uacms_sum_linear_unit.
Print Assumptions uacms_sum_add_unit.
Print Assumptions uacms_sum_le_unit.
Print Assumptions uacms_lt_plus_sel_unit.
Print Assumptions uacms_lt_plus_time_point.
Print Assumptions uacms_bs_swap_bool.
Print Assumptions uacms_sum_eq_list_bool.
Print Assumptions uacms_fold_shim_bool.
Print Assumptions uacms_bs_abs_one.
Print Assumptions uacms_bs_lpc_unit.
