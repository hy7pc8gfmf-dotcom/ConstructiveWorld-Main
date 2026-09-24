(* ============================================================ *)
(* UpReqAttnMixTime.v —— 本件形式化有界 softmax 注意力核的混合时间性质：  *)
(*   对任意归一化行分布 mu nu 与正预算 budget，构造性给出迭代步数 k 使     *)
(*   TV(T^k mu, T^k nu) < budget（及 <= 版），几何率 1-delta* 的 k 次幂，  *)
(*   delta* = e^{-2Delta/T} = lo*lo（lo = e^{-Delta/T}，精确无损耗）。     *)
(*   主件：amt_attention_mixing_time / amt_attention_mixing_time_le。     *)
(*   另附接口证书位的就地消解定理（amtr_ 系：bs_swap 由 sum_eq_list 参数位    *)
(*   整体导出、bs_abs/bs_lpc 由实数层已证件供给）与 expf 五字段封装投影、  *)
(*   Fin 2 非退化实例读法、列表折叠实现化读法等具体层消解供给。           *)
(* 依赖：CW_ConstructiveWorld_219、AttnDoeblin、UpReqUMixSelect、         *)
(*   fa53_compat_abs、AbsLeId、P7BoundedSoftmaxDeep、UpReqConcFin2。      *)
(* 对标：mathlib Doeblin 条件混合时间定量界的构造性 Set 层对应物。        *)
(* 构造性注记：Set 层承载，零承认；主件 Defined 可提取；消解定理全由      *)
(*   库内已证件以显式实参供给，可提取面零 Prop 残留。                     *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹。                         *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import UpReqUMixSelect.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import P7BoundedSoftmaxDeep.
Require Import UpReqConcFin2.

Section BoundedSoftmaxMixTime.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let zero := @zero RI.
Let one := @one RI.
Let le := @le RI.
Let lt := @lt RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let sum_over_S := @sum_over_S RI SS SO.
Let tv := @tv_dist RI SS SO.

(* ---- BoundedSoftmax 接口全集（照 AttnDoeblin.v L453-485 逐一照抄） ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (Id enum nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).
Variable expf_mono_le : forall a b : R, le a b -> le (expf a) (expf b).
Variable bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> Id (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R, Id (sum_over_S g) (bs_list_sum g enum).

(* ---- 核实例（消解 bs_kernel 的 11 参重装） ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let omd := minus one delta_star.

Let amt_kernel : S -> S -> R :=
  bs_kernel enum enum_nonempty temp temp_pos Delta z z_lb expf expf_pos
            expf_mono_le sum_eq_list.

(* ================= B 档：消解件使用桥 ================= *)

(* δ* < 1（使用 bs_delta_star_lt_one，参量序照 _tat2_probe1 实测） *)
Lemma amt_ds_lt_one : lt delta_star one.
Proof.
  exact (bs_delta_star_lt_one temp temp_pos Delta Delta_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* 1 − δ* > 0（使用 u_omd_pos_next，lpc 参数位同位传入 bs_lpc） *)
Lemma amt_omd_pos : lt zero omd.
Proof.
  exact (u_omd_pos_next delta_star amt_ds_lt_one bs_lpc).
Qed.

(* TV₀ ≥ 0（使用 S06 tv_dist_nonneg 直连） *)
Lemma amt_tv_nonneg : forall mu nu : S -> R, le zero (tv mu nu).
Proof.
  intros mu nu. exact (tv_dist_nonneg mu nu).
Qed.

(* ================= A 档：自证胶水（退化端严格性） ================= *)

(* one = 1−δ*+δ*（五段 id 链） *)
Lemma amt_one_eq : Id one (plus (minus one delta_star) delta_star).
Proof.
  unfold minus.
  exact (id_sym (id_trans (id_sym (plus_assoc one (opp delta_star) delta_star))
    (id_trans (id_cong (fun w : R => plus one w)
      (id_trans (plus_comm (opp delta_star) delta_star) (plus_opp delta_star)))
    (plus_zero one)))).
Qed.

(* 1−δ* < one：δ* > 0 退化端（对照具体层 mix_omd_lt_one 语义） *)
Lemma amt_omd_lt_one : lt omd one.
Proof.
  unfold omd, minus.
  assert (Hds : lt zero delta_star).
  { exact (mult_positive lo lo
             (expf_pos (mult invT (opp Delta)))
             (expf_pos (mult invT (opp Delta)))). }
  assert (Hcore : lt (plus zero (plus one (opp delta_star)))
                     (plus delta_star (plus one (opp delta_star)))).
  { exact (bs_lpc zero delta_star (plus one (opp delta_star))
                  (plus one (opp delta_star))
                  Hds (le_refl (plus one (opp delta_star)))). }
  assert (Hshift : lt (plus one (opp delta_star))
                      (plus (plus one (opp delta_star)) delta_star)).
  { exact (lt_id_r_loc _ _ _ (plus_comm delta_star (plus one (opp delta_star)))
             (lt_id_l _ _ _
               (id_sym (id_trans (plus_comm zero (plus one (opp delta_star)))
                                 (plus_zero (plus one (opp delta_star)))))
               Hcore)). }
  exact (lt_id_r_loc _ _ _ (id_sym amt_one_eq) Hshift).
Qed.

(* ================= C 档：闭合主件 ================= *)

(* 闭合定理（严格版）：TV(T^k μ, T^k ν) < budget *)
Theorem amt_attention_mixing_time :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    lt (tv (@u_titer RI SS SO amt_kernel k mu)
           (@u_titer RI SS SO amt_kernel k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  destruct (@ums_k_select RI bs_lpc omd (tv mu nu) budget
              amt_omd_pos amt_omd_lt_one (amt_tv_nonneg mu nu)
              Hbudget Harch) as [k Hk].
  exists k.
  exact (le_lt_trans _ _ _
           (bounded_softmax_tv_iter enum enum_nonempty temp temp_pos
              Delta Delta_pos z z_lb z_ub expf expf_pos expf_zero
              expf_plus expf_mono_lt expf_mono_le bs_swap bs_abs bs_lpc
              sum_eq_list k mu nu Hmu Hnu)
           Hk).
Defined.

(* 闭合定理（非严格版）：TV(T^k μ, T^k ν) ≤ budget *)
Theorem amt_attention_mixing_time_le :
  forall mu nu : S -> R,
  Id (sum_over_S mu) one -> Id (sum_over_S nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (ums_scale (Datatypes.S N) one))) ->
  sigT (fun k : nat =>
    le (tv (@u_titer RI SS SO amt_kernel k mu)
           (@u_titer RI SS SO amt_kernel k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch.
  destruct (@ums_k_select RI bs_lpc omd (tv mu nu) budget
              amt_omd_pos amt_omd_lt_one (amt_tv_nonneg mu nu)
              Hbudget Harch) as [k Hk].
  exists k.
  apply (le_trans _ (mult (r_pow omd k) (tv mu nu))).
  - exact (bounded_softmax_tv_iter enum enum_nonempty temp temp_pos
             Delta Delta_pos z z_lb z_ub expf expf_pos expf_zero
             expf_plus expf_mono_lt expf_mono_le bs_swap bs_abs bs_lpc
             sum_eq_list k mu nu Hmu Hnu).
  - exact (lt_le_iff _ _ (inl Hk)).
Defined.


(* ================= 证书位就地消解（签名保持式） ===================== *)
(* bs_swap 参数位：由 sum_eq_list 参数位与列表 Fubini 组合学整体导出             *)
(*   （p7d_swap_of_sum_eq_list 全参显式供给，本参数位非独立接口位）。        *)

Context {DO : DecidableOrder RI}.

Theorem amtr_bs_swap : forall f : S -> S -> R,
  Id (sum_over_S (fun s : S => sum_over_S (fun s' : S => f s s')))
     (sum_over_S (fun s' : S => sum_over_S (fun s : S => f s s'))).
Proof.
  intro f.
  exact (p7d_swap_of_sum_eq_list enum sum_eq_list f).
Qed.

(* bs_abs 参数位：abs 非负恒等（ali_abs_ge_zero_id 供给，S01/fa53 深链） *)
Theorem amtr_bs_abs : forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (ali_abs_ge_zero_id a Ha).
Qed.

(* bs_lpc 参数位：lt 与 le 混合加法严格保序（fa53_lt_plus_compat_lt_le_dec） *)
Theorem amtr_bs_lpc : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (@fa53_lt_plus_compat_lt_le_dec RI DO a b c d Hab Hcd).
Qed.

End BoundedSoftmaxMixTime.

(* ================= 具体实现化读法消解块 ============================= *)

(* expf 参数位五字段：real_expf_realizable 封装投影（uabd1x 拆件形）。
   Id 面参数位（expf_zero/plus）在典范载体 req 幺等下取 req 形。 *)
Definition amtr_expf : Real -> Real := projT1 real_expf_realizable.

Theorem amtr_expf_pos : forall x : Real, real_lt real_zero (amtr_expf x).
Proof.
  intro x.
  exact (fst (projT2 real_expf_realizable) x).
Qed.

Theorem amtr_expf_zero : real_eq (amtr_expf real_zero) real_one.
Proof.
  exact (fst (snd (projT2 real_expf_realizable))).
Qed.

Theorem amtr_expf_plus : forall a b : Real,
  real_eq (amtr_expf (real_plus a b)) (real_mult (amtr_expf a) (amtr_expf b)).
Proof.
  exact (fst (snd (snd (projT2 real_expf_realizable)))).
Qed.

Theorem amtr_expf_mono_lt : forall a b : Real,
  real_lt a b -> real_lt (amtr_expf a) (amtr_expf b).
Proof.
  exact (fst (snd (snd (snd (projT2 real_expf_realizable))))).
Qed.

Theorem amtr_expf_mono_le : forall a b : Real,
  real_le a b -> real_le (amtr_expf a) (amtr_expf b).
Proof.
  exact (snd (snd (snd (snd (projT2 real_expf_realizable))))).
Qed.


(*   折叠机与出节真机 bs_list_sum 逐元素一致，en 上归纳）。           *)
Section AmtResSumEqListIdt.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

Fixpoint amtr_idt_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => @zero RI
  | x :: t => @plus RI (f x) (amtr_idt_list_sum f t)
  end.

Definition amtr_idt_sumf (en : list S) (f : S -> R) : R :=
  amtr_idt_list_sum f en.

Theorem amtr_sum_eq_list : forall (en : list S) (g : S -> R),
  Id (amtr_idt_sumf en g) (AttnDoeblin.bs_list_sum g en).
Proof.
  intros en g.
  unfold amtr_idt_sumf.
  induction en as [| x t IH].
  - exact id_refl.
  - simpl. exact (id_cong2 (@plus RI) id_refl IH).
Qed.

End AmtResSumEqListIdt.

Import RealInterfaceEnhancedMod.

(* temp/Delta/z/enum 参数位：Fin 2 非退化实例读法（cf2 供给件直引） *)

Theorem amtr_temp_pos : lt zero cf2_temp.
Proof.
  exact cf2_temp_pos.
Qed.

Theorem amtr_Delta_pos : lt zero cf2_Delta.
Proof.
  exact cf2_Delta_pos.
Qed.

Theorem amtr_z_lb : forall s s' : bool, le (opp cf2_Delta) (cf2_z s s').
Proof.
  exact cf2_z_lb.
Qed.

Theorem amtr_z_ub : forall s s' : bool, le (cf2_z s s') cf2_Delta.
Proof.
  exact cf2_z_ub.
Qed.

(* enum 参数位非空性的 Set 层 sigT 见证重述（InT 载体，见证 true） *)
Theorem amtr_enum_nonempty : sigT (fun t : bool => InT t cf2_enum2).
Proof.
  exact (existT _ true (InT_here true (false :: nil))).
Qed.

(* sum_eq_list 参数位：列表折叠实现化读法（抽象求和参数位实现为列表折叠机， *)


(* ================= 消解件假设面核验（预期全 Closed） =============== *)

Print Assumptions amtr_bs_swap.
Print Assumptions amtr_bs_abs.
Print Assumptions amtr_bs_lpc.
Print Assumptions amtr_expf_pos.
Print Assumptions amtr_expf_zero.
Print Assumptions amtr_expf_plus.
Print Assumptions amtr_expf_mono_lt.
Print Assumptions amtr_expf_mono_le.
Print Assumptions amtr_temp_pos.
Print Assumptions amtr_Delta_pos.
Print Assumptions amtr_z_lb.
Print Assumptions amtr_z_ub.
Print Assumptions amtr_enum_nonempty.
Print Assumptions amtr_sum_eq_list.
