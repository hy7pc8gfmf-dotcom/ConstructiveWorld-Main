(* ============================================================ *)
(* UpReqAttnMixTime.v —— 合龙定理 attention_mixing_time（AT3 接入版） *)
(* 论文7 §6.3 / §10.2 开放工作第 1 项（机器检查版）                *)
(*   AT2 席待命形（四关绿）× AT3 席接入 UpReqUMixSelect 真消费形态   *)
(*                                                              *)
(* 主件： amt_attention_mixing_time / amt_attention_mixing_time_le *)
(*   有界 logits softmax 核的 Doeblin 收缩引擎（AttnDoeblin.v 放电件） *)
(*   × 接口层显式 k 选取器（AT1 席 UpReqUMixSelect）的单一具名合龙： *)
(*   ∀ 归一化 μ ν、∀ budget > 0，构造性给出迭代步数 k 使          *)
(*   TV(T^k μ, T^k ν) < budget（及 ≤ 版），几何率 1−δ* 的 k 次幂，  *)
(*   δ* = e^{−2Δ/T} = lo·lo（lo = e^{−Δ/T}，精确无损耗）。         *)
(*                                                              *)
(* AT3 接入注记（2026-09-17，自 AT2 待命形换装真消费形态）：          *)
(*   ① 头部加 Require Import UpReqUMixSelect（AttnDoeblin 行后，    *)
(*      位序照依赖）；                                            *)
(*   ② 删 amt_ums_k_select_standby 占位 Hypothesis 位；             *)
(*   ③ 消费位换真 ums_k_select：出节 discharged 形含接口诚实前件     *)
(*      lt_plus_compat_lt_le 槽（proof-term 拖进放电签名判据，        *)
(*      E-STAGING-AT2 卡 4），由本节 bs_lpc 同型同位喂入；           *)
(*   ④ Arch 前件形对齐 AT1 实形：nat-尺度 ums_scale 形              *)
(*      （forall x, le zero x -> sigT (fun N => lt x (ums_scale      *)
(*      (Datatypes.S N) one))），非待命形预写的 r_arch_pow 泛化形——    *)
(*      签名偏差清单见 attn/_tat3_交付报告-20260917.md。              *)
(*                                                              *)
(* 侦察笔记（_tat2_probe1/_tat2_probe2 Check 实测放电形态）：        *)
(*   1. bounded_softmax_tv_iter 放电形：Section 内 Let delta_star *)
(*      在语句位全展开为                                          *)
(*      mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))     *)
(*           (expf (mult (inv_pos temp temp_pos) (opp Delta)))，   *)
(*      非 let-绑定；参量序 enum enum_nonempty temp temp_pos Delta *)
(*      Delta_pos z z_lb z_ub expf expf_pos expf_zero expf_plus    *)
(*      expf_mono_lt expf_mono_le bs_swap bs_abs bs_lpc sum_eq_list *)
(*      n mu nu（@ 全显 22 参）。                                  *)
(*   2. bs_kernel 放电形 11 参：enum enum_nonempty temp temp_pos   *)
(*      Delta z z_lb expf expf_pos expf_mono_le sum_eq_list ——     *)
(*      Delta_pos/expf_zero/expf_plus/expf_mono_lt/bs_swap/bs_abs/ *)
(*      bs_lpc 未入语句被剪除（未用 Variable 自动消失）。           *)
(*   3. u_omd_pos_next 放电形：(delta) (lt delta one)             *)
(*      (forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)) *)
(*      —— 第三槽在本节由 bs_lpc 同位重装。                        *)
(*   4. tv_dist_nonneg 在 S06 AttentionGibbsBridge 节；AttnDoeblin *)
(*      对 CW219 只 Require 不 Export，本席自 Require CW219 直连。  *)
(*                                                              *)
(* 非平凡性分级：                                                 *)
(*   A 自证胶水（退化端 δ*<1 严格性的构造性处置）：                *)
(*      amt_one_eq（one = 1−δ*+δ* 的 Id 换形，五段 id 链）、        *)
(*      amt_omd_lt_one（1−δ* < one：bs_lpc 严格缝合 + 两侧 Id 换形）； *)
(*   B 放电件消费桥（Require 消费，非重证）：                       *)
(*      amt_ds_lt_one（bs_delta_star_lt_one 本节重装）、            *)
(*      amt_omd_pos（u_omd_pos_next 重装，lpc 槽喂 bs_lpc）、       *)
(*      amt_tv_nonneg（tv_dist_nonneg 直连：TV₀ ≥ 0 端）；          *)
(*   C 合龙分量（AT2 核心增量 + AT3 真消费换装）：                  *)
(*      接口层 k 选取器消费 + 两侧 TV 缝合                         *)
(*      （amt_ds_pos 端 le_lt_trans；≤ 端 le_trans + lt_le_iff 升格） *)
(*      + sigT 见证打包。                                          *)
(*                                                              *)
(* 公理面自审：全件语句 Set 值；前提位全显式证书参数（接口前件=显式  *)
(*   参数，探针应 Closed——Arch 前件为 AT1 实形 nat-尺度 ums_scale   *)
(*   形，语句面如实可见）；无未证断言；无非构造 shortcut；主件       *)
(*   Defined 收束。                                                *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import UpReqUMixSelect.

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

(* ---- 核实例（放电 bs_kernel 的 11 参重装） ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let omd := minus one delta_star.

Let amt_kernel : S -> S -> R :=
  bs_kernel enum enum_nonempty temp temp_pos Delta z z_lb expf expf_pos
            expf_mono_le sum_eq_list.

(* ================= B 档：放电件消费桥 ================= *)

(* δ* < 1（消费 bs_delta_star_lt_one，参量序照 _tat2_probe1 实测） *)
Lemma amt_ds_lt_one : lt delta_star one.
Proof.
  exact (bs_delta_star_lt_one temp temp_pos Delta Delta_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* 1 − δ* > 0（消费 u_omd_pos_next，lpc 槽同位喂 bs_lpc） *)
Lemma amt_omd_pos : lt zero omd.
Proof.
  exact (u_omd_pos_next delta_star amt_ds_lt_one bs_lpc).
Qed.

(* TV₀ ≥ 0（消费 S06 tv_dist_nonneg 直连） *)
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

(* ================= C 档：合龙主件 ================= *)

(* 合龙定理（严格版）：TV(T^k μ, T^k ν) < budget *)
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

(* 合龙定理（非严格版）：TV(T^k μ, T^k ν) ≤ budget *)
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

End BoundedSoftmaxMixTime.
