(* ============================================================ *)
(* UpReqConcFin2.v —— 席 F21：Fin 2 非退化实例第一棒                             *)
(*   （T2 世界数据 + T3 TV 非平凡演示；_tax2_ 侦察报告 T1 探针实录照抄施工）      *)
(*   2026-09-18                                                            *)
(*                                                              *)
(* 上游（零改八母本）：CW219（RealEnhancedReal 实例）、UpReqAlgebra、          *)
(*   UpReqSumD（sumd 折叠）、UpReqDist（reqd_nat_to_R/reqd_opp_zero）、        *)
(*   UpReqConcSoftmax（csm_sumf 折叠机 + csm_abs_sum_le_eps 逐 eps 形）、      *)
(*   UpReqSampling（rsq_ 泛型 softmax 链：Zrow 三证 + rsq_bs_kernel +         *)
(*   k_titer + Unif 同构自持）、UpReqConcMixSel（cmk_tv 同形 TV 口径）、       *)
(*   UpReqConcB1（cb1_bs_abs 具体层消解）。                                   *)
(*                                                              *)
(* 本件三组（cf2_ 前缀；全树 grep 零撞名 20260918 实测）：                     *)
(*   T2 世界数据：world:=bool（T1 探针定谳：Fin.t 2 dependent-match 不可用，   *)
(*       bool 零新 import、destruct 二支、if 归约直通；论文「Fin n」措辞改注   *)
(*       bool 同构——交付注记声明）、enum2:=[true;false]、enum2_nonempty       *)
(*       （红线②强化项：Not-Prop 只许 False 消去落 Set——discriminate 一发，   *)
(*       与 cbt_enum_ne/T1 探针同形，零入 Set 槽）、Delta:=one+one_pos、       *)
(*       z:=±1 对称对（行间相异——核行真不同的结构前提）、z_lb/z_ub destruct    *)
(*       二支（inl rsq_bs_opp_lt＋le_refl 各 3 行，T1 实录照抄）、sumf:=       *)
(*       csm_sumf 2 元实例、sum_eq_list:=req_refl 一行（T1 断言 2）、Unif:=    *)
(*       1/2 均匀分布（rsq Unif 同构自持）、kernel:=rsq_bs_kernel 10+2 参全显   *)
(*       （槽序雷点：temp/temp_pos 后必跟 Delta 再 z）、Zrow_pos 证书、        *)
(*       kernel_row（行归一，泛型件直喂）、titer（10+2 全显）。               *)
(*   T3 TV 非平凡演示：点质量对 mu0=[1;0]/nu0=[0;1]（req 归一化双前提）下      *)
(*       cf2_tv_pos : lt zero (cf2_tv mu0 nu0)——B2 单点退化（cbt 档 TV≡0）    *)
(*       的反面，「非退化」的机器判据（inl 严格支 + req_two_pos）；le 一跳      *)
(*       cf2_tv_nonneg（合龙 Htv0 槽 concrete 形零前件供件）。                *)
(*   T4 前置件：cf2_abs_row_eps（|Sigma f·r| ≤ Sigma|f|·r + eps 逐 eps 形，     *)
(*       直消费 csm_abs_sum_le_eps；rsq_u_abs_row 消费位 plain 槽的 eps 绕行   *)
(*       第一段——AT6 报告 §五配方轨）。                                       *)
(*                                                              *)
(* 红线自审：①real_arch 的 And-Prop 支本件零触碰（本件不进合龙终装）；        *)
(*   ②enum_nonempty（Not-Prop）仅作证书直喂 rsq_ 泛型件（其内部 False 消去    *)
(*   落 Set 形已经 UpReqSampling 认证），本件零新增 Not 消去入 Set；           *)
(*   ③面-面逐字：语句层全用实例字段名（req/le/lt/zero/one/plus/mult/opp/abs），*)
(*   proof 内 exact 项式转换同体喂入（AT7 卡③最稳轨），零 cbn 后 apply。      *)
(* 公理面自审：全件语句 Set 值；前提位全显式证书参数；无未证断言、无经典逻辑、  *)
(*   无排中律；主件 Defined 收束可提取。                                    *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——E-STAGING-AT5 卡①）：             *)
(*   _taf21_ 前缀自建件，full 后 -vos 重跑生成实体（AT8 卡⑧）；full/vos 双证   *)
(*   为 G2 真关（tathA 卡：vos 不查 opaque 证明）；慢磨判活勿过早杀。           *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lra.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqDist.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
Require Import UpReqConcB2.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* T2 · Fin 2 世界数据（2 元非退化世界；全部 concrete 定义级，零新证明）         *)
(* ============================================================ *)

Section Fin2World.

(* 世界载体：bool（T1 探针定谳；论文「Fin n」措辞改注 bool 同构） *)
Definition cf2_world : Set := bool.
Definition cf2_enum2 : list bool := [true; false].

(* 红线②强化项：Not-Prop 的 enum 非空证书——False 消去落 Set 仅此认证形        *)
(* （discriminate 一发；与 cbt_enum_ne 同形，消费面仅 rsq_ 泛型件证书直喂位）   *)
Lemma cf2_enum_ne : Not ([true; false] = (@nil bool)).
Proof. intro H. discriminate H. Qed.

(* ---- 温度与 Delta（±1 对称 logit 下 max|z| = 1 = Delta，无 +1 松弛） ---- *)

Definition cf2_temp : Real := one.

Lemma cf2_temp_pos : lt zero cf2_temp.
Proof. exact one_pos. Defined.

Definition cf2_Delta : Real := one.

Lemma cf2_Delta_pos : lt zero cf2_Delta.
Proof. exact one_pos. Defined.

(* ---- z：±1 对称对（z true s' = +1、z false s' = −1；行间相异——核行真不同） ---- *)

Definition cf2_z (s s' : bool) : Real := if s then one else opp one.

(* z 双界（destruct 二支各 3 行，T1 实录照抄；rsq_bs_opp_lt 四参全显） *)
Lemma cf2_z_lb : forall s s' : bool, le (opp cf2_Delta) (cf2_z s s').
Proof.
  intros s s'. destruct s as [ | ].
  - exact (inl (@rsq_bs_opp_lt Real RealEnhancedReal cf2_Delta cf2_Delta_pos)).
  - exact (le_refl (opp cf2_Delta)).
Defined.

Lemma cf2_z_ub : forall s s' : bool, le (cf2_z s s') cf2_Delta.
Proof.
  intros s s'. destruct s as [ | ].
  - exact (le_refl cf2_Delta).
  - exact (inl (@rsq_bs_opp_lt Real RealEnhancedReal cf2_Delta cf2_Delta_pos)).
Defined.

(* ---- 求和机器：csm_sumf 2 元实例 + sum_eq_list（req_refl 一行，T1 断言 2） ---- *)

Definition cf2_sumf (f : bool -> Real) : Real := @csm_sumf bool [true; false] f.

Lemma cf2_sum_eq_list : forall g : bool -> Real,
  req (cf2_sumf g) (rsq_bs_list_sum bool g [true; false]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum bool g [true; false])). Defined.

(* ---- 均匀分布 U := 1/2（rsq Unif 同构自持；nR = 2·one 路线） ---- *)

Definition cf2_nR : Real := reqd_nat_to_R (length [true; false]).

Lemma cf2_nR_pos : lt zero cf2_nR.
Proof. exact (reqd_nat_to_R_pos 1). Defined.

Definition cf2_Unif : bool -> Real := fun _ : bool => inv_pos cf2_nR cf2_nR_pos.

Lemma cf2_Unif_norm : req (cf2_sumf cf2_Unif) one.
Proof.
  apply (req_trans _ (rsq_bs_list_sum bool cf2_Unif [true; false]) _).
  - exact (cf2_sum_eq_list cf2_Unif).
  - apply (req_trans _
             (mult (reqd_nat_to_R (length [true; false]))
                   (inv_pos cf2_nR cf2_nR_pos)) _).
    + exact (rsq_bs_list_const_sum bool (inv_pos cf2_nR cf2_nR_pos)
               [true; false]).
    + exact (inv_pos_correct cf2_nR cf2_nR_pos).
Defined.

(* ---- softmax 核实例化（rsq_bs_kernel 12 参全显——cbt_kernel 同形逐字换世界； ---- *)
(*      槽序雷点：temp/temp_pos 后必跟 Delta 再 z——T1 三次脱槽返工实录）        *)

Definition cf2_kernel : bool -> bool -> Real :=
  @rsq_bs_kernel Real RealEnhancedReal bool cf2_sumf [true; false] cf2_enum_ne
    cf2_temp cf2_temp_pos cf2_Delta cf2_z cf2_z_lb cf2_sum_eq_list.

(* Zrow 正性证书（T1 c2_Zrow_pos_cert 同位；rsq_Zrow 7+1 参、rsq_bs_Zrow_pos    *)
(*  12+1 参全显——泛型链在 2 元世界直通的机器实证） *)
Definition cf2_Zrow (s : bool) : Real :=
  @rsq_Zrow Real RealEnhancedReal bool cf2_sumf cf2_temp cf2_temp_pos cf2_z s.

Lemma cf2_Zrow_pos : forall s : bool, lt zero (cf2_Zrow s).
Proof.
  intro s.
  exact (@rsq_bs_Zrow_pos Real RealEnhancedReal bool cf2_sumf [true; false]
            cf2_enum_ne cf2_temp cf2_temp_pos cf2_Delta cf2_z cf2_z_lb
            cf2_sum_eq_list s).
Defined.

(* 核行归一（行和 = one——随机阵面；泛型 rsq_bs_kernel_row 直喂） *)
Lemma cf2_kernel_row : forall s : bool,
  req (cf2_sumf (fun s' : bool => cf2_kernel s s')) one.
Proof.
  intro s.
  exact (@rsq_bs_kernel_row Real RealEnhancedReal bool cf2_sumf
            (csm_sum_ext bool [true; false])
            (csm_sum_linear bool [true; false])
            [true; false] cf2_enum_ne cf2_temp cf2_temp_pos cf2_Delta cf2_z
            cf2_z_lb cf2_sum_eq_list s).
Defined.

(* 迭代器包装（k_titer 10+2 全显——cbt_titer 同形逐字换世界） *)
Definition cf2_titer (n : nat) (mu : bool -> Real) : bool -> Real :=
  k_titer bool cf2_sumf [true; false] cf2_enum_ne cf2_temp cf2_temp_pos
          cf2_Delta cf2_z cf2_z_lb cf2_sum_eq_list n mu.

(* ============================================================ *)
(* T3 · TV 非平凡演示：点质量对 [1;0]/[0;1] 下 TV 严格正                        *)
(*   ——B2 单点退化（TV≡0）的反面，「非退化」机器判据。                          *)
(* ============================================================ *)

(* 点质量对：mu0 = [1;0]、nu0 = [0;1]（req 归一化前提下件自供） *)
Definition cf2_mu0 (s : bool) : Real := if s then one else zero.
Definition cf2_nu0 (s : bool) : Real := if s then zero else one.

(* 质量前提双件（exact 项式直给，零 cbn——cf2_sumf 折叠在具体 2 元枚举上定义级） *)
Lemma cf2_mu0_mass : req (cf2_sumf cf2_mu0) one.
Proof.
  exact (req_trans _ _ _
           (req_plus_compat (cf2_mu0 true) (cf2_mu0 true)
              (plus (cf2_mu0 false) zero) zero
              (req_refl (cf2_mu0 true)) (plus_zero (cf2_mu0 false)))
           (plus_zero (cf2_mu0 true))).
Defined.

Lemma cf2_nu0_mass : req (cf2_sumf cf2_nu0) one.
Proof.
  exact (req_trans _ _ _
           (req_plus_compat (cf2_nu0 true) (cf2_nu0 true)
              (plus (cf2_nu0 false) zero) one
              (req_refl (cf2_nu0 true)) (plus_zero (cf2_nu0 false)))
           (req_plus_zero_l one)).
Defined.

(* TV 算子（cmk_tv/cbt_tv 同形；inv_two = 1/2） *)
Definition cf2_inv_two : Real := inv_pos (plus one one) req_two_pos.

Definition cf2_tv (mu nu : bool -> Real) : Real :=
  mult cf2_inv_two (cf2_sumf (fun s : bool => abs (req_minus (mu s) (nu s)))).

(* 逐点 |mu0 − nu0| = one（true 支：one−zero 直归一；false 支：zero−one 经     *)
(*  abs_opp + abs_pos 换形——req 面 |−1| = 1 的构造性通路） *)
Lemma cf2_abs_pt_one : forall b : bool,
  req (abs (req_minus (cf2_mu0 b) (cf2_nu0 b))) one.
Proof.
  intro b. destruct b as [ | ].
  - exact (req_trans _ _ _
             (req_abs_compat (req_minus (cf2_mu0 true) (cf2_nu0 true)) one
                (req_trans _ _ _
                   (req_plus_compat one one (opp zero) zero
                      (req_refl one) reqd_opp_zero)
                   (plus_zero one)))
             (abs_pos one one_pos)).
  - exact (req_trans _ _ _
             (req_abs_compat (req_minus (cf2_mu0 false) (cf2_nu0 false)) (opp one)
                (req_plus_zero_l (opp one)))
             (req_trans _ _ _ (abs_opp one) (abs_pos one one_pos))).
Defined.

(* 逐点差和归一：Sigma |mu0 − nu0| = 1 + 1（求和折叠 + plus_zero 缝合） *)
Lemma cf2_tv_sum_one : req
  (cf2_sumf (fun s : bool => abs (req_minus (cf2_mu0 s) (cf2_nu0 s))))
  (plus one one).
Proof.
  exact (req_trans _ _ _
           (req_plus_compat
              (abs (req_minus (cf2_mu0 true) (cf2_nu0 true)))
              (abs (req_minus (cf2_mu0 true) (cf2_nu0 true)))
              (plus (abs (req_minus (cf2_mu0 false) (cf2_nu0 false))) zero)
              (abs (req_minus (cf2_mu0 false) (cf2_nu0 false)))
              (cf2_abs_pt_one true)
              (plus_zero (abs (req_minus (cf2_mu0 false) (cf2_nu0 false)))))
           (req_plus_compat
              (abs (req_minus (cf2_mu0 true) (cf2_nu0 true)))
              one
              (abs (req_minus (cf2_mu0 false) (cf2_nu0 false)))
              one
              (cf2_abs_pt_one true) (cf2_abs_pt_one false))).
Defined.

(* T3 主件：TV 严格正（inl 严格支 + req_two_pos；req_lt_id_r_loc 换形一跳） *)
Theorem cf2_tv_pos : lt zero (cf2_tv cf2_mu0 cf2_nu0).
Proof.
  apply (req_lt_id_r_loc zero (mult cf2_inv_two (plus one one))
                           (cf2_tv cf2_mu0 cf2_nu0)).
  - exact (req_sym (mult cf2_inv_two
                     (cf2_sumf (fun s : bool => abs (req_minus (cf2_mu0 s) (cf2_nu0 s)))))
             (mult cf2_inv_two (plus one one))
             (req_mult_compat cf2_inv_two cf2_inv_two
                (cf2_sumf (fun s : bool => abs (req_minus (cf2_mu0 s) (cf2_nu0 s))))
                (plus one one)
                (req_refl cf2_inv_two) cf2_tv_sum_one)).
  - exact (mult_positive cf2_inv_two (plus one one)
             (inv_pos_pos (plus one one) req_two_pos) req_two_pos).
Defined.

(* le 一跳（合龙 Htv0 槽 concrete 形——零前件供件） *)
Lemma cf2_tv_nonneg : le zero (cf2_tv cf2_mu0 cf2_nu0).
Proof. exact (lt_le_iff zero (cf2_tv cf2_mu0 cf2_nu0) (inl cf2_tv_pos)). Defined.

(* ============================================================ *)
(* T4 前置件：eps 链重述第一段——|Sigma f·r| ≤ Sigma|f|·r + eps（逐 eps 形）      *)
(*   直消费 csm_abs_sum_le_eps；r ≥ 0 前件经 cf2_bs_abs 消解 abs r = r。        *)
(*   （rsq_u_abs_row 消费位 plain 冻结槽的 eps 绕行第一段，AT6 报告 §五轨）      *)
(* ============================================================ *)

(* 字段面 bs_abs 桥（cb1_bs_abs 的语句面同体转换；本件语句全字段名，消费位     *)
(*  零 real_* 面混写——F21 新坑：裸写泛型件头隐实例参成未解 evar 时，real_*      *)
(*  面项转换检查失败，字段面桥件消解） *)
Lemma cf2_bs_abs : forall a : Real, le zero a -> req (abs a) a.
Proof. exact cb1_bs_abs. Defined.

Lemma cf2_abs_row_eps : forall (f : bool -> Real) (r eps : Real),
  le zero r -> lt zero eps ->
  le (abs (cf2_sumf (fun s : bool => mult (f s) r)))
     (plus (mult (cf2_sumf (fun s : bool => abs (f s))) r) eps).
Proof.
  intros f r eps Hr Heps.
  apply (le_trans _ (plus (cf2_sumf (fun s : bool => abs (mult (f s) r))) eps)).
  - exact (csm_abs_sum_le_eps bool [true; false]
             (fun s : bool => mult (f s) r) eps Heps).
  - exact (le_id_r _ _ _
             (req_plus_compat (cf2_sumf (fun s : bool => abs (mult (f s) r)))
                (mult (cf2_sumf (fun s : bool => abs (f s))) r)
                eps eps
                (req_trans _ _ _
                   (csm_sum_ext bool [true; false]
                      (fun s : bool => abs (mult (f s) r))
                      (fun s : bool => mult r (abs (f s)))
                      (fun s : bool =>
                         @req_trans Real RealEnhancedReal
                           (abs (mult (f s) r))
                           (mult (abs (f s)) (abs r))
                           (mult r (abs (f s)))
                           (@abs_mult Real RealEnhancedReal (f s) r)
                           (@req_trans Real RealEnhancedReal
                              (mult (abs (f s)) (abs r))
                              (mult (abs (f s)) r)
                              (mult r (abs (f s)))
                              (@req_mult_compat Real RealEnhancedReal
                                 (abs (f s)) (abs (f s)) (abs r) r
                                 (@req_refl Real RealEnhancedReal (abs (f s)))
                                 (cf2_bs_abs r Hr))
                              (req_sym (mult r (abs (f s)))
                                 (mult (abs (f s)) r)
                                 (mult_comm r (abs (f s)))))))
                   (req_trans _ _ _
                      (csm_sum_linear bool [true; false] r
                         (fun s : bool => abs (f s)))
                      (mult_comm r (cf2_sumf (fun s : bool => abs (f s))))))
                (req_refl eps))
             (le_refl (plus (cf2_sumf (fun s : bool => abs (mult (f s) r)))
                        eps))).
Defined.

(* ============================================================ *)
(* 自检哨兵：±1 对称 z 的数值可见性（G3 辅证；reflexivity 级）                   *)
(*   z(true,·) = +1 ≠ z(false,·) = −1——行间相异，核行真不同的冒烟。             *)
(* ============================================================ *)

Lemma cf2_smoke_z_true : projT1 (cf2_z true false) 5%nat == 1%Q.
Proof. reflexivity. Qed.

Lemma cf2_smoke_z_false : projT1 (cf2_z false true) 5%nat == (-1)%Q.
Proof. reflexivity. Qed.

End Fin2World.

(* ============ G4 证据：全件 Closed（前提=显式证书参数，零外部未证假设） ============ *)
Print Assumptions cf2_enum_ne.
Print Assumptions cf2_z_lb.
Print Assumptions cf2_z_ub.
Print Assumptions cf2_sum_eq_list.
Print Assumptions cf2_Unif_norm.
Print Assumptions cf2_Zrow_pos.
Print Assumptions cf2_kernel_row.
Print Assumptions cf2_titer.
Print Assumptions cf2_mu0_mass.
Print Assumptions cf2_nu0_mass.
Print Assumptions cf2_tv_pos.
Print Assumptions cf2_tv_nonneg.
Print Assumptions cf2_bs_abs.
Print Assumptions cf2_abs_row_eps.

(* ============================================================ *)
(* 席 F22 续作（20260918）：T4 第二段 + T5 eps 链重述                           *)
(*                                                              *)
(* 目标：abs_sum_le plain 槽 ≥2 元 Or 墙（AT5/AT6/AT8 定谳）下的                  *)
(*   cmk_attention_mixing_time 消费前置全供给——全链走 csm_abs_sum_le_eps        *)
(*   逐 eps 通路。abs_sum_le 消费位清单逐槽对照（侦察报告 ③风险1）：             *)
(*     ① rsq_u_abs_row        (UpReqSampling L488)  → cf2_abs_row_kernel_eps   *)
(*     ② rsq_bounded_softmax_tv_contraction (L1153) → cf2_tv_contraction_eps    *)
(*     ③ rsq_bounded_softmax_tv_iter        (L1166) → cf2_tv_iter_eps           *)
(*   机器面（rsq_u_* 节件非 abs_sum_le 消费者）全部 @ 全显实例化直供——           *)
(*   「五族主件零改动直消费」判词的逐件验证（T6 前置侦察）。                      *)
(*   F21 卡坑位对照：rsq_ 系 @ 全显（症状一）、req_trans 五参（症状二）、         *)
(*   语句面桥 cf2_bs_abs（症状三）、六层项式逐层配平（症状五）。                  *)
(* ============================================================ *)

(* ---- F22·B0 常数族：lo/delta_star/omd（ReqBoundedSoftmax 节 Let 的出节实例） ---- *)

Definition cf2_invT : Real := inv_pos cf2_temp cf2_temp_pos.
Definition cf2_lo : Real := rsq_exp_pos_fn (mult cf2_invT (opp cf2_Delta)).
Definition cf2_delta_star : Real := mult cf2_lo cf2_lo.
Definition cf2_omd : Real := req_minus one cf2_delta_star.

Lemma cf2_lo_pos : lt zero cf2_lo.
Proof. exact (exp_neg_pos (opp (mult cf2_invT (opp cf2_Delta)))). Defined.

Lemma cf2_ds_pos : lt zero cf2_delta_star.
Proof. exact (mult_positive cf2_lo cf2_lo cf2_lo_pos cf2_lo_pos). Defined.

Lemma cf2_ds_lt_one : lt cf2_delta_star one.
Proof.
  exact (@rsq_bs_delta_star_lt_one Real RealEnhancedReal cf2_temp cf2_temp_pos
           cf2_Delta cf2_Delta_pos).
Defined.

Lemma cf2_aux_ds_omd : req (plus cf2_delta_star cf2_omd) one.
Proof. exact (@aux_delta_plus_omd Real RealEnhancedReal cf2_delta_star). Defined.

Lemma cf2_omd_pos : lt zero cf2_omd.
Proof.
  exact (@rsq_u_omd_pos_next Real RealEnhancedReal cf2_delta_star cf2_ds_lt_one
           real_lt_plus_compat_lt_le).
Defined.

Lemma cf2_omd_nonneg : le zero cf2_omd.
Proof. exact (lt_le_iff zero cf2_omd (inl cf2_omd_pos)). Defined.

Lemma cf2_omd_le_one : le cf2_omd one.
Proof.
  apply (le_id_r cf2_omd (plus cf2_delta_star cf2_omd) one).
  - exact cf2_aux_ds_omd.
  - apply (le_id_l cf2_omd (plus zero cf2_omd) (plus cf2_delta_star cf2_omd)).
    + exact (req_sym _ _ (req_plus_zero_l cf2_omd)).
    + exact (le_plus_compat zero cf2_delta_star cf2_omd cf2_omd
               (lt_le_iff zero cf2_delta_star (inl cf2_ds_pos))
               (le_refl cf2_omd)).
Defined.

(* c ≤ 1 与 e ≥ 0 下的 omd·e ≤ e 族用尾件（本段三处消费） *)
Lemma cf2_mult_one_l : forall a : Real, req (mult one a) a.
Proof. intro a. exact (req_trans _ _ _ (mult_comm one a) (mult_one a)). Defined.

Lemma cf2_le_mult_one : forall c e : Real, le zero e -> le c one -> le (mult c e) e.
Proof.
  intros c e H0 H1.
  apply (le_trans _ (mult one e)).
  - exact (le_mult_compat_weak c one e H0 H1).
  - exact (le_id_l (mult one e) e e (cf2_mult_one_l e) (le_refl e)).
Defined.

Lemma cf2_inv2_le_one : le cf2_inv_two one.
Proof.
  apply (le_id_r cf2_inv_two (mult (plus one one) cf2_inv_two) one).
  - exact (inv_pos_correct (plus one one) req_two_pos).
  - apply (le_id_l cf2_inv_two (mult one cf2_inv_two)
                     (mult (plus one one) cf2_inv_two)).
    + exact (req_sym _ _ (req_trans _ _ _ (mult_comm one cf2_inv_two)
                            (mult_one cf2_inv_two))).
    + exact (le_mult_compat_weak one (plus one one) cf2_inv_two
                 (lt_le_iff zero cf2_inv_two
                    (inl (inv_pos_pos (plus one one) req_two_pos)))
                 (le_id_l one (plus one zero) (plus one one)
                    (req_sym _ _ (plus_zero one))
                    (le_plus_compat one one zero one (le_refl one)
                       (lt_le_iff zero one (inl one_pos))))).
Defined.

(* nR·(1/2) = 1：nR 两件换形（几何 slack 的 eps/2 预算与 2·e₀=eps 找零） *)
Lemma cf2_nR_two : req cf2_nR (plus one one).
Proof.
  exact (req_trans _ _ _
           (req_refl (plus one (plus one (reqd_nat_to_R 0%nat))))
           (req_plus_compat one one (plus one zero) one
              (req_refl one) (plus_zero one))).
Defined.

Lemma cf2_nR_inv2 : req (mult cf2_nR cf2_inv_two) one.
Proof.
  apply (req_trans _ (mult cf2_nR (cf2_Unif true)) _).
  - exact (req_mult_compat cf2_nR cf2_nR cf2_inv_two (cf2_Unif true)
             (req_refl cf2_nR)
             (req_sym _ _
                (inv_pos_ext cf2_nR (plus one one) cf2_nR_pos req_two_pos
                   cf2_nR_two))).
  - exact (inv_pos_correct cf2_nR cf2_nR_pos).
Defined.

(* Σ(f−g) = Σf − Σg（Hd 链消费；reqd_sum_minus 的 bool 2 元实例） *)
Definition cf2_sum_minus : forall f g : bool -> Real,
  req (cf2_sumf (fun s : bool => req_minus (f s) (g s)))
      (req_minus (cf2_sumf f) (cf2_sumf g)) :=
  reqd_sum_minus bool cf2_sumf (csm_sum_ext bool [true; false])
    (csm_sum_add bool [true; false]) (csm_sum_linear bool [true; false]).

(* ---- F22·T4-2a：核正性/非负 + abs_row 消费位①的核行 eps 供给 ---- *)

Lemma cf2_kernel_pos : forall s s' : bool, lt zero (cf2_kernel s s').
Proof.
  intros s s'.
  exact (@rsq_bs_kernel_pos Real RealEnhancedReal bool cf2_sumf [true; false]
            cf2_enum_ne cf2_temp cf2_temp_pos cf2_Delta cf2_z cf2_z_lb
            cf2_sum_eq_list s s').
Defined.

Lemma cf2_kernel_nonneg : forall s s' : bool, le zero (cf2_kernel s s').
Proof.
  intros s s'.
  exact (lt_le_iff zero (cf2_kernel s s') (inl (cf2_kernel_pos s s'))).
Defined.

(* 消费位①（rsq_u_abs_row L488 同位）eps 形：核行内 r 不提出（与 rsq_u_abs_row *)
(*  RHS 同构，Hsum 交换链直用）；直抄 cf2_abs_row_eps 模板前半（AT6 §五轨）。    *)
Lemma cf2_abs_row_kernel_eps : forall (f : bool -> Real) (s' : bool) (eps : Real),
  lt zero eps ->
  le (abs (cf2_sumf (fun s : bool => mult (f s) (cf2_kernel s s'))))
     (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (cf2_kernel s s'))) eps).
Proof.
  intros f s' eps Heps.
  apply (le_id_r (abs (cf2_sumf (fun s : bool => mult (f s) (cf2_kernel s s'))))
                 (plus (cf2_sumf (fun s : bool => abs (mult (f s) (cf2_kernel s s')))) eps)
                 (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (cf2_kernel s s'))) eps)).
  - exact (req_plus_compat
              (cf2_sumf (fun s : bool => abs (mult (f s) (cf2_kernel s s'))))
              (cf2_sumf (fun s : bool => mult (abs (f s)) (cf2_kernel s s')))
              eps eps
              (csm_sum_ext bool [true; false]
                 (fun s : bool => abs (mult (f s) (cf2_kernel s s')))
                 (fun s : bool => mult (abs (f s)) (cf2_kernel s s'))
                 (fun s : bool =>
                    req_trans _ _ _
                      (abs_mult (f s) (cf2_kernel s s'))
                      (req_mult_compat (abs (f s)) (abs (f s))
                         (abs (cf2_kernel s s')) (cf2_kernel s s')
                         (req_refl (abs (f s)))
                         (cf2_bs_abs (cf2_kernel s s') (cf2_kernel_nonneg s s')))))
              (req_refl eps)).
  - exact (csm_abs_sum_le_eps bool [true; false]
              (fun s : bool => mult (f s) (cf2_kernel s s')) eps Heps).
Defined.

(* ---- F22·T4-2b：bs_swap 槽供给（2 元四项和的直接换序；req_plus_exchange 收口） ---- *)

Lemma cf2_bs_swap : forall f : bool -> bool -> Real,
  req (cf2_sumf (fun s : bool => cf2_sumf (fun s' : bool => f s s')))
      (cf2_sumf (fun s' : bool => cf2_sumf (fun s : bool => f s s'))).
Proof.
  intro f.
  exact (cb1_swap_lists bool f [true; false] [true; false]).
Defined.

(* ---- F22·T5 机器面：Doeblin 分解机器 @ 全显实例化（五族主件直消费验证） ---- *)

Definition cf2_k_step (mu : bool -> Real) (s' : bool) : Real :=
  cf2_sumf (fun s : bool => mult (mu s) (cf2_kernel s s')).

Definition cf2_ptdiff (mu nu : bool -> Real) (s : bool) : Real :=
  req_minus (mu s) (nu s).

Lemma cf2_minorization : forall s s' : bool,
  le (mult cf2_delta_star (cf2_Unif s')) (cf2_kernel s s').
Proof.
  intros s s'.
  apply (le_id_l (mult cf2_delta_star (cf2_Unif s'))
                 (mult cf2_delta_star
                    (inv_pos (reqd_nat_to_R (length [true; false]))
                       (@rsq_bs_nR_pos Real RealEnhancedReal bool cf2_sumf [true; false] cf2_enum_ne
                          cf2_sum_eq_list)))
                 (cf2_kernel s s')).
  - exact (req_mult_compat cf2_delta_star cf2_delta_star (cf2_Unif s')
              (inv_pos (reqd_nat_to_R (length [true; false]))
                 (@rsq_bs_nR_pos Real RealEnhancedReal bool cf2_sumf [true; false] cf2_enum_ne
                    cf2_sum_eq_list))
              (req_refl cf2_delta_star)
              (inv_pos_ext (reqd_nat_to_R (length [true; false]))
                 (reqd_nat_to_R (length [true; false]))
                 cf2_nR_pos
                 (@rsq_bs_nR_pos Real RealEnhancedReal bool cf2_sumf [true; false] cf2_enum_ne
                    cf2_sum_eq_list)
                 (req_refl (reqd_nat_to_R (length [true; false]))))).
  - exact (@rsq_bs_minorization Real RealEnhancedReal bool cf2_sumf
              [true; false] cf2_enum_ne cf2_temp cf2_temp_pos cf2_Delta cf2_z
              cf2_z_lb cf2_z_ub cf2_sum_eq_list s s').
Defined.

Definition cf2_r_kernel (s s' : bool) : Real :=
  @rsq_u_r_kernel Real RealEnhancedReal bool cf2_Unif cf2_delta_star
     cf2_ds_lt_one cf2_kernel real_lt_plus_compat_lt_le s s'.

Definition cf2_rD (mu nu : bool -> Real) (s' : bool) : Real :=
  cf2_sumf (fun s : bool => mult (cf2_ptdiff mu nu s) (cf2_r_kernel s s')).

Definition cf2_rX (mu nu : bool -> Real) (s' : bool) : Real :=
  cf2_sumf (fun s : bool => mult (abs (cf2_ptdiff mu nu s)) (cf2_r_kernel s s')).

Lemma cf2_r_nonneg : forall s s' : bool, le zero (cf2_r_kernel s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg Real RealEnhancedReal bool cf2_Unif cf2_delta_star
            cf2_ds_lt_one cf2_kernel cf2_minorization
            real_lt_plus_compat_lt_le s s').
Defined.

Lemma cf2_r_norm : forall s : bool,
  req (cf2_sumf (fun s' : bool => cf2_r_kernel s s')) one.
Proof.
  intro s.
  exact (@rsq_u_r_norm Real RealEnhancedReal bool cf2_sumf
            (csm_sum_ext bool [true; false])
            (csm_sum_linear bool [true; false])
            (csm_sum_add bool [true; false])
            cf2_Unif cf2_Unif_norm cf2_delta_star cf2_ds_lt_one cf2_kernel
            cf2_kernel_row real_lt_plus_compat_lt_le s).
Defined.

Lemma cf2_step_decomp : forall (mu : bool -> Real) (s' : bool),
  req (cf2_sumf mu) one ->
  req (cf2_k_step mu s')
      (plus (mult cf2_delta_star (cf2_Unif s'))
            (mult cf2_omd
               (cf2_sumf (fun s : bool => mult (mu s) (cf2_r_kernel s s'))))).
Proof.
  intros mu s' Hmu.
  exact (@rsq_u_step_decomp Real RealEnhancedReal bool cf2_sumf
            (csm_sum_ext bool [true; false])
            (csm_sum_linear bool [true; false])
            (csm_sum_add bool [true; false])
            cf2_Unif cf2_delta_star cf2_ds_lt_one cf2_kernel
            real_lt_plus_compat_lt_le mu s' Hmu).
Defined.

Lemma cf2_k_step_norm : forall mu : bool -> Real,
  req (cf2_sumf mu) one ->
  req (cf2_sumf (fun s' : bool => cf2_k_step mu s')) one.
Proof.
  intros mu Hmu.
  exact (@rsq_u_step_norm Real RealEnhancedReal bool cf2_sumf
            (csm_sum_ext bool [true; false])
            (csm_sum_linear bool [true; false])
            (csm_sum_add bool [true; false])
            cf2_Unif cf2_Unif_norm cf2_delta_star cf2_ds_lt_one cf2_kernel
            cf2_kernel_row cf2_bs_swap real_lt_plus_compat_lt_le mu Hmu).
Defined.


(* ---- F22·T4-2 追加：abs_row 供给件按权重函数泛型化——消费位的核/Р 核各一行 ----
   （hang 根因坑：按 kernel 实例化的供给件喂 r_kernel 槽，单化器在双核塔间
     转换下潜循环爆炸；泛型化后逐位钉死，零下潜。） *)
Lemma cf2_abs_row_gen_eps : forall (K : bool -> bool -> Real) (f : bool -> Real)
    (s' : bool) (eps : Real),
  (forall s : bool, le zero (K s s')) -> lt zero eps ->
  le (abs (cf2_sumf (fun s : bool => mult (f s) (K s s'))))
     (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (K s s'))) eps).
Proof.
  intros K f s' eps HK Heps.
  apply (le_id_r (abs (cf2_sumf (fun s : bool => mult (f s) (K s s'))))
                 (plus (cf2_sumf (fun s : bool => abs (mult (f s) (K s s')))) eps)
                 (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (K s s'))) eps)).
  - exact (req_plus_compat
              (cf2_sumf (fun s : bool => abs (mult (f s) (K s s'))))
              (cf2_sumf (fun s : bool => mult (abs (f s)) (K s s')))
              eps eps
              (csm_sum_ext bool [true; false]
                 (fun s : bool => abs (mult (f s) (K s s')))
                 (fun s : bool => mult (abs (f s)) (K s s'))
                 (fun s : bool =>
                    req_trans _ _ _
                      (abs_mult (f s) (K s s'))
                      (req_mult_compat (abs (f s)) (abs (f s))
                         (abs (K s s')) (K s s')
                         (req_refl (abs (f s)))
                         (cf2_bs_abs (K s s') (HK s)))))
              (req_refl eps)).
  - exact (csm_abs_sum_le_eps bool [true; false]
              (fun s : bool => mult (f s) (K s s')) eps Heps).
Defined.

Lemma cf2_abs_row_r_kernel_eps : forall (f : bool -> Real) (s' : bool) (eps : Real),
  lt zero eps ->
  le (abs (cf2_sumf (fun s : bool => mult (f s) (cf2_r_kernel s s'))))
     (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (cf2_r_kernel s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (cf2_abs_row_gen_eps cf2_r_kernel f s' eps
           (fun s : bool => cf2_r_nonneg s s') Heps).
Defined.
(* ---- F22·T5a：消费位②——单步 TV 收缩逐 eps 形（L499-650 同构重走） ---- *)
(*   e₀ := inv_two·eps 预算制：Hpt 逐点 slack e₀，外和 2·e₀ =req= eps 精确找零；
     omd·e₀ ≤ e₀ 走 le_mult_compat_weak（omd ≤ 1）。 *)

Theorem cf2_tv_contraction_eps : forall (mu nu : bool -> Real) (eps : Real),
  req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> lt zero eps ->
  le (cf2_tv (cf2_k_step mu) (cf2_k_step nu))
     (plus (mult cf2_omd (cf2_tv mu nu)) eps).
Proof.
  intros mu nu eps Hmu Hnu Heps.
  assert (Hge : le zero cf2_omd).
  { exact cf2_omd_nonneg. }
  assert (He0 : lt zero (mult cf2_inv_two eps)).
  { exact (mult_positive cf2_inv_two eps
             (inv_pos_pos (plus one one) req_two_pos) Heps). }
  assert (Hpt : forall s' : bool,
    le (abs (req_minus (cf2_k_step mu s') (cf2_k_step nu s')))
       (plus (mult cf2_omd (cf2_rX mu nu s')) (mult cf2_inv_two eps))).
  { intro s'.
    assert (Hd : req (req_minus (cf2_k_step mu s') (cf2_k_step nu s'))
                     (mult cf2_omd (cf2_rD mu nu s'))).
    { apply (req_trans _
               (req_minus
                  (plus (mult cf2_delta_star (cf2_Unif s'))
                        (mult cf2_omd
                           (cf2_sumf (fun s : bool => mult (mu s) (cf2_r_kernel s s')))))
                  (plus (mult cf2_delta_star (cf2_Unif s'))
                        (mult cf2_omd
                           (cf2_sumf (fun s : bool => mult (nu s) (cf2_r_kernel s s')))))) _).
      - exact (reqd_minus_compat _ _ _ _
                  (cf2_step_decomp mu s' Hmu) (cf2_step_decomp nu s' Hnu)).
      - apply (req_trans _
                 (req_minus
                    (mult cf2_omd
                       (cf2_sumf (fun s : bool => mult (mu s) (cf2_r_kernel s s'))))
                    (mult cf2_omd
                       (cf2_sumf (fun s : bool => mult (nu s) (cf2_r_kernel s s'))))) _).
        + exact (req_minus_plus_congr_l (mult cf2_delta_star (cf2_Unif s')) _ _).
        + apply (req_trans _
                    (mult cf2_omd
                       (req_minus
                          (cf2_sumf (fun s : bool => mult (mu s) (cf2_r_kernel s s')))
                          (cf2_sumf (fun s : bool => mult (nu s) (cf2_r_kernel s s'))))) _).
          * exact (req_minus_factor cf2_omd _ _).
          * apply (req_mult_compat cf2_omd cf2_omd _ _ (req_refl cf2_omd)).
            apply (req_trans _
                       (cf2_sumf (fun s : bool =>
                          req_minus (mult (mu s) (cf2_r_kernel s s'))
                                    (mult (nu s) (cf2_r_kernel s s')))) _).
            -- exact (req_sym _ _
                          (cf2_sum_minus
                             (fun s : bool => mult (mu s) (cf2_r_kernel s s'))
                             (fun s : bool => mult (nu s) (cf2_r_kernel s s')))).
            -- exact (csm_sum_ext bool [true; false] _ _
                          (fun s : bool => req_minus_factor_pt (mu s) (nu s)
                                              (cf2_r_kernel s s'))). }
    apply (le_id_l (abs (req_minus (cf2_k_step mu s') (cf2_k_step nu s')))
                   (mult cf2_omd (abs (cf2_rD mu nu s')))
                   (plus (mult cf2_omd (cf2_rX mu nu s')) (mult cf2_inv_two eps))).
    - exact (req_trans _ _ _
               (req_abs_compat _ _ Hd)
               (req_trans _ _ _
                  (abs_mult cf2_omd (cf2_rD mu nu s'))
                  (req_mult_compat (abs cf2_omd) cf2_omd
                     (abs (cf2_rD mu nu s')) (abs (cf2_rD mu nu s'))
                     (cf2_bs_abs cf2_omd Hge)
                     (req_refl (abs (cf2_rD mu nu s')))))).
    - apply (le_trans _
                (mult cf2_omd (plus (cf2_rX mu nu s') (mult cf2_inv_two eps)))).
      + exact (req_le_mult_compat_r cf2_omd (abs (cf2_rD mu nu s'))
                  (plus (cf2_rX mu nu s') (mult cf2_inv_two eps)) Hge
                  (cf2_abs_row_r_kernel_eps (cf2_ptdiff mu nu) s'
                     (mult cf2_inv_two eps) He0)).
      + apply (le_trans _
                  (plus (mult cf2_omd (cf2_rX mu nu s'))
                        (mult cf2_omd (mult cf2_inv_two eps)))).
        * exact (le_id_l _
                    (plus (mult cf2_omd (cf2_rX mu nu s'))
                          (mult cf2_omd (mult cf2_inv_two eps)))
                    (plus (mult cf2_omd (cf2_rX mu nu s'))
                          (mult cf2_omd (mult cf2_inv_two eps)))
                    (distrib cf2_omd (cf2_rX mu nu s') (mult cf2_inv_two eps))
                    (le_refl (plus (mult cf2_omd (cf2_rX mu nu s'))
                                   (mult cf2_omd (mult cf2_inv_two eps))))).
        * exact (le_plus_compat
                    (mult cf2_omd (cf2_rX mu nu s'))
                    (mult cf2_omd (cf2_rX mu nu s'))
                    (mult cf2_omd (mult cf2_inv_two eps))
                    (mult cf2_inv_two eps)
                    (le_refl (mult cf2_omd (cf2_rX mu nu s')))
                    (cf2_le_mult_one cf2_omd (mult cf2_inv_two eps)
                       (lt_le_iff zero (mult cf2_inv_two eps) (inl He0))
                       cf2_omd_le_one)). }
  assert (HsumSwap : req
    (cf2_sumf (fun s' : bool => cf2_rX mu nu s'))
    (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))).
  { exact (req_trans _ _ _
             (req_sym _ _
                (cf2_bs_swap (fun s s' : bool =>
                   mult (abs (cf2_ptdiff mu nu s)) (cf2_r_kernel s s'))))
             (req_trans _ _ _
                (csm_sum_ext bool [true; false]
                   (fun s : bool =>
                      cf2_sumf (fun s' : bool =>
                         mult (abs (cf2_ptdiff mu nu s)) (cf2_r_kernel s s')))
                   (fun s : bool =>
                      mult (abs (cf2_ptdiff mu nu s))
                           (cf2_sumf (fun s' : bool => cf2_r_kernel s s')))
                   (fun s : bool =>
                      csm_sum_linear bool [true; false]
                         (abs (cf2_ptdiff mu nu s))
                         (fun s' : bool => cf2_r_kernel s s')))
                (csm_sum_ext bool [true; false]
                   (fun s : bool =>
                      mult (abs (cf2_ptdiff mu nu s))
                           (cf2_sumf (fun s' : bool => cf2_r_kernel s s')))
                   (fun s : bool => abs (cf2_ptdiff mu nu s))
                   (fun s : bool =>
                      req_trans _ _ _
                         (req_mult_compat
                            (abs (cf2_ptdiff mu nu s)) (abs (cf2_ptdiff mu nu s))
                            (cf2_sumf (fun s' : bool => cf2_r_kernel s s')) one
                            (req_refl (abs (cf2_ptdiff mu nu s)))
                            (cf2_r_norm s))
                         (mult_one (abs (cf2_ptdiff mu nu s))))))). }
  assert (HsumConst : req (cf2_sumf (fun _ : bool => mult cf2_inv_two eps)) eps).
  { exact (req_trans _ _ _
             (rsq_bs_list_const_sum bool (mult cf2_inv_two eps) [true; false])
             (req_trans _ _ _
                (mult_assoc cf2_nR cf2_inv_two eps)
                (req_trans _ _ _
                   (req_mult_compat (mult cf2_nR cf2_inv_two) one eps eps
                      cf2_nR_inv2 (req_refl eps))
                   (req_trans _ _ _ (mult_comm one eps) (mult_one eps))))). }
  assert (Hsum : le
    (cf2_sumf (fun s' : bool => abs (req_minus (cf2_k_step mu s') (cf2_k_step nu s'))))
    (plus (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))) eps)).
  { apply (le_trans _
              (plus (mult cf2_omd (cf2_sumf (fun s' : bool => cf2_rX mu nu s'))) eps)).
    - apply (le_trans _
                (cf2_sumf (fun s' : bool =>
                   plus (mult cf2_omd (cf2_rX mu nu s')) (mult cf2_inv_two eps)))).
      + exact (csm_sum_le bool [true; false]
                   (fun s' : bool => abs (req_minus (cf2_k_step mu s') (cf2_k_step nu s')))
                   (fun s' : bool =>
                      plus (mult cf2_omd (cf2_rX mu nu s')) (mult cf2_inv_two eps))
                   Hpt).
      + exact (lt_le_iff _ _ (inr
                   (req_trans _ _ _
                      (csm_sum_add bool [true; false]
                         (fun s' : bool => mult cf2_omd (cf2_rX mu nu s'))
                         (fun _ : bool => mult cf2_inv_two eps))
                      (req_plus_compat
                         (cf2_sumf (fun s' : bool => mult cf2_omd (cf2_rX mu nu s')))
                         (mult cf2_omd (cf2_sumf (fun s' : bool => cf2_rX mu nu s')))
                         (cf2_sumf (fun _ : bool => mult cf2_inv_two eps)) eps
                         (csm_sum_linear bool [true; false] cf2_omd
                            (fun s' : bool => cf2_rX mu nu s'))
                         HsumConst)))).
    - exact (lt_le_iff _ _ (inr
                 (req_plus_compat
                    (mult cf2_omd (cf2_sumf (fun s' : bool => cf2_rX mu nu s')))
                    (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))
                    eps eps
                    (req_mult_compat cf2_omd cf2_omd
                       (cf2_sumf (fun s' : bool => cf2_rX mu nu s'))
                       (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))
                       (req_refl cf2_omd) HsumSwap)
                    (req_refl eps)))). }
  apply (le_trans _
              (mult cf2_inv_two
                 (plus (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))
                       eps))).
  - exact (req_le_mult_compat_r cf2_inv_two
              (cf2_sumf (fun s' : bool =>
                 abs (req_minus (cf2_k_step mu s') (cf2_k_step nu s'))))
              (plus (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))
                    eps)
              (lt_le_iff zero cf2_inv_two
                 (inl (inv_pos_pos (plus one one) req_two_pos)))
              Hsum).
  - apply (le_trans _ (plus (mult cf2_omd (cf2_tv mu nu)) (mult cf2_inv_two eps))).
    + assert (HX2 : req (mult cf2_inv_two (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))) (mult cf2_omd (mult cf2_inv_two (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))))).
      { exact (req_trans _ _ _
                 (mult_assoc cf2_inv_two cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))
                 (req_trans _ _ _
                    (req_mult_compat (mult cf2_inv_two cf2_omd)
                       (mult cf2_omd cf2_inv_two)
                       (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))) (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))
                       (mult_comm cf2_inv_two cf2_omd)
                       (req_refl (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))))
                    (req_sym _ _ (mult_assoc cf2_omd cf2_inv_two (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))))). }
      apply (le_trans _ (plus (mult cf2_inv_two (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))) (mult cf2_inv_two eps))).
      * exact (le_id_l _ _ _ (distrib cf2_inv_two (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s)))) eps) (le_refl _)).
      * exact (le_id_l _ _ _ (req_plus_compat (mult cf2_inv_two (mult cf2_omd (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))) (mult cf2_omd (mult cf2_inv_two (cf2_sumf (fun s : bool => abs (cf2_ptdiff mu nu s))))) (mult cf2_inv_two eps) (mult cf2_inv_two eps) HX2 (req_refl (mult cf2_inv_two eps))) (le_refl _)).
    + exact (le_plus_compat (mult cf2_omd (cf2_tv mu nu))
                            (mult cf2_omd (cf2_tv mu nu))
                            (mult cf2_inv_two eps) eps
                 (le_refl (mult cf2_omd (cf2_tv mu nu)))
                 (cf2_le_mult_one cf2_inv_two eps
                    (lt_le_iff zero eps (inl Heps)) cf2_inv2_le_one)).
Defined.

(* ---- F22·T5b：消费位③——迭代 TV 收缩逐 eps 形（slack 线性累积 + 尾预算） ---- *)

Lemma cf2_titer_norm : forall (n : nat) (mu : bool -> Real),
  req (cf2_sumf mu) one -> req (cf2_sumf (cf2_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (cf2_k_step_norm (cf2_titer n mu) (IH mu H)).
Defined.

(* nR·(S k) 换形：mult (reqd_nat_to_R (S k)) e = e + mult (reqd_nat_to_R k) e *)
Lemma cf2_nR_S_split : forall (k : nat) (e : Real),
  req (mult (reqd_nat_to_R (Datatypes.S k)) e) (plus (mult (reqd_nat_to_R k) e) e).
Proof.
  intro k. intro e.
  exact (req_trans _ _ _
            (mult_comm (reqd_nat_to_R (Datatypes.S k)) e)
            (req_trans _ _ _
               (distrib e one (reqd_nat_to_R k))
               (req_trans _ _ _
                  (req_plus_compat (mult e one) e
                     (mult e (reqd_nat_to_R k)) (mult (reqd_nat_to_R k) e)
                     (req_trans _ _ _ (mult_comm e one) (cf2_mult_one_l e))
                     (mult_comm e (reqd_nat_to_R k)))
                  (plus_comm e (mult (reqd_nat_to_R k) e))))).
Qed.
(* ============ F22·G4 证据追加：全件 Closed（前提=显式证书参数） ============ *)

Theorem cf2_tv_iter_eps : forall (n : nat) (mu nu : bool -> Real) (eps : Real),
  req (cf2_sumf mu) one -> req (cf2_sumf nu) one -> lt zero eps ->
  le (cf2_tv (cf2_titer n mu) (cf2_titer n nu))
     (plus (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
           (mult (reqd_nat_to_R n) eps)).
Proof.
  intro n. induction n as [| n IH]; intros mu nu eps Hmu Hnu Heps.
  - exact (le_id_r (cf2_tv mu nu) (plus (cf2_tv mu nu) zero)
             (plus (mult (req_r_pow cf2_omd 0%nat) (cf2_tv mu nu))
                   (mult (reqd_nat_to_R 0%nat) eps))
             (req_sym _ _
                (req_plus_compat (mult (req_r_pow cf2_omd 0%nat) (cf2_tv mu nu))
                   (cf2_tv mu nu)
                   (mult (reqd_nat_to_R 0%nat) eps) zero
                   (req_trans _ _ _
                      (mult_comm (req_r_pow cf2_omd 0%nat) (cf2_tv mu nu))
                      (mult_one (cf2_tv mu nu)))
                   (req_trans _ _ _
                      (mult_comm (reqd_nat_to_R 0%nat) eps)
                      (mult_zero eps))))
             (le_id_l (cf2_tv mu nu) (plus (cf2_tv mu nu) zero)
                (plus (cf2_tv mu nu) zero)
                (req_sym _ _ (plus_zero (cf2_tv mu nu)))
                (le_refl (plus (cf2_tv mu nu) zero)))).
  - assert (Hge : le zero cf2_omd).
    { exact cf2_omd_nonneg. }
    assert (HQ0 : le zero (mult (reqd_nat_to_R n) eps)).
    { destruct n as [| m].
      - exact (le_id_l zero (mult (reqd_nat_to_R 0%nat) eps)
                 (mult (reqd_nat_to_R 0%nat) eps)
                 (req_sym _ _
                    (req_trans _ _ _
                       (mult_comm (reqd_nat_to_R 0%nat) eps)
                       (mult_zero eps)))
                 (le_refl (mult (reqd_nat_to_R 0%nat) eps))).
      - exact (lt_le_iff zero (mult (reqd_nat_to_R (Datatypes.S m)) eps)
                   (inl (mult_positive (reqd_nat_to_R (Datatypes.S m)) eps
                          (reqd_nat_to_R_pos m) Heps))). }
    assert (HXS : req (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))) (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))).
    { exact (req_trans _ _ _
               (mult_assoc cf2_omd (req_r_pow cf2_omd n) (cf2_tv mu nu))
               (req_mult_compat (mult cf2_omd (req_r_pow cf2_omd n))
                  (req_r_pow cf2_omd (Datatypes.S n))
                  (cf2_tv mu nu) (cf2_tv mu nu)
                  (req_refl (mult cf2_omd (req_r_pow cf2_omd n)))
                  (req_refl (cf2_tv mu nu)))). }
    apply (le_trans _
                (plus (mult cf2_omd (cf2_tv (cf2_titer n mu) (cf2_titer n nu))) eps)).
    + exact (le_id_l
                 (cf2_tv (cf2_titer (Datatypes.S n) mu) (cf2_titer (Datatypes.S n) nu))
                 (cf2_tv (cf2_k_step (cf2_titer n mu)) (cf2_k_step (cf2_titer n nu)))
                 (plus (mult cf2_omd (cf2_tv (cf2_titer n mu) (cf2_titer n nu))) eps)
                 (req_refl (cf2_tv (cf2_k_step (cf2_titer n mu)) (cf2_k_step (cf2_titer n nu))))
                 (cf2_tv_contraction_eps (cf2_titer n mu) (cf2_titer n nu) eps
                    (cf2_titer_norm n mu Hmu) (cf2_titer_norm n nu Hnu) Heps)).
    + apply (le_trans _
                  (plus (mult cf2_omd
                          (plus (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                                (mult (reqd_nat_to_R n) eps)))
                        eps)).
      * exact (le_plus_compat
                    (mult cf2_omd (cf2_tv (cf2_titer n mu) (cf2_titer n nu)))
                    (mult cf2_omd
                       (plus (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                             (mult (reqd_nat_to_R n) eps)))
                    eps eps
                    (req_le_mult_compat_r cf2_omd
                       (cf2_tv (cf2_titer n mu) (cf2_titer n nu))
                       (plus (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                             (mult (reqd_nat_to_R n) eps))
                       Hge (IH mu nu eps Hmu Hnu Heps))
                    (le_refl eps)).
      * apply (le_trans _
                      (plus (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                            (plus (mult cf2_omd (mult (reqd_nat_to_R n) eps)) eps))).
        -- exact (lt_le_iff _ _ (inr
                     (req_trans _ _ _
                        (req_plus_compat
                           (mult cf2_omd (plus (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                                               (mult (reqd_nat_to_R n) eps)))
                           (plus (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                                 (mult cf2_omd (mult (reqd_nat_to_R n) eps)))
                           eps eps
                           (distrib cf2_omd
                              (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                              (mult (reqd_nat_to_R n) eps))
                           (req_refl eps))
                        (req_sym _ _
                           (plus_assoc (mult cf2_omd
                                          (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                                       (mult cf2_omd (mult (reqd_nat_to_R n) eps))
                                       eps))))).
        -- exact (le_id_r
             (plus (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                   (plus (mult cf2_omd (mult (reqd_nat_to_R n) eps)) eps))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
                   (plus (mult (reqd_nat_to_R n) eps) eps))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
                   (mult (reqd_nat_to_R (Datatypes.S n)) eps))
             (req_plus_compat (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
                (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
                (plus (mult (reqd_nat_to_R n) eps) eps)
                (mult (reqd_nat_to_R (Datatypes.S n)) eps)
                (req_refl (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu)))
                (req_trans _ _ _
                   (req_plus_compat (mult (reqd_nat_to_R n) eps)
                      (mult eps (reqd_nat_to_R n))
                      eps (mult eps one)
                      (mult_comm (reqd_nat_to_R n) eps)
                      (req_sym _ _ (mult_one eps)))
                   (req_trans _ _ _
                      (plus_comm (mult eps (reqd_nat_to_R n)) (mult eps one))
                      (req_trans _ _ _
                         (req_sym _ _ (distrib eps one (reqd_nat_to_R n)))
                         (mult_comm eps (plus one (reqd_nat_to_R n)))))))
             (le_plus_compat
                (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
                (plus (mult cf2_omd (mult (reqd_nat_to_R n) eps)) eps)
                (plus (mult (reqd_nat_to_R n) eps) eps)
                (lt_le_iff _ _ (inr HXS))
                (le_plus_compat
                   (mult cf2_omd (mult (reqd_nat_to_R n) eps))
                   (mult (reqd_nat_to_R n) eps)
                   eps eps
                   (cf2_le_mult_one cf2_omd (mult (reqd_nat_to_R n) eps) HQ0 cf2_omd_le_one)
                   (le_refl eps)))).
Qed.

Print Assumptions cf2_kernel_nonneg.
Print Assumptions cf2_abs_row_kernel_eps.
Print Assumptions cf2_bs_swap.
Print Assumptions cf2_omd_pos.
Print Assumptions cf2_minorization.
Print Assumptions cf2_r_norm.
Print Assumptions cf2_step_decomp.
Print Assumptions cf2_k_step_norm.
Print Assumptions cf2_titer_norm.
Print Assumptions cf2_tv_contraction_eps.

(* ============ F22·G4 证据追加：全件 Closed（前提=显式证书参数） ============ *)
Print Assumptions cf2_kernel_nonneg.
Print Assumptions cf2_abs_row_kernel_eps.
Print Assumptions cf2_bs_swap.
Print Assumptions cf2_omd_pos.
Print Assumptions cf2_minorization.
Print Assumptions cf2_r_norm.
Print Assumptions cf2_step_decomp.
Print Assumptions cf2_k_step_norm.
Print Assumptions cf2_titer_norm.
Print Assumptions cf2_tv_contraction_eps.
Print Assumptions cf2_tv_contraction_eps.

Print Assumptions cf2_tv_iter_eps.