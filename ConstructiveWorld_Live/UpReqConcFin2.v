(* ==========================================================================)
   UpReqConcFin2.v — 二态 bool 世界上的 TV 收缩与显式混合时间
   使命: Fin2World 节：bool 载体世界、TV 距离（cf2_tv_pos/nonneg）、核正性与 bs_swap、Doeblin 分解（cf2_minorization）、单步/迭代 TV 收缩逐 eps 形，至主定理 cf2_mixing_time_le（显式混合时间上界）及其 general 形（任意归一化分布对）。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、UpReqDist、UpReqConcSoftmax、UpReqSampling、UpReqConcMixSel、UpReqConcB1、UpReqConcB2、AttnDoeblin；Stdlib List、QArith、Lia。
   对标: 二态马尔可夫链的总变差收缩率与混合时间显式界（经典 Doeblin 理论）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
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

(* 世界载体：bool（T1 检验结论；论文「Fin n」措辞改注 bool 同构） *)
Definition cf2_world : Set := bool.
Definition cf2_enum2 : list bool := [true; false].

(* 红线②强化项：Not-Prop 的 enum 非空证书——False 消去落 Set 仅此认证形        *)
(* （discriminate 一发；与 cbt_enum_ne 同形，使用面仅 rsq_ 泛型件证书直接代入位）   *)
(* 不可化·判别闭合：discriminate 一发即最短形（Not 非空证书认证形） *)
Lemma cf2_enum_ne : Not ([true; false] = (@nil bool)).
Proof. intro H. discriminate H. Qed.

(* ---- 温度与 Delta（±1 对称 logit 下 max|z| = 1 = Delta，无 +1 松弛） ---- *)

Definition cf2_temp : Real := one.

Lemma cf2_temp_pos : lt zero cf2_temp.
Proof.
  unfold cf2_temp.
  exact one_pos.
Defined.

Definition cf2_Delta : Real := one.

Lemma cf2_Delta_pos : lt zero cf2_Delta.
Proof.
  unfold cf2_Delta.
  exact one_pos.
Defined.

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

(* 不可化·定义性闭合：rsq_bs_list_sum 展开即 req_refl 最短形 *)
Lemma cf2_sum_eq_list : forall g : bool -> Real,
  req (cf2_sumf g) (rsq_bs_list_sum bool g [true; false]).
Proof. intro g. exact (req_refl (rsq_bs_list_sum bool g [true; false])). Defined.

(* ---- 均匀分布 U := 1/2（rsq Unif 同构自持；nR = 2·one 路线） ---- *)

Definition cf2_nR : Real := reqd_nat_to_R (length [true; false]).

(* 不可化·上游认证件直引（reqd_nat_to_R_pos） *)
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

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_Zrow_pos : forall s : bool, lt zero (cf2_Zrow s).
Proof.
  intro s.
  exact (@rsq_bs_Zrow_pos Real RealEnhancedReal bool cf2_sumf [true; false]
            cf2_enum_ne cf2_temp cf2_temp_pos cf2_Delta cf2_z cf2_z_lb
            cf2_sum_eq_list s).
Defined.

(* 核行归一（行和 = one——随机阵面；泛型 rsq_bs_kernel_row 直接代入） *)
(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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
(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_mu0_mass : req (cf2_sumf cf2_mu0) one.
Proof.
  exact (req_trans _ _ _
           (req_plus_compat (cf2_mu0 true) (cf2_mu0 true)
              (plus (cf2_mu0 false) zero) zero
              (req_refl (cf2_mu0 true)) (plus_zero (cf2_mu0 false)))
           (plus_zero (cf2_mu0 true))).
Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* 逐点差和归一：Sigma |mu0 − nu0| = 1 + 1（求和折叠 + plus_zero 衔接） *)
(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* le 一跳（闭合 Htv0 槽 concrete 形——零前件供件） *)
Lemma cf2_tv_nonneg : le zero (cf2_tv cf2_mu0 cf2_nu0).
Proof.
  apply (lt_le_iff zero (cf2_tv cf2_mu0 cf2_nu0)).
  left.
  exact cf2_tv_pos.
Defined.

(* ============================================================ *)
(* T4 前置件：eps 链重述第一段——|Sigma f·r| ≤ Sigma|f|·r + eps（逐 eps 形）      *)
(*   直使用 csm_abs_sum_le_eps；r ≥ 0 前件经 cf2_bs_abs 消解 abs r = r。        *)
(*   （rsq_u_abs_row 使用位 plain 冻结槽的 eps 绕行第一段，AT6 报告 §五轨）      *)
(* ============================================================ *)

(* 字段面 bs_abs 桥（cb1_bs_abs 的语句面同体转换；本件语句全字段名，使用位     *)
(*  零 real_* 面混写——F21 新坑：裸写泛型件头隐实例参成未解 evar 时，real_*      *)
(*  面项转换检查失败，字段面桥接件消解） *)
(* 不可化·上游件直引（cb1_bs_abs） *)
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
(* 自检守卫：±1 对称 z 的数值可见性（G3 辅证；reflexivity 级）                   *)
(*   z(true,·) = +1 ≠ z(false,·) = −1——行间相异，核行真不同的冒烟。             *)
(* ============================================================ *)

(* 不可化·定义性闭合：reflexivity 计算最短形 *)
Lemma cf2_smoke_z_true : projT1 (cf2_z true false) 5%nat == 1%Q.
Proof. reflexivity. Qed.

(* 不可化·定义性闭合：reflexivity 计算最短形 *)
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
(* F22 段：T4 第二段 + T5 eps 链重述                           *)
(*                                                              *)
(* 目标：abs_sum_le plain 槽 ≥2 元 Or 墙（AT5/AT6/AT8 结论）下的                  *)
(*   cmk_attention_mixing_time 使用前置全供给——全链走 csm_abs_sum_le_eps        *)
(*   逐 eps 通路。abs_sum_le 使用位清单逐槽对照（侦察报告 ③风险1）：             *)
(*     ① rsq_u_abs_row        (UpReqSampling L488)  → cf2_abs_row_kernel_eps   *)
(*     ② rsq_bounded_softmax_tv_contraction (L1153) → cf2_tv_contraction_eps    *)
(*     ③ rsq_bounded_softmax_tv_iter        (L1166) → cf2_tv_iter_eps           *)
(*   机器面（rsq_u_* 节件非 abs_sum_le 使用者）全部 @ 全显实例化直供——           *)
(*   「五族主件零改动直使用」判定的逐件验证（T6 前置侦察）。                      *)
(*   F21 卡坑位对照：rsq_ 系 @ 全显（症状一）、req_trans 五参（症状二）、         *)
(*   语句面桥 cf2_bs_abs（症状三）、六层项式逐层配平（症状五）。                  *)
(* ============================================================ *)

(* ---- F22·B0 常数族：lo/delta_star/omd（ReqBoundedSoftmax 节 Let 的出节实例） ---- *)

Definition cf2_invT : Real := inv_pos cf2_temp cf2_temp_pos.
Definition cf2_lo : Real := rsq_exp_pos_fn (mult cf2_invT (opp cf2_Delta)).
Definition cf2_delta_star : Real := mult cf2_lo cf2_lo.
Definition cf2_omd : Real := req_minus one cf2_delta_star.

(* 不可化·接口字段族直引：exp_neg_pos＝S07:8014 字段族（已判定） *)
Lemma cf2_lo_pos : lt zero cf2_lo.
Proof. exact (exp_neg_pos (opp (mult cf2_invT (opp cf2_Delta)))). Defined.

(* 不可化·上游引擎件直引（mult_positive） *)
Lemma cf2_ds_pos : lt zero cf2_delta_star.
Proof. exact (mult_positive cf2_lo cf2_lo cf2_lo_pos cf2_lo_pos). Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_ds_lt_one : lt cf2_delta_star one.
Proof.
  exact (@rsq_bs_delta_star_lt_one Real RealEnhancedReal cf2_temp cf2_temp_pos
           cf2_Delta cf2_Delta_pos).
Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_aux_ds_omd : req (plus cf2_delta_star cf2_omd) one.
Proof. exact (@aux_delta_plus_omd Real RealEnhancedReal cf2_delta_star). Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_omd_pos : lt zero cf2_omd.
Proof.
  exact (@rsq_u_omd_pos_next Real RealEnhancedReal cf2_delta_star cf2_ds_lt_one
           real_lt_plus_compat_lt_le).
Defined.

Lemma cf2_omd_nonneg : le zero cf2_omd.
Proof.
  apply (lt_le_iff zero cf2_omd).
  left.
  exact cf2_omd_pos.
Defined.

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

(* c ≤ 1 与 e ≥ 0 下的 omd·e ≤ e 族用尾件（本段三处使用） *)
Lemma cf2_mult_one_l : forall a : Real, req (mult one a) a.
Proof.
  intro a.
  apply (req_trans (mult one a) (mult a one) a).
  - apply mult_comm.
  - apply mult_one.
Defined.

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
(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* Σ(f−g) = Σf − Σg（Hd 链使用；reqd_sum_minus 的 bool 2 元实例） *)
Definition cf2_sum_minus : forall f g : bool -> Real,
  req (cf2_sumf (fun s : bool => req_minus (f s) (g s)))
      (req_minus (cf2_sumf f) (cf2_sumf g)) :=
  reqd_sum_minus bool cf2_sumf (csm_sum_ext bool [true; false])
    (csm_sum_add bool [true; false]) (csm_sum_linear bool [true; false]).

(* ---- F22·T4-2a：核正性/非负 + abs_row 使用位①的核行 eps 供给 ---- *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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
  apply (lt_le_iff zero (cf2_kernel s s')).
  left.
  exact (cf2_kernel_pos s s').
Defined.

(* 使用位①（rsq_u_abs_row L488 同位）eps 形：核行内 r 不提出（与 rsq_u_abs_row *)
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

(* ---- F22·T4-2b：bs_swap 槽供给（2 元四项和的直接换序；req_plus_exchange 闭合） ---- *)

(* 不可化·上游件直引（cb1_swap_lists） *)
Lemma cf2_bs_swap : forall f : bool -> bool -> Real,
  req (cf2_sumf (fun s : bool => cf2_sumf (fun s' : bool => f s s')))
      (cf2_sumf (fun s' : bool => cf2_sumf (fun s : bool => f s s'))).
Proof.
  intro f.
  exact (cb1_swap_lists bool f [true; false] [true; false]).
Defined.

(* ---- F22·T5 机器面：Doeblin 分解机器 @ 全显实例化（五族主件直使用验证） ---- *)

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

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_r_nonneg : forall s s' : bool, le zero (cf2_r_kernel s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg Real RealEnhancedReal bool cf2_Unif cf2_delta_star
            cf2_ds_lt_one cf2_kernel cf2_minorization
            real_lt_plus_compat_lt_le s s').
Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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


(* ---- F22·T4-2 追加：abs_row 供给引理按权重函数泛型化——使用位的核/Р 核各一行 ----
   （hang 根因坑：按 kernel 实例化的供给引理喂 r_kernel 槽，单化器在双核塔间
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

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_abs_row_r_kernel_eps : forall (f : bool -> Real) (s' : bool) (eps : Real),
  lt zero eps ->
  le (abs (cf2_sumf (fun s : bool => mult (f s) (cf2_r_kernel s s'))))
     (plus (cf2_sumf (fun s : bool => mult (abs (f s)) (cf2_r_kernel s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (cf2_abs_row_gen_eps cf2_r_kernel f s' eps
           (fun s : bool => cf2_r_nonneg s s') Heps).
Defined.
(* ---- F22·T5a：使用位②——单步 TV 收缩逐 eps 形（L499-650 同构重走） ---- *)
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

(* ---- F22·T5b：使用位③——迭代 TV 收缩逐 eps 形（slack 线性累积 + 尾预算） ---- *)

Lemma cf2_titer_norm : forall (n : nat) (mu : bool -> Real),
  req (cf2_sumf mu) one -> req (cf2_sumf (cf2_titer n mu)) one.
Proof.
  intro n. induction n as [| n IH]; intros mu H.
  - exact H.
  - exact (cf2_k_step_norm (cf2_titer n mu) (IH mu H)).
Defined.

(* nR·(S k) 换形：mult (reqd_nat_to_R (S k)) e = e + mult (reqd_nat_to_R k) e *)
(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
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

(* ============================================================ *)
(* F67 段：T6 混合链 + T7 显式混合时间定理（主定理）        *)
(*                                                              *)
(* 使用面：T4 常数族（cf2_omd=1−δ*、cf2_ds_pos、cf2_omd_le_one）+        *)
(*   T5 逐 eps 收缩/迭代件（cf2_tv_contraction_eps/cf2_tv_iter_eps）。   *)
(* T6：点质量对（cf2_mu0/cf2_nu0）n 步 TV 界——TV_k ≤ （1−δ*）^n·TV₀ +      *)
(*   n·eps（照 T5 iter 形）；δ* > 0 证书链 = cf2_kernel_pos/nonneg →       *)
(*   rsq_bs_minorization → δ*=lo²>0（cf2_ds_pos）→ omd∈[0,1)。          *)
(* T7：forall budget>0, sigT k, TV(cf2 迭代 k) < budget——非退化实例的    *)
(*   实质混合界（对照 B2 单点平凡性 §6.4；§10.2 第 9 项兑现件）。         *)
(*   前件诚实申报（逐条列，禁藏）：                                      *)
(*   ① lt zero budget——预算为正；                                       *)
(*   ② 几何衰减前提（显式参）：omd^{k0}·TV₀ ≤ B/2（_le 形）/ < B/2        *)
(*      （plain 形）——本件不进 real_arch And-Prop 支（红线①），故        *)
(*      「衰减达半预算」不作隐藏断言而作显式前提逐条申报；               *)
(*   ③ 归一化前提由已绿件 cf2_mu0_mass/cf2_nu0_mass 消解，零隐藏。       *)
(*   见证：k := S k0；eps := (1/nR_{S k0})·(B/2)（plain）/(B/4)（_le 形），*)
(*   nR·eps =req= B/2 / B/4 精确找零（inv_pos_correct + mult_one）。     *)
(* ============================================================ *)

(* ---- F67·帮件一：lt/le 混合加法桥（real_lt_plus_compat_lt_le 字段面桥） ---- *)

(* 不可化·上游 Real 层引擎件直引：S07:6118 十一段体，接口面字段名映射另批评估 *)
Lemma cf2_lt_plus_compat_lt_le : forall a b c d : Real,
  lt a b -> le c d -> lt (plus a c) (plus b d).
Proof. exact real_lt_plus_compat_lt_le. Defined.

(* ---- F67·帮件二：1/2 < 1（常数严格序；2·(1/2)=1 反用 lt_mult_compat） ---- *)

Lemma cf2_inv2_lt_one : lt cf2_inv_two one.
Proof.
  assert (H21 : lt one (plus one one)).
  { exact (lt_id_l one (plus zero one) (plus one one)
             (req_sym _ _ (req_trans _ _ _ (plus_comm zero one) (plus_zero one)))
             (cf2_lt_plus_compat_lt_le zero one one one one_pos (le_refl one))). }
  exact (lt_id_r cf2_inv_two (mult (plus one one) cf2_inv_two) one
           (inv_pos_correct (plus one one) req_two_pos)
           (lt_id_l cf2_inv_two (mult one cf2_inv_two)
              (mult (plus one one) cf2_inv_two)
              (req_sym _ _ (cf2_mult_one_l cf2_inv_two))
              (lt_mult_compat one (plus one one) cf2_inv_two
                 (inv_pos_pos (plus one one) req_two_pos) H21))).
Defined.

(* ---- F67·帮件三：1/2 + 1/2 = 1 与 B/2 + B/2 = B（终局找零） ---- *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_inv2_sum : req (plus cf2_inv_two cf2_inv_two) one.
Proof.
  exact (req_trans _ _ _
           (req_plus_compat cf2_inv_two (mult cf2_inv_two one)
                            cf2_inv_two (mult cf2_inv_two one)
              (req_sym _ _ (mult_one cf2_inv_two))
              (req_sym _ _ (mult_one cf2_inv_two)))
           (req_trans _ _ _
              (req_sym _ _ (distrib cf2_inv_two one one))
              (req_trans _ _ _
                 (mult_comm cf2_inv_two (plus one one))
                 (inv_pos_correct (plus one one) req_two_pos)))).
Defined.

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_two_inv_budget : forall b : Real,
  req (plus (mult cf2_inv_two b) (mult cf2_inv_two b)) b.
Proof.
  intro b.
  exact (req_trans _ _ _
           (req_plus_compat (mult cf2_inv_two b) (mult b cf2_inv_two)
                            (mult cf2_inv_two b) (mult b cf2_inv_two)
              (mult_comm cf2_inv_two b) (mult_comm cf2_inv_two b))
           (req_trans _ _ _
              (req_sym _ _ (distrib b cf2_inv_two cf2_inv_two))
              (req_trans _ _ _
                 (mult_comm b (plus cf2_inv_two cf2_inv_two))
                 (req_trans _ _ _
                    (req_mult_compat (plus cf2_inv_two cf2_inv_two) one b b
                       cf2_inv2_sum (req_refl b))
                    (cf2_mult_one_l b))))).
Defined.

(* ---- F67·帮件四：nR_{S k}·((1/nR_{S k})·c) = c（eps 预算精确找零） ---- *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Lemma cf2_inv_cancel : forall (c : Real) (k0 : nat),
  req (mult (reqd_nat_to_R (Datatypes.S k0))
            (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0)) c))
      c.
Proof.
  intros c k0.
  exact (req_trans _ _ _
           (mult_assoc (reqd_nat_to_R (Datatypes.S k0))
              (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0)) c)
           (req_trans _ _ _
              (req_mult_compat (mult (reqd_nat_to_R (Datatypes.S k0))
                                   (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                                           (reqd_nat_to_R_pos k0)))
                              one c c
                              (inv_pos_correct (reqd_nat_to_R (Datatypes.S k0))
                                 (reqd_nat_to_R_pos k0))
                              (req_refl c))
              (cf2_mult_one_l c))).
Defined.

(* ---- F67·帮件五：omd^n·TV₀ ≥ 0（非负幂；req_le_mult_compat_r 逐级） ---- *)

Lemma cf2_pow_tv_nonneg : forall n : nat,
  le zero (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0)).
Proof.
  intro n. induction n as [| n IH].
  - exact (le_id_r zero (cf2_tv cf2_mu0 cf2_nu0)
             (mult (req_r_pow cf2_omd 0%nat) (cf2_tv cf2_mu0 cf2_nu0))
             (req_sym _ _ (cf2_mult_one_l (cf2_tv cf2_mu0 cf2_nu0)))
             cf2_tv_nonneg).
  - exact (le_id_r zero
             (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0)))
             (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv cf2_mu0 cf2_nu0))
             (req_trans _ _ _
                (mult_assoc cf2_omd (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0))
                (req_refl (mult (req_r_pow cf2_omd (Datatypes.S n))
                                (cf2_tv cf2_mu0 cf2_nu0))))
             (le_id_l zero (mult cf2_omd zero)
                (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0)))
                (req_sym _ _ (mult_zero cf2_omd))
                (req_le_mult_compat_r cf2_omd zero
                   (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0))
                   cf2_omd_nonneg IH))).
Defined.

(* ---- F67·T6 证书件：omd + δ* = 1（（1−δ*） 读法显式化；δ* > 0 = cf2_ds_pos） ---- *)

Lemma cf2_omd_form : req (plus cf2_omd cf2_delta_star) one.
Proof.
  apply (req_trans (plus cf2_omd cf2_delta_star)
                   (plus cf2_delta_star cf2_omd) one).
  - apply plus_comm.
  - exact cf2_aux_ds_omd.
Defined.

(* ---- F67·T6 主件：点质量对 n 步 TV 界（T5 iter 件的归一化对实例化） ----
   TV(titer n mu0, titer n nu0) ≤ （1−δ*）^n·TV₀ + n·eps；
   δ* > 0 由 cf2_ds_pos 供给（其上游 = cf2_kernel_pos/nonneg 证书链）。 *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Theorem cf2_tv_iter_mu0 : forall (n : nat) (eps : Real),
  lt zero eps ->
  le (cf2_tv (cf2_titer n cf2_mu0) (cf2_titer n cf2_nu0))
     (plus (mult (req_r_pow cf2_omd n) (cf2_tv cf2_mu0 cf2_nu0))
           (mult (reqd_nat_to_R n) eps)).
Proof.
  intros n eps Heps.
  exact (cf2_tv_iter_eps n cf2_mu0 cf2_nu0 eps cf2_mu0_mass cf2_nu0_mass Heps).
Defined.

(* ---- F67·T7 主定理（_le 形）：显式混合时间定理 ----
   前件（诚实申报）：①lt zero budget；②几何衰减前提（显式参）
   omd^{k0}·TV₀ ≤ B/2。见证 k := S k0，eps := (1/nR_{S k0})·(B/4)：
   TV_k ≤ omd^{S k0}·TV₀ + B/4 ≤ B/2 + B/4 < B/2 + B/2 = B。 *)

Theorem cf2_mixing_time_le : forall (budget : Real) (k0 : nat),
  lt zero budget ->
  le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 HB Hgeo.
  assert (HX0 : lt zero (mult cf2_inv_two budget)).
  { exact (mult_positive cf2_inv_two budget
             (inv_pos_pos (plus one one) req_two_pos) HB). }
  assert (HY0 : lt zero (mult cf2_inv_two (mult cf2_inv_two budget))).
  { exact (mult_positive cf2_inv_two (mult cf2_inv_two budget)
             (inv_pos_pos (plus one one) req_two_pos) HX0). }
  assert (HYX : lt (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult cf2_inv_two budget)).
  { exact (lt_id_r (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult one (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (cf2_mult_one_l (mult cf2_inv_two budget))
             (lt_mult_compat cf2_inv_two one (mult cf2_inv_two budget)
                HX0 cf2_inv2_lt_one)). }
  assert (HepsQ : lt zero
             (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (mult_positive
             (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (inv_pos_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
             HY0). }
  assert (Hiter : le
             (cf2_tv (cf2_titer (Datatypes.S k0) cf2_mu0)
                     (cf2_titer (Datatypes.S k0) cf2_nu0))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (le_id_r
             (cf2_tv (cf2_titer (Datatypes.S k0) cf2_mu0)
                     (cf2_titer (Datatypes.S k0) cf2_nu0))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult (reqd_nat_to_R (Datatypes.S k0))
                      (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                                     (reqd_nat_to_R_pos k0))
                            (mult cf2_inv_two (mult cf2_inv_two budget)))))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (req_plus_compat
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv cf2_mu0 cf2_nu0))
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv cf2_mu0 cf2_nu0))
                (mult (reqd_nat_to_R (Datatypes.S k0))
                   (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                                  (reqd_nat_to_R_pos k0))
                         (mult cf2_inv_two (mult cf2_inv_two budget))))
                (mult cf2_inv_two (mult cf2_inv_two budget))
                (req_refl (mult (req_r_pow cf2_omd (Datatypes.S k0))
                                (cf2_tv cf2_mu0 cf2_nu0)))
                (cf2_inv_cancel (mult cf2_inv_two (mult cf2_inv_two budget)) k0))
             (cf2_tv_iter_eps (Datatypes.S k0) cf2_mu0 cf2_nu0
                (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                               (reqd_nat_to_R_pos k0))
                      (mult cf2_inv_two (mult cf2_inv_two budget)))
                cf2_mu0_mass cf2_nu0_mass HepsQ)). }
  assert (Hshrink : le (mult (req_r_pow cf2_omd (Datatypes.S k0))
                             (cf2_tv cf2_mu0 cf2_nu0))
                      (mult cf2_inv_two budget)).
  { exact (le_trans
             (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv cf2_mu0 cf2_nu0))
             (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
             (mult cf2_inv_two budget)
             (le_id_l
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv cf2_mu0 cf2_nu0))
                (mult cf2_omd (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0)))
                (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
                (req_sym _ _
                   (mult_assoc cf2_omd (req_r_pow cf2_omd k0)
                      (cf2_tv cf2_mu0 cf2_nu0)))
                (cf2_le_mult_one cf2_omd
                   (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
                   (cf2_pow_tv_nonneg k0) cf2_omd_le_one))
             Hgeo). }
  assert (Hcomb : lt
             (plus (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0)))
             (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))).
  { exact (cf2_lt_plus_compat_lt_le
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv cf2_mu0 cf2_nu0))
             (mult cf2_inv_two budget)
             HYX Hshrink). }
  assert (Hfinal : lt
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             budget).
  { exact (lt_id_r
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))
             budget
             (cf2_two_inv_budget budget)
             (lt_id_l
                (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                            (cf2_tv cf2_mu0 cf2_nu0))
                      (mult cf2_inv_two (mult cf2_inv_two budget)))
                (plus (mult cf2_inv_two (mult cf2_inv_two budget))
                      (mult (req_r_pow cf2_omd (Datatypes.S k0))
                            (cf2_tv cf2_mu0 cf2_nu0)))
                (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))
                (plus_comm
                   (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
                Hcomb)). }
  exact (existT (fun k : nat =>
            lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget)
           (Datatypes.S k0)
           (le_lt_trans
              (cf2_tv (cf2_titer (Datatypes.S k0) cf2_mu0)
                      (cf2_titer (Datatypes.S k0) cf2_nu0))
              (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                          (cf2_tv cf2_mu0 cf2_nu0))
                    (mult cf2_inv_two (mult cf2_inv_two budget)))
              budget
              Hiter Hfinal)).
Defined.

(* ---- F67·T7 主定理（plain 形）：衰减前提取严格形，_le 形一跳直推 ---- *)

Theorem cf2_mixing_time : forall (budget : Real) (k0 : nat),
  lt zero budget ->
  lt (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 HB Hgeo.
  apply (cf2_mixing_time_le budget k0 HB).
  apply (lt_le_iff (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
                   (mult cf2_inv_two budget)).
  left.
  exact Hgeo.
Defined.

(* ============ F67·G4 证据：新件全 Closed（前提=显式证书参） ============ *)

Print Assumptions cf2_lt_plus_compat_lt_le.
Print Assumptions cf2_inv2_lt_one.
Print Assumptions cf2_inv2_sum.
Print Assumptions cf2_two_inv_budget.
Print Assumptions cf2_inv_cancel.
Print Assumptions cf2_pow_tv_nonneg.
Print Assumptions cf2_omd_form.
Print Assumptions cf2_tv_iter_mu0.
Print Assumptions cf2_mixing_time_le.
Print Assumptions cf2_mixing_time.
(* ============================================================ *)
(* T7 general 续作——任意归一化分布对的混合时间           *)
(*                                                              *)
(* 使用面：T5 iter 件（cf2_tv_iter_eps 本就 general 于 mu/nu，归一化双槽显式）  *)
(*   + 主定理 cf2_mixing_time_le 的装配配方（常数族/找零链全 generic）。     *)
(* 泛化口径（同泛化前件口径，逐条列明）：                                *)
(*   ① 归一化前提：req (cf2_sumf mu) one 与 req (cf2_sumf nu) one 显式双槽，   *)
(*      点质量对实例位由 cf2_mu0_mass/cf2_nu0_mass 供给；                     *)
(*   ② TV₀ 非负槽：le zero (cf2_tv mu nu) 显式前件——setoid 接口 abs_nonneg    *)
(*      已 eps 化（UpReqAlgebra L920 注记：plain 形不设），不可凭空构造，      *)
(*      照实携带；点质量对实例位由已绿 cf2_tv_nonneg 供给。2 元世界非退化性    *)
(*      由 cf2_tv_pos（点质量对）分列陈述，本 general 件不重复申报；           *)
(*   ③ 预算为正 + 几何衰减前提（显式参 k0）：同上件口径。                   *)
(* 见证：k := S k0；eps := （1/nR_{S k0}）·（B/4）；链：                        *)
(*   TV_{S k0} ≤ omd^{S k0}·TV₀ + B/4 ≤ B/2 + B/4 < B/2 + B/2 = B。          *)
(* ============================================================ *)

(* ---- 泛化帮件：omd 幂·TV₀ ≥ 0 泛化形（TV₀ 非负槽显式前件，逐级归纳同前件） ---- *)

Lemma cf2_pow_tv_nonneg_gen : forall (n : nat) (mu nu : bool -> Real),
  le zero (cf2_tv mu nu) ->
  le zero (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)).
Proof.
  intros n mu nu Hnn.
  induction n as [| n IH].
  - exact (le_id_r zero (cf2_tv mu nu)
             (mult (req_r_pow cf2_omd 0%nat) (cf2_tv mu nu))
             (req_sym _ _ (cf2_mult_one_l (cf2_tv mu nu)))
             Hnn).
  - exact (le_id_r zero
             (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
             (mult (req_r_pow cf2_omd (Datatypes.S n)) (cf2_tv mu nu))
             (req_trans _ _ _
                (mult_assoc cf2_omd (req_r_pow cf2_omd n) (cf2_tv mu nu))
                (req_refl (mult (req_r_pow cf2_omd (Datatypes.S n))
                                (cf2_tv mu nu))))
             (le_id_l zero (mult cf2_omd zero)
                (mult cf2_omd (mult (req_r_pow cf2_omd n) (cf2_tv mu nu)))
                (req_sym _ _ (mult_zero cf2_omd))
                (req_le_mult_compat_r cf2_omd zero
                   (mult (req_r_pow cf2_omd n) (cf2_tv mu nu))
                   cf2_omd_nonneg IH))).
Defined.

(* ---- T7 general（_le 形）续：任意归一化对的显式混合时间定理 ----
   前件（诚实申报）：归一化双槽 + TV₀ 非负槽 + ①lt zero budget；
   ②几何衰减前提（显式参）omd^{k0}·TV₀ ≤ B/2。见证 k := S k0，
   eps := （1/nR_{S k0}）·（B/4）：
   TV_k ≤ omd^{S k0}·TV₀ + B/4 ≤ B/2 + B/4 < B/2 + B/2 = B。 *)

Theorem cf2_mixing_time_le_gen : forall (mu nu : bool -> Real) (budget : Real) (k0 : nat),
  req (cf2_sumf mu) one ->
  req (cf2_sumf nu) one ->
  le zero (cf2_tv mu nu) ->
  lt zero budget ->
  le (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k mu) (cf2_titer k nu)) budget).
Proof.
  intros mu nu budget k0 Hmu Hnu Hnn HB Hgeo.
  assert (HX0 : lt zero (mult cf2_inv_two budget)).
  { exact (mult_positive cf2_inv_two budget
             (inv_pos_pos (plus one one) req_two_pos) HB). }
  assert (HY0 : lt zero (mult cf2_inv_two (mult cf2_inv_two budget))).
  { exact (mult_positive cf2_inv_two (mult cf2_inv_two budget)
             (inv_pos_pos (plus one one) req_two_pos) HX0). }
  assert (HYX : lt (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult cf2_inv_two budget)).
  { exact (lt_id_r (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult one (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (cf2_mult_one_l (mult cf2_inv_two budget))
             (lt_mult_compat cf2_inv_two one (mult cf2_inv_two budget)
                HX0 cf2_inv2_lt_one)). }
  assert (HepsQ : lt zero
             (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (mult_positive
             (inv_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (inv_pos_pos (reqd_nat_to_R (Datatypes.S k0)) (reqd_nat_to_R_pos k0))
             HY0). }
  assert (Hiter : le
             (cf2_tv (cf2_titer (Datatypes.S k0) mu)
                     (cf2_titer (Datatypes.S k0) nu))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))).
  { exact (le_id_r
             (cf2_tv (cf2_titer (Datatypes.S k0) mu)
                     (cf2_titer (Datatypes.S k0) nu))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult (reqd_nat_to_R (Datatypes.S k0))
                      (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                                     (reqd_nat_to_R_pos k0))
                            (mult cf2_inv_two (mult cf2_inv_two budget)))))
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (req_plus_compat
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv mu nu))
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv mu nu))
                (mult (reqd_nat_to_R (Datatypes.S k0))
                   (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                                  (reqd_nat_to_R_pos k0))
                         (mult cf2_inv_two (mult cf2_inv_two budget))))
                (mult cf2_inv_two (mult cf2_inv_two budget))
                (req_refl (mult (req_r_pow cf2_omd (Datatypes.S k0))
                                (cf2_tv mu nu)))
                (cf2_inv_cancel (mult cf2_inv_two (mult cf2_inv_two budget)) k0))
             (cf2_tv_iter_eps (Datatypes.S k0) mu nu
                (mult (inv_pos (reqd_nat_to_R (Datatypes.S k0))
                               (reqd_nat_to_R_pos k0))
                      (mult cf2_inv_two (mult cf2_inv_two budget)))
                Hmu Hnu HepsQ)). }
  assert (Hshrink : le (mult (req_r_pow cf2_omd (Datatypes.S k0))
                             (cf2_tv mu nu))
                      (mult cf2_inv_two budget)).
  { exact (le_trans
             (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv mu nu))
             (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu))
             (mult cf2_inv_two budget)
             (le_id_l
                (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv mu nu))
                (mult cf2_omd (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu)))
                (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu))
                (req_sym _ _
                   (mult_assoc cf2_omd (req_r_pow cf2_omd k0)
                      (cf2_tv mu nu)))
                (cf2_le_mult_one cf2_omd
                   (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu))
                   (cf2_pow_tv_nonneg_gen k0 mu nu Hnn) cf2_omd_le_one))
             Hgeo). }
  assert (Hcomb : lt
             (plus (mult cf2_inv_two (mult cf2_inv_two budget))
                   (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu)))
             (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))).
  { exact (cf2_lt_plus_compat_lt_le
             (mult cf2_inv_two (mult cf2_inv_two budget))
             (mult cf2_inv_two budget)
             (mult (req_r_pow cf2_omd (Datatypes.S k0)) (cf2_tv mu nu))
             (mult cf2_inv_two budget)
             HYX Hshrink). }
  assert (Hfinal : lt
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             budget).
  { exact (lt_id_r
             (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
             (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))
             budget
             (cf2_two_inv_budget budget)
             (lt_id_l
                (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                            (cf2_tv mu nu))
                      (mult cf2_inv_two (mult cf2_inv_two budget)))
                (plus (mult cf2_inv_two (mult cf2_inv_two budget))
                      (mult (req_r_pow cf2_omd (Datatypes.S k0))
                            (cf2_tv mu nu)))
                (plus (mult cf2_inv_two budget) (mult cf2_inv_two budget))
                (plus_comm
                   (mult (req_r_pow cf2_omd (Datatypes.S k0))
                         (cf2_tv mu nu))
                   (mult cf2_inv_two (mult cf2_inv_two budget)))
                Hcomb)). }
  exact (existT (fun k : nat =>
            lt (cf2_tv (cf2_titer k mu) (cf2_titer k nu)) budget)
           (Datatypes.S k0)
           (le_lt_trans
              (cf2_tv (cf2_titer (Datatypes.S k0) mu)
                      (cf2_titer (Datatypes.S k0) nu))
              (plus (mult (req_r_pow cf2_omd (Datatypes.S k0))
                          (cf2_tv mu nu))
                    (mult cf2_inv_two (mult cf2_inv_two budget)))
              budget
              Hiter Hfinal)).
Defined.

(* ---- T7 general（plain 形）续：衰减前提取严格形，_le 形一跳直推 ---- *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Theorem cf2_mixing_time_gen : forall (mu nu : bool -> Real) (budget : Real) (k0 : nat),
  req (cf2_sumf mu) one ->
  req (cf2_sumf nu) one ->
  le zero (cf2_tv mu nu) ->
  lt zero budget ->
  lt (mult (req_r_pow cf2_omd k0) (cf2_tv mu nu))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k mu) (cf2_titer k nu)) budget).
Proof.
  intros mu nu budget k0 Hmu Hnu Hnn HB Hgeo.
  exact (cf2_mixing_time_le_gen mu nu budget k0 Hmu Hnu Hnn HB
           (lt_le_iff _ _ (inl Hgeo))).
Defined.

(* ---- 收尾件：点质量对主定理 = general 件实例（泛化装配自证封闭） ----
   cf2_tv_pos 非退化判据分列在案：本件仅证 general 装配在点质量对位退化回
   同主定理 cf2_mixing_time_le 结论。 *)

(* 不可化·单跳直引：上游 @-call／同件已证件转发，内联须整体迁移上游归纳体，另批评估 *)
Theorem cf2_mixing_time_le_ptmass : forall (budget : Real) (k0 : nat),
  lt zero budget ->
  le (mult (req_r_pow cf2_omd k0) (cf2_tv cf2_mu0 cf2_nu0))
     (mult cf2_inv_two budget) ->
  sigT (fun k : nat =>
        lt (cf2_tv (cf2_titer k cf2_mu0) (cf2_titer k cf2_nu0)) budget).
Proof.
  intros budget k0 HB Hgeo.
  exact (cf2_mixing_time_le_gen cf2_mu0 cf2_nu0 budget k0
           cf2_mu0_mass cf2_nu0_mass cf2_tv_nonneg HB Hgeo).
Defined.

(* ============ G4 证据：新件全 Closed（前提=显式证书参） ============ *)

Print Assumptions cf2_pow_tv_nonneg_gen.
Print Assumptions cf2_mixing_time_le_gen.
Print Assumptions cf2_mixing_time_gen.
Print Assumptions cf2_mixing_time_le_ptmass.
