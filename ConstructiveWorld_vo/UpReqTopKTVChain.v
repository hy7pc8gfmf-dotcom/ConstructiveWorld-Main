(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqTopKTVChain.v *)
(* *)
(* 目的： 定理 7.6 topk_tv_identity 的 Real 层构造。 *)
(* 主件： rtk_kept_plus_tail_full 保持-尾部分解与 rtk2_* 链节。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： Boltzmann 因子与配分正性为接口前提；保持质量与尾部质量的恒等式为主件。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqTopKTVChain.v —— 定理 7.6 topk_tv_identity（前半段） *)
(*   Real 层平移·前半段（Id 层 19 引理链前 10 件）      *)
(* ------------------------------------------------------------------ *)
(* 【使命】定理 7.6 topk_tv_identity_strict（论文2 P2 项 9）：        *)
(*   TV(boltzmann, topk 重归一) == tail_mass / Z_thermo（精确恒等）。  *)
(*   Id 层全部通过（S06 Section AttentionGibbsBridge @5554-5886，19 引理   *)
(*   四段组装）；req 对位 ag_topk_tv_identity_strict 已结果            *)
(*   UpReqAttnGibbs.v @1721（Print Assumptions 闭）；Real 层平移未做   *)
(*   （附录 B L1387「Real 层 TV 恒等未复刻，grep 无命中」）。          *)
(*   本件 = Id 原件顺序前 10 件的 real_eq / real_le / real_lt 载体     *)
(*   平移（kept 家 6 件 + _cc 符号辅件 4 件）；余件 9 件留后续滚动组。 *)
(* ------------------------------------------------------------------ *)
(* 【Id 锚（S06 模块行号，Live_X 版）】                                *)
(*   定义件：topk_tail_mass @5537 / topk_kept_partition @5541          *)
(*     / topk_renorm @5548（boltzmann 载体 @3840-3845）。              *)
(*   引理件（本件前半段 11 件 = 前 10 件 + _cc 家族收尾件）：           *)
(*     1. boltzmann_factor_pos_attn @5554                              *)
(*     2. topk_kept_term_nonneg @5560                                  *)
(*     3. topk_kept_term_le_factor @5569                               *)
(*     4. topk_kept_plus_tail_full @5578（守恒：kept + tail == Z）     *)
(*     5. topk_kept_le_Zthermo @5603（子集和 ≤ 全和）                  *)
(*     6. topk_inv_Z_le_inv_kept @5611（inv 反序）                     *)
(*     7. inv_one_cc @5620                                             *)
(*     8. opp_zero_cc @5628                                            *)
(*     9. lt_minus_cc @5637                                            *)
(*    10. abs_neg_cc @5647                                             *)
(*    11. minus_zero_cc @5658（_cc 符号辅件家族收尾）                  *)
(*   余件（ 续作清单，8 件，自 TV 点态链起）：                       *)
(*     topk_tv_pointwise_keep @5667 / topk_tv_pointwise_evict @5725    *)
(*     / topk_if_split @5742 / eviction_if_linear_else @5753           *)
(*     / topk_tv_pointwise @5764 / topk_sum_decomp @5780               *)
(*     / topk_sum_collapse @5840 / topk_tv_identity_strict @5886        *)
(*     （主定理）。                                                       *)
(* ------------------------------------------------------------------ *)
(* 【载体选择（req 对位 UpReqAttnGibbs 同轴）】                        *)
(*   Id 固定 keep_dec 的 tail/kept 家统一为 (k : S -> Set) + kd 可判定  *)
(*   保留集形参（req 版参数化归一登记表同轴，-30294 实例统一）； *)
(*  相等/序载体：real_eq（逐 eps 函数型 Set 值等价，S02 L387）/        *)
(*   real_lt（见证 eps 的 sigT，S02 L456）/ real_le = Or(lt,eq)        *)
(*   （S02 L460）——全 Set 载体，零 Prop 泄露。                         *)
(*   减法载体：real_minus_r a b := real_plus a (real_opp b)            *)
(*   （S12 L13224 顶层，Id minus 同形）。                              *)
(* ------------------------------------------------------------------ *)

(*   求和载体三位为 Real 层平行接口（S08 RealAttnSteady 同位）：        *)
(*     real_sum_over_S       <- Id sum_over_S                          *)
(*     real_sum_over_S_ext   <- Id sum_over_S_ext（件4 使用）          *)
(*     real_sum_over_S_add   <- Id sum_over_S_add（件4 使用）          *)
(*     real_sum_over_S_le    <- Id sum_over_S_le（件5 使用；req 位      *)
(*                                诚实新增先例 UpReqAttnGibbs sum_le）  *)
(*   热力学载体：D/D_pos/energy/Z_thermo_pos 逐位对位 -3845     *)
(*   （boltzmann_factor := exp_neg(inv(D)·energy) 同构副本）。          *)
(*   全件无非推导假设：Print Assumptions 十件全闭（G3 提取检验）。  *)
(* ------------------------------------------------------------------ *)
(* 【使用引用（前置 .vo 直引，零重建）】                                  *)
(*   real_inv_pos/real_inv_pos_correct（S03 L6653/L6722）；             *)
(*   real_inv_pos_le_compat（S07 L6775，inv 反序引擎）；                *)
(*   real_exp_neg_pos（S07 L7765）；real_lt_le_iff_req/real_lt_id_r     *)

(*   real_lt_plus_compat_lt_le（S07 L6109）；real_opp_lt_compat         *)
(*   （S07 L6667）；real_abs_pos_req（S07 L7280）；real_abs_opp         *)
(*   （S03 L6522）；real_opp_zero（S08 L386，件8 直引——        *)
(*   节内自证防前向引用，Real 基座已在盘，直引即诚实）；                *)
(*   real_lt_zero_one（S07 L6928，件7 one 正性 witnesses 位）。         *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（real_eq/real_lt/real_le 全     *)
(*   Set 载体，kd 的 Or/Not 为 Stdlib Set 级析取，req 对位同构）；      *)
(*   real_eq 非 Id 禁改写——全链 real_eq_trans + RealSetoid 运输        *)
(*   （判例 纪律）；全件 Qed 闭合。                                    *)
(* 编译配方：_t16_run.ps1 + cpu_guard（CoreN 3，LoadLimit 65）          *)


(* ============================================================ *)

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

(* ============================================================ *)
(* Section RealTopKTVChain：与 Id AttentionGibbsBridge（topk 段）同构  *)
(* ============================================================ *)
Section RealTopKTVChain.

(* 世界：状态类型（ Context 位副本；Id 经 RealInterface 取 S， *)
(*   Real 层直取 Type 形参——求和载体三位同取抽象位，判例坑2 同款）。 *)
Variable S : Type.


Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) ->
  real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) ->
  real_le (real_sum_over_S f) (real_sum_over_S g).

(* ---- Boltzmann 载体（-3843 逐位副本；req 版 L537-541 同构） ---- *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.

Definition rtk_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

Definition rtk_Z_thermo : Real := real_sum_over_S rtk_boltzmann_factor.

Variable rtk_Z_thermo_pos : real_lt real_zero rtk_Z_thermo.

(* ---- 定义件（/@5541 参数化副本；req 版 tail_mass_of_r 同轴） -- *)
(* Top-K 版尾部质量（Id topk_tail_mass：逐出态质量） *)
Definition rtk_tail_mass
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then real_zero else rtk_boltzmann_factor s).

(* Top-K 版保留质量（Id topk_kept_partition：重归一化分母） *)
Definition rtk_kept_partition
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then rtk_boltzmann_factor s else real_zero).

(* ---- 件1（）：单参 boltzmann 因子正性 ---- *)
(* Id 证明 = exp_neg_pos 直引；Real 层同型（real_exp_neg_pos 引擎位）。 *)
Lemma rtk_boltzmann_factor_pos_attn :
  forall s : S, real_lt real_zero (rtk_boltzmann_factor s).
Proof.
  intro s.
  unfold rtk_boltzmann_factor.
  apply real_exp_neg_pos.
Qed.

(* ---- 件2（）：if 保留项非负（keep 时 > 0，else == 0） ---- *)
Lemma rtk_kept_term_nonneg :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    real_le real_zero (if kd s then rtk_boltzmann_factor s else real_zero).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply (RealSetoid.real_lt_le_iff_req real_zero (rtk_boltzmann_factor s)).
    left. apply rtk_boltzmann_factor_pos_attn.
  - apply real_le_refl.
Qed.

(* ---- 件3（）：if 保留项 ≤ 因子（keep 时自反，else 0 < b） ---- *)
Lemma rtk_kept_term_le_factor :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    real_le (if kd s then rtk_boltzmann_factor s else real_zero)
            (rtk_boltzmann_factor s).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply real_le_refl.
  - apply (RealSetoid.real_lt_le_iff_req real_zero (rtk_boltzmann_factor s)).
    left. apply rtk_boltzmann_factor_pos_attn.
Qed.

(* ---- 件4（）：守恒 kept + tail == Z_thermo ---- *)
(* Id 证明链：逐点 plus 消零（plus_zero 两向）→ 求和外延 → 求和可加；   *)
(* Real 层同构重放（real_eq_trans 链 + ext/add 双肢；判例 纪律）。      *)
Lemma rtk_kept_plus_tail_full :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    real_eq (real_plus (rtk_kept_partition k kd) (rtk_tail_mass k kd))
            rtk_Z_thermo.
Proof.
  intros k kd.
  unfold rtk_kept_partition, rtk_tail_mass, rtk_Z_thermo.
  (* 逐点：保留项 + 尾项 == 因子（keep：b + 0 == b；逐出：0 + b == b） *)
  assert (Hpt : forall s : S,
           real_eq (real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                              (if kd s then real_zero else rtk_boltzmann_factor s))
                   (rtk_boltzmann_factor s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - exact (real_plus_zero (rtk_boltzmann_factor s)).
    - exact (real_eq_trans _ _ _
                (real_plus_comm real_zero (rtk_boltzmann_factor s))
                (real_plus_zero (rtk_boltzmann_factor s))). }
  assert (Hext : real_eq
                   (real_sum_over_S (fun s : S =>
                      real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                                (if kd s then real_zero else rtk_boltzmann_factor s)))
                   (real_sum_over_S (fun s : S => rtk_boltzmann_factor s)))
    by exact (real_sum_over_S_ext _ _ Hpt).
  assert (Hadd : real_eq
                   (real_sum_over_S (fun s : S =>
                      real_plus (if kd s then rtk_boltzmann_factor s else real_zero)
                                (if kd s then real_zero else rtk_boltzmann_factor s)))
                   (real_plus (real_sum_over_S (fun s : S =>
                                  if kd s then rtk_boltzmann_factor s else real_zero))
                              (real_sum_over_S (fun s : S =>
                                  if kd s then real_zero else rtk_boltzmann_factor s))))
    by exact (real_sum_over_S_add _ _).
  exact (real_eq_trans _ _ _ (real_eq_sym _ _ Hadd) Hext).
Qed.

(* ---- 件5（）：kept ≤ Z_thermo（子集和 ≤ 全和） ---- *)
Lemma rtk_kept_le_Zthermo :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    real_le (rtk_kept_partition k kd) rtk_Z_thermo.
Proof.
  intros k kd.
  unfold rtk_kept_partition, rtk_Z_thermo.
  apply real_sum_over_S_le.
  intro s.
  apply rtk_kept_term_le_factor.
Qed.

(* ---- 件6（）：inv 反序 kept ≤ Z ⟹ 1/Z ≤ 1/kept ---- *)
(* 引擎：real_inv_pos_le_compat（S07 L6775；Id inv_pos_le_compat 同位）。 *)
Lemma rtk_inv_Z_le_inv_kept :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk_kept_partition k kd)),
    real_le (real_inv_pos rtk_Z_thermo rtk_Z_thermo_pos)
            (real_inv_pos (rtk_kept_partition k kd) Hkpos).
Proof.
  intros k kd Hkpos.
  exact (real_inv_pos_le_compat (rtk_kept_partition k kd) rtk_Z_thermo
           Hkpos rtk_Z_thermo_pos (rtk_kept_le_Zthermo k kd)).
Qed.

(* ============================================================ *)
(* _cc 符号辅件四件（-@5647；与 topk 载体解耦，纯 Real 代数）  *)
(* ============================================================ *)

(* ---- 件7（）：inv one == one ---- *)
(* Id 证明 = mult_one 对称 → comm → inv_pos_correct；Real 层同链重放。   *)
Lemma rtk_inv_one_cc :
  real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
                       (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)
                       real_one).
  - exact (real_eq_sym _ _ (real_mult_one (real_inv_pos real_one real_lt_zero_one))).
  - apply (real_eq_trans (real_mult (real_inv_pos real_one real_lt_zero_one) real_one)
                         (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                         real_one).
    + exact (real_mult_comm (real_inv_pos real_one real_lt_zero_one) real_one).
    + exact (real_inv_pos_correct real_one real_lt_zero_one).
Qed.

(* ---- 件8（）：opp zero == zero ---- *)
(* Id 节内自证防前向引用；Real 基座 S08 L386 real_opp_zero 已在盘，      *)
(* 直引使用（前置核验引用零重建纪律；检验核验 Closed）。        *)
Lemma rtk_opp_zero_cc : real_eq (real_opp real_zero) real_zero.
Proof.
  exact real_opp_zero.
Qed.

(* ---- 件9（）：a < b ⟹ a − b < 0 ---- *)
(* Id 链：minus 展开 → lt_id_r（b + opp b == 0）→ 混合 plus 兼容；       *)
(* Real 层：real_minus_r 展开 → real_lt_id_r + real_plus_opp 肢          *)
(* + real_lt_plus_compat_lt_le 混合兼容（S07 L6109，req 版假设位          *)
(* req_lt_plus_compat_lt_le_h 的 Real 实例引擎——req 接口无混合字段，     *)
(* Real 层可直接使用，假设位自然消解，见头注 对位）。               *)
Lemma rtk_lt_minus_cc :
  forall a b : Real, real_lt a b -> real_lt (real_minus_r a b) real_zero.
Proof.
  intros a b Hab.
  unfold real_minus_r.
  apply (RealSetoid.real_lt_id_r (real_plus a (real_opp b))                                 (real_plus b (real_opp b)) real_zero                                 (real_plus_opp b)).
  exact (real_lt_plus_compat_lt_le a b (real_opp b) (real_opp b)             Hab (real_le_refl (real_opp b))).
Qed.

(* ---- 件10（）：a < 0 ⟹ |a| == −a ---- *)
(* Id 链：abs_opp 对称 → abs_pos（负支）→ opp 保序换向；                 *)
(* Real 层：real_abs_opp 对称肢 + real_abs_pos_req（负号消去引擎，       *)
(* 施于 −a）+ real_opp_lt_compat 换向（a < 0 ⟹ 0 < −a，经               *)
(* real_opp_zero 换元 real_lt_id_r）。                                   *)
Lemma rtk_abs_neg_cc :
  forall a : Real, real_lt a real_zero -> real_eq (real_abs a) (real_opp a).
Proof.
  intros a Ha.
  apply (real_eq_trans (real_abs a) (real_abs (real_opp a)) (real_opp a)).
  - exact (real_eq_sym _ _ (real_abs_opp a)).
  - apply real_abs_pos_req.
    exact (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp a)
               (real_eq_sym _ _ real_opp_zero)
               (real_opp_lt_compat a real_zero Ha)).
Qed.

(* ---- 件11（，_cc 家族收尾件）：x − 0 == x ---- *)
(* Id 链：minus 展开 → opp zero == zero 换元 → plus_zero；Real 层：     *)
(* real_minus_r 展开 → RealSetoid.real_eq_plus_compat 换右元（opp 0 ≈ 0）*)
(* → real_plus_zero 完成。至此 _cc 符号辅件五件全平移， 自 TV 点态   *)
(* 链（@5667 topk_tv_pointwise_keep）起续。                             *)
Lemma rtk_minus_zero_cc :
  forall x : Real, real_eq (real_minus_r x real_zero) x.
Proof.
  intro x. unfold real_minus_r.
  apply (real_eq_trans _ (real_plus x real_zero)).
  - apply (RealSetoid.real_eq_plus_compat x (real_opp real_zero) x real_zero).
    + apply real_eq_refl.
    + exact real_opp_zero.
  - exact (real_plus_zero x).
Qed.

End RealTopKTVChain.

(* ============================================================ *)
(* 【前半段结果核对（本件 11 引理件 + 5 定义载体，合规验证验证见尾注）】    *)
(*   rtk_boltzmann_factor_pos_attn<-5554  rtk_kept_term_nonneg<-5560    *)
(*   rtk_kept_term_le_factor<-5569        rtk_kept_plus_tail_full<-5578 *)
(*   rtk_kept_le_Zthermo<-5603            rtk_inv_Z_le_inv_kept<-5611   *)
(*   rtk_inv_one_cc<-5620                 rtk_opp_zero_cc<-5628         *)
(*   rtk_lt_minus_cc<-5637                rtk_abs_neg_cc<-5647          *)
(*   rtk_minus_zero_cc<-5658                                            *)
(*   定义载体：rtk_boltzmann_factor<-3840 rtk_Z_thermo<-3843            *)
(*   rtk_tail_mass<-5537                  rtk_kept_partition<-5541      *)
(*   （topk_renorm<-5548 属 TV 链后半段使用面，留  与件 12-19 同批）。 *)
(* 【 续作清单（-@5886，8 件）】                              *)
(*   topk_tv_pointwise_keep<-5667 / topk_tv_pointwise_evict<-5725 /      *)
(*   topk_if_split<-5742 / eviction_if_linear_else<-5753 /               *)
(*   topk_tv_pointwise<-5764 / topk_sum_decomp<-5780 /                   *)
(*   topk_sum_collapse<-5840 / topk_tv_identity_strict<-5886（主定理）。   *)
(*    使用面：本节三求和位 + linear 位（tv 链点态/分解需               *)
(*   real_sum_over_S_linear，Id sum_over_S_linear 字段同位，诚实新增）；  *)
(*   件9 rtk_lt_minus_cc / 件10 rtk_abs_neg_cc / 件11 rtk_minus_zero_cc  *)
(*   为逐点差分解符号肢引擎。                                            *)

(*   G1 禁词 0（自查脚本）；G3 Print Assumptions 十一件全闭               *)
(*   （_t16_g3.v）+ Recursive Extraction 顶级名 Obj.magic=0；             *)

(* ============================================================ *)

(* ============================================================ *)
(* UpReqTopKTVChain.v —— 定理 7.6 topk_tv_identity（后半段） *)
(*   Real 层平移·后半段完成（TV 点态链 8 件 + 主定理闭合） *)
(* ------------------------------------------------------------------ *)

(*   件12 rtk_tv_pointwise_keep       <- S06 5667（keep 分支符号恒等） *)
(*   件13 rtk_tv_pointwise_evict      <- S06 5725（evict |x-0|==x）   *)
(*   件14 rtk_if_split                <- S06 5742（逐点 if 加法分解）  *)
(*   件15 rtk_eviction_if_linear_else <- S06 5753（else 线性对偶）     *)
(*   件16 rtk_tv_pointwise            <- S06 5764（逐点总恒等，条件化）*)
(*   件17 rtk_sum_decomp              <- S06 5780（求和分解）          *)
(*   件18 rtk_sum_collapse            <- S06 5840（完成 2·invZ·T）    *)
(*   件19 rtk_tv_identity_strict      <- S06 5886（主定理 TV==tail/Z）  *)
(* ------------------------------------------------------------------ *)
(* 【新增载体（ 升参名直引，零重建；Id 同位锚见行尾）】              *)
(*   rtk2_bfactor<- rtk_boltzmann_factor  rtk2_Z<-rtk_Z_thermo      *)
(*   rtk2_kept<-rtk_kept_partition @5541  rtk2_tail<-rtk_tail_mass @5537 *)
(*   rtk2_topk_renorm<-S06 5548  rtk2_boltzmann_dist_attn<-S06 3847    *)
(*   rtk2_tv_dist<-S06 4033（inv2 := 1/(1+1)，real_two_pos S08 593）   *)

(*   S01 1402； 头注预留  补位，件17 使用）。辅件两件（使用面）：  *)
(*   rtk_minus_plus_cancel_r_cc（Id minus_plus_cancel_r 副本，件18 使用）*)
(*   rtk_eviction_if_linear<-S06 4653（keep 分支线性，件17 使用）。     *)
(* 【使用引用】 件9 lt_minus_cc/件10 abs_neg_cc/件11 minus_zero_cc    *)
(*   （符号肢引擎）+ 基座：real_distrib S02 2375 / real_distrib_r S09   *)
(*   111 / real_mult_opp_l S08 49 / real_opp_plus S07 7786 /            *)
(*   real_opp_opp S08 95 / real_plus_assoc S02 2333 / real_plus_opp     *)
(*   S02 2345 / real_abs_mult_req S07 7268 / real_abs_eq_compat S08     *)
(*   5112 / real_abs_pos_req S07 7280 / real_mult_positive S07 6960 /   *)
(*   real_inv_pos_pos S03 6771 / real_inv_pos_correct S03 6722。        *)
(* 【红线】纯构造性；Set 层零 Prop 泄露；real_eq 非 Id 禁改写——全链     *)
(*   real_eq_trans 显式端点（ 双卡参序坑：族件 x y 显式首参）；       *)
(*   全件 Qed 闭合。                                                    *)
(* ============================================================ *)

Section RealTopKTVFinish.


Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) ->
  real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).

(* ---- 热力学载体（-3843 逐位对位； 节同形） ---- *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.

(* ---- Boltzmann 载体实例化（ 升参名直引） ---- *)
Definition rtk2_bfactor (s : S) : Real :=
  rtk_boltzmann_factor S D D_pos energy s.

Definition rtk2_Z : Real := rtk_Z_thermo S real_sum_over_S D D_pos energy.

Variable rtk2_Zpos : real_lt real_zero rtk2_Z.

Definition rtk2_invZ : Real := real_inv_pos rtk2_Z rtk2_Zpos.

Definition rtk2_kept (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  rtk_kept_partition S real_sum_over_S D D_pos energy k kd.

Definition rtk2_tail (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  rtk_tail_mass S real_sum_over_S D D_pos energy k kd.

Definition rtk2_invK (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) : Real :=
  real_inv_pos (rtk2_kept k kd) Hkpos.

(* Top-K 重归一化分布 <- S06 5548 *)
Definition rtk2_topk_renorm (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) (s : S) : Real :=
  if kd s then real_mult (rtk2_invK k kd Hkpos) (rtk2_bfactor s) else real_zero.

(* Boltzmann 分布 <- S06 3847 *)
Definition rtk2_boltzmann_dist_attn (s : S) : Real :=
  real_mult rtk2_invZ (rtk2_bfactor s).

(* 总变差距离 <- S06 4033（inv2 := 1/(1+1)） *)
Definition rtk2_tv_dist (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
  (Hkpos : real_lt real_zero (rtk2_kept k kd)) : Real :=
  real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
            (real_sum_over_S (fun s : S =>
               real_abs (real_minus_r (rtk2_boltzmann_dist_attn s)
                                      (rtk2_topk_renorm k kd Hkpos s)))).

(* ============================================================ *)
(* 辅件 A1：x + y − x == y（Id minus_plus_cancel_r 副本；件18 使用）   *)
(* ============================================================ *)
Lemma rtk_minus_plus_cancel_r_cc :
  forall m x : Real,
    real_eq (real_minus_r (real_plus m x) m) x.
Proof.
  intros m x.
  apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply (real_eq_trans _ (real_plus x (real_plus m (real_opp m))) _).
    + apply (real_eq_trans _ (real_plus (real_plus x m) (real_opp m)) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_plus m x) (real_opp m)
                 (real_plus x m) (real_opp m)
                 (real_plus_comm m x) (real_eq_refl (real_opp m))).
      * exact (real_eq_sym _ _ (real_plus_assoc x m (real_opp m))).
    + apply (RealSetoid.real_eq_plus_compat
               x (real_plus m (real_opp m)) x real_zero
               (real_eq_refl x) (real_plus_opp m)).
  - exact (real_plus_zero x).
Qed.

(* ---- 件14（）：逐点 if 加法分解 ---- *)
Lemma rtk_if_split :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (X Y : Real) (s : S),
    real_eq (if kd s then X else Y)
            (real_plus (if kd s then X else real_zero)
                       (if kd s then real_zero else Y)).
Proof.
  intros k kd X Y s. destruct (kd s) as [Hk | Hnk].
  - exact (real_eq_sym _ _ (real_plus_zero X)).
  - exact (real_eq_trans _ _ _ (real_eq_sym _ _ (real_plus_zero Y))
             (real_eq_sym _ _ (real_plus_comm real_zero Y))).
Qed.

(* ---- 辅件 A2（）：keep 分支线性（件17 使用） ---- *)
Lemma rtk_eviction_if_linear :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : Real) (f : S -> Real) (s : S),
    real_eq (if kd s then real_mult a (f s) else real_zero)
            (real_mult a (if kd s then f s else real_zero)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - apply real_eq_refl.
  - exact (real_eq_sym _ _ (real_mult_zero a)).
Qed.

(* ---- 件15（）：else 分支线性（对偶 A2） ---- *)
Lemma rtk_eviction_if_linear_else :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (a : Real) (f : S -> Real) (s : S),
    real_eq (if kd s then real_zero else real_mult a (f s))
            (real_mult a (if kd s then real_zero else f s)).
Proof.
  intros k kd a f s. destruct (kd s) as [Hk | Hnk].
  - exact (real_eq_sym _ _ (real_mult_zero a)).
  - apply real_eq_refl.
Qed.

(* ============================================================ *)
(* 件12（）：keep 分支点态符号恒等                              *)
(*   |b·invZ − invK·b| == b·(invK − invZ)，前提 invZ < invK（严格逐出， *)
(*   Real 层由 T > 0 实例化）；符号肢 =  件9+件10 引擎。             *)
(* ============================================================ *)
Lemma rtk_tv_pointwise_keep :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S)
         (Hk : k s)
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
              (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos) (rtk2_bfactor s))))
            (real_mult (rtk2_bfactor s)
                       (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_inv_pos rtk2_Z rtk2_Zpos))).
Proof.
  intros k kd s Hk Hkpos Hst.
  (* 肢1（提公因子，Id mult_minus_distr_r 反向副本） *)
  assert (Hfac : real_eq
           (real_minus_r (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                         (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos) (rtk2_bfactor s)))
           (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                    (real_inv_pos (rtk2_kept k kd) Hkpos))
                      (rtk2_bfactor s))).
  { apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_opp (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (rtk2_bfactor s)))) _).
    - apply real_eq_refl.
    - apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                          (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_opp (rtk2_bfactor s)))) _).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                 (real_opp (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (rtk2_bfactor s)))
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                 (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                            (real_opp (rtk2_bfactor s)))
                 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
                 (real_eq_sym _ _
                    (real_mult_opp_l (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (rtk2_bfactor s)))).
      + apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                            (real_mult (rtk2_bfactor s)
                                       (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                   (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                              (real_opp (rtk2_bfactor s)))
                   (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                   (real_mult (rtk2_bfactor s)
                              (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                   (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
                   (real_eq_trans _ _ _
                      (real_mult_opp_l (real_inv_pos (rtk2_kept k kd) Hkpos)
                                       (rtk2_bfactor s))
                      (real_eq_trans _ _ _
                         (RealSetoid.real_eq_opp_compat
                            (real_mult (real_inv_pos (rtk2_kept k kd) Hkpos)
                                       (rtk2_bfactor s))
                            (real_mult (rtk2_bfactor s)
                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                            (real_mult_comm (real_inv_pos (rtk2_kept k kd) Hkpos)
                                            (rtk2_bfactor s)))
                         (real_eq_sym _ _
                            (real_mult_opp_l (rtk2_bfactor s)
                                             (real_inv_pos (rtk2_kept k kd) Hkpos)))))).
        * apply (real_eq_trans _ (real_mult (rtk2_bfactor s)
                              (real_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
          -- apply (real_eq_trans _
                      (real_plus (real_mult (rtk2_bfactor s)
                                            (real_inv_pos rtk2_Z rtk2_Zpos))
                                 (real_mult (rtk2_bfactor s)
                                            (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
            ++ apply (RealSetoid.real_eq_plus_compat
                        (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_mult (rtk2_bfactor s)
                                   (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_mult (rtk2_bfactor s) (real_inv_pos rtk2_Z rtk2_Zpos))
                        (real_mult (rtk2_bfactor s)
                                   (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_mult_comm (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                        (real_eq_refl
                           (real_mult (rtk2_bfactor s)
                                      (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos))))).
            ++ exact (real_eq_sym _ _
                         (real_distrib (rtk2_bfactor s) (real_inv_pos rtk2_Z rtk2_Zpos)
                                       (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))).
          -- exact (real_mult_comm (rtk2_bfactor s)
                       (real_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                                  (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))). }
  (* 肢2（|D'·b| == b·|D'|）：real_abs_mult_req + comm + |b|==b *)
  assert (Habs : real_eq
           (real_abs (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))
                                (rtk2_bfactor s)))
           (real_mult (rtk2_bfactor s)
                      (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))))).
  { apply (real_eq_trans _ (real_mult (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (real_inv_pos (rtk2_kept k kd) Hkpos)))
                        (real_abs (rtk2_bfactor s))) _).
    - exact (real_abs_mult_req
               (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                             (real_inv_pos (rtk2_kept k kd) Hkpos))
               (rtk2_bfactor s)).
    - apply (real_eq_trans _ (real_mult (real_abs (rtk2_bfactor s))
                          (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                  (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
      + exact (real_mult_comm
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (real_abs (rtk2_bfactor s))).
      + apply (RealSetoid.real_eq_mult_compat
                 (real_abs (rtk2_bfactor s))
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (rtk2_bfactor s)
                 (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                         (real_inv_pos (rtk2_kept k kd) Hkpos)))
                 (real_abs_pos_req (rtk2_bfactor s)
                    (rtk_boltzmann_factor_pos_attn S D D_pos energy s))
                 (real_eq_refl
                    (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                            (real_inv_pos (rtk2_kept k kd) Hkpos))))). }
  (* 肢3（符号，前提 invZ < invK）： 件9+件10 引擎 *)
  assert (Hsign : real_eq
           (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                   (real_inv_pos (rtk2_kept k kd) Hkpos)))
           (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                         (real_inv_pos rtk2_Z rtk2_Zpos))).
  { apply (real_eq_trans _ (real_opp (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                     (real_inv_pos (rtk2_kept k kd) Hkpos))) _).
    - exact (rtk_abs_neg_cc
               (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                             (real_inv_pos (rtk2_kept k kd) Hkpos))
               (rtk_lt_minus_cc (real_inv_pos rtk2_Z rtk2_Zpos)
                                (real_inv_pos (rtk2_kept k kd) Hkpos) Hst)).
    - apply (real_eq_trans _ (real_plus (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                          (real_opp (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
      + exact (real_opp_plus (real_inv_pos rtk2_Z rtk2_Zpos)
                 (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos))).
      + apply (real_eq_trans _ (real_plus (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                            (real_inv_pos (rtk2_kept k kd) Hkpos)) _).
        * apply (RealSetoid.real_eq_plus_compat
                   (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                   (real_opp (real_opp (real_inv_pos (rtk2_kept k kd) Hkpos)))
                   (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                   (real_inv_pos (rtk2_kept k kd) Hkpos)
                   (real_eq_refl (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))
                   (real_opp_opp (real_inv_pos (rtk2_kept k kd) Hkpos))).
        * exact (real_plus_comm (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))
                                (real_inv_pos (rtk2_kept k kd) Hkpos)). }
  (* 组装：|b·invZ − invK·b| == b·(invK − invZ) *)
  apply (real_eq_trans _ (real_abs (real_mult (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                              (real_inv_pos (rtk2_kept k kd) Hkpos))
                                (rtk2_bfactor s))) _).
  - apply real_abs_eq_compat. exact Hfac.
  - apply (real_eq_trans _ (real_mult (rtk2_bfactor s)
                        (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (real_inv_pos (rtk2_kept k kd) Hkpos)))) _).
    + exact Habs.
    + apply (RealSetoid.real_eq_mult_compat
               (rtk2_bfactor s)
               (real_abs (real_minus_r (real_inv_pos rtk2_Z rtk2_Zpos)
                                       (real_inv_pos (rtk2_kept k kd) Hkpos)))
               (rtk2_bfactor s)
               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                             (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_eq_refl (rtk2_bfactor s)) Hsign).
Qed.

(* ---- 件13（）：evict 分支 |b·invZ − 0| == b·invZ ---- *)
Lemma rtk_tv_pointwise_evict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S)
         (Hnk : Not (k s)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)) real_zero))
            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
Proof.
  intros k kd s Hnk.
  apply (real_eq_trans _ (real_abs (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))) _).
  - apply real_abs_eq_compat.
    exact (rtk_minus_zero_cc
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))).
  - apply real_abs_pos_req.
    apply (real_mult_positive (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
    + apply (real_inv_pos_pos rtk2_Z rtk2_Zpos).
    + exact (rtk_boltzmann_factor_pos_attn S D D_pos energy s).
Qed.

(* ---- 件16（）：逐点总恒等（条件化） ---- *)
Lemma rtk_tv_pointwise :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd)) (s : S)
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_abs (real_minus_r
              (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
              (rtk2_topk_renorm k kd Hkpos s)))
            (if kd s
             then real_mult (rtk2_bfactor s)
                            (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
             else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)).
Proof.
  intros k kd Hkpos s Hst. unfold rtk2_topk_renorm.
  destruct (kd s) as [Hk | Hnk].
  - exact (rtk_tv_pointwise_keep k kd s Hk Hkpos Hst).
  - exact (rtk_tv_pointwise_evict k kd s Hnk).
Qed.

(* ============================================================ *)
(* 件17（）：求和分解                                           *)
(*   Σ(if keep then b·D' else invZ·b) == kept·D' + invZ·T               *)
(*   链：if 加法分解（件14）→ 求和可加 → 双 linear 肢（linear 位 +       *)
(*   A2/件15）→ kept/tail 端点定义性完成。                              *)
(* ============================================================ *)
Lemma rtk_sum_decomp :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (real_sum_over_S (fun s : S =>
               if kd s
               then real_mult (rtk2_bfactor s)
                              (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                            (real_inv_pos rtk2_Z rtk2_Zpos))
               else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
            (real_plus (real_mult (rtk2_kept k kd)
                                  (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos)))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Proof.
  intros k kd Hkpos Hst.
  apply (real_eq_trans _ (real_plus
              (real_sum_over_S (fun s : S =>
                 if kd s
                 then real_mult (rtk2_bfactor s)
                                (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                              (real_inv_pos rtk2_Z rtk2_Zpos))
                 else real_zero))
              (real_sum_over_S (fun s : S =>
                 if kd s then real_zero
                 else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))) _).
  - (* 逐点 if 分解（件14）→ 求和可加 *)
    apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                real_plus (if kd s
                           then real_mult (rtk2_bfactor s)
                                          (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                        (real_inv_pos rtk2_Z rtk2_Zpos))
                           else real_zero)
                          (if kd s then real_zero
                           else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))) _).
    + apply real_sum_over_S_ext. intro s.
      exact (rtk_if_split k kd
               (real_mult (rtk2_bfactor s)
                          (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                        (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)) s).
    + exact (real_sum_over_S_add
               (fun s : S =>
                  if kd s
                  then real_mult (rtk2_bfactor s)
                                 (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                               (real_inv_pos rtk2_Z rtk2_Zpos))
                  else real_zero)
               (fun s : S =>
                  if kd s then real_zero
                  else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))).
  - (* 双 linear 肢 *)
    apply (RealSetoid.real_eq_plus_compat
             (real_sum_over_S (fun s : S =>
                if kd s
                then real_mult (rtk2_bfactor s)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos))
                else real_zero))
             (real_sum_over_S (fun s : S =>
                if kd s then real_zero
                else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
             (real_mult (rtk2_kept k kd)
                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
    + (* LEFT：Σ(if k then b·D' else 0) == (Σ if-kept)·D' *)
      apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                  real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
                            (if kd s then rtk2_bfactor s else real_zero))) _).
      * apply real_sum_over_S_ext. intro s.
        apply (real_eq_trans _ (if kd s
                  then real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos))
                                 (rtk2_bfactor s)
                  else real_zero) _).
        -- destruct (kd s) as [Hks | Hnks].
           ++ exact (real_mult_comm (rtk2_bfactor s)
                       (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                     (real_inv_pos rtk2_Z rtk2_Zpos))).
           ++ apply real_eq_refl.
        -- exact (rtk_eviction_if_linear k kd
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    rtk2_bfactor s).
      * apply (real_eq_trans _ (real_mult (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                          (real_inv_pos rtk2_Z rtk2_Zpos))
                            (real_sum_over_S (fun s : S =>
                               if kd s then rtk2_bfactor s else real_zero))) _).
        -- exact (real_sum_over_S_linear
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    (fun s : S => if kd s then rtk2_bfactor s else real_zero)).
        -- exact (real_mult_comm
                    (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                  (real_inv_pos rtk2_Z rtk2_Zpos))
                    (real_sum_over_S (fun s : S =>
                       if kd s then rtk2_bfactor s else real_zero))).
    + (* RIGHT：Σ(if k then 0 else invZ·b) == invZ·(Σ if-tail)（件15） *)
      apply (real_eq_trans _ (real_sum_over_S (fun s : S =>
                  real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                            (if kd s then real_zero else rtk2_bfactor s))) _).
      * apply real_sum_over_S_ext. intro s.
        exact (rtk_eviction_if_linear_else k kd
                 (real_inv_pos rtk2_Z rtk2_Zpos) rtk2_bfactor s).
      * exact (real_sum_over_S_linear (real_inv_pos rtk2_Z rtk2_Zpos)
                  (fun s : S => if kd s then real_zero else rtk2_bfactor s)).
Qed.

(* ============================================================ *)
(* 件18（）：完成代数 kept·D' + invZ·T == (1+1)·(invZ·T)        *)
(* ============================================================ *)
Lemma rtk_sum_collapse :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd)),
    real_eq (real_plus (real_mult (rtk2_kept k kd)
                                  (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                (real_inv_pos rtk2_Z rtk2_Zpos)))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
            (real_mult (real_plus real_one real_one)
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Proof.
  intros k kd Hkpos.
  (* kept·invK == 1（real_inv_pos_correct 直引） *)
  assert (Hkept1 : real_eq
             (real_mult (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos))
             real_one)
    by exact (real_inv_pos_correct (rtk2_kept k kd) Hkpos).
  (* Hk1：kept·(invK − invZ) == 1 − kept·invZ *)
  assert (Hk1 : real_eq
           (real_mult (rtk2_kept k kd)
                      (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                    (real_inv_pos rtk2_Z rtk2_Zpos)))
           (real_minus_r real_one
                         (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))).
  { unfold real_minus_r.
    apply (real_eq_trans _ (real_plus real_one
                          (real_opp (real_mult (rtk2_kept k kd)
                                               (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
    - apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd)
                                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                          (real_mult (rtk2_kept k kd)
                                     (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
      + apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd)
                                                       (real_inv_pos (rtk2_kept k kd) Hkpos))
                            (real_mult (rtk2_kept k kd)
                                       (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))) _).
        * exact (real_distrib (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos)
                              (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))).
        * exact (real_eq_refl
                   (real_plus (real_mult (rtk2_kept k kd)
                                          (real_inv_pos (rtk2_kept k kd) Hkpos))
                              (real_mult (rtk2_kept k kd)
                                         (real_opp (real_inv_pos rtk2_Z rtk2_Zpos))))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_mult (rtk2_kept k kd) (real_inv_pos (rtk2_kept k kd) Hkpos))
                 (real_mult (rtk2_kept k kd) (real_opp (real_inv_pos rtk2_Z rtk2_Zpos)))
                 real_one
                 (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
                 Hkept1
                 (real_mult_opp_l (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))).
    - apply real_eq_refl. }
  (* Hk2：kept·invZ + invZ·T == 1（守恒 + inv_pos_correct） *)
  assert (Hk2 : real_eq
           (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                      (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
           real_one).
  { apply (real_eq_trans _ (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                        (real_mult (rtk2_tail k kd) (real_inv_pos rtk2_Z rtk2_Zpos))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (rtk2_tail k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_eq_refl
                  (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult_comm (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
    - apply (real_eq_trans _ (real_mult rtk2_Z (real_inv_pos rtk2_Z rtk2_Zpos)) _).
      + apply (real_eq_trans _
                  (real_mult (real_plus (rtk2_kept k kd) (rtk2_tail k kd))
                             (real_inv_pos rtk2_Z rtk2_Zpos)) _).
        * exact (real_distrib_r (rtk2_kept k kd) (rtk2_tail k kd)
                                (real_inv_pos rtk2_Z rtk2_Zpos)).
        * apply (RealSetoid.real_eq_mult_compat
                   (real_plus (rtk2_kept k kd) (rtk2_tail k kd))
                   (real_inv_pos rtk2_Z rtk2_Zpos)
                   rtk2_Z
                   (real_inv_pos rtk2_Z rtk2_Zpos)
                   (rtk_kept_plus_tail_full S real_sum_over_S real_sum_over_S_ext
                      real_sum_over_S_add D D_pos energy k kd)
                   (real_eq_refl (real_inv_pos rtk2_Z rtk2_Zpos))).
      + exact (real_inv_pos_correct rtk2_Z rtk2_Zpos). }
  (* Hk3：1 − kept·invZ == invZ·T（A1 完成） *)
  assert (Hk3 : real_eq
           (real_minus_r real_one
                         (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
  { apply (real_eq_trans _ (real_minus_r
                (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))) _).
    - apply (RealSetoid.real_eq_plus_compat real_one
               (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_plus (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
               (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_eq_sym _ _ Hk2)
               (real_eq_refl
                  (real_opp (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))))).
    - exact (rtk_minus_plus_cancel_r_cc
               (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))). }
  (* 组装：kept·D' + invZ·T == (1 − kept·invZ) + invZ·T == X + X == (1+1)·X *)
  apply (real_eq_trans _ (real_plus (real_minus_r real_one
                                   (real_mult (rtk2_kept k kd)
                                              (real_inv_pos rtk2_Z rtk2_Zpos)))
                      (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
  - apply (RealSetoid.real_eq_plus_compat
             (real_mult (rtk2_kept k kd)
                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                      (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
             (real_minus_r real_one
                           (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
             (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
             Hk1 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                          (rtk2_tail k kd)))).
  - apply (real_eq_trans _ (real_plus (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                        (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_minus_r real_one
                             (real_mult (rtk2_kept k kd) (real_inv_pos rtk2_Z rtk2_Zpos)))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
               Hk3 (real_eq_refl (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                            (rtk2_tail k kd)))).
    + apply (real_eq_trans _ (real_plus (real_mult real_one
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))
                          (real_mult real_one
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))) _).
      * apply (RealSetoid.real_eq_plus_compat
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                 (real_mult real_one
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_mult real_one
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_eq_trans _ _ _
                    (real_eq_sym _ _
                       (real_mult_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))))
                    (real_eq_sym _ _
                       (real_mult_comm real_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))))
                 (real_eq_trans _ _ _
                    (real_eq_sym _ _
                       (real_mult_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))))
                    (real_eq_sym _ _
                       (real_mult_comm real_one
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))))).
      * exact (real_distrib_r real_one real_one
                 (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
Qed.

(* ============================================================ *)
(* 件19（，主定理）：严格逐出 ⟹ TV(boltzmann, topk) == tail/Z    *)
(* ============================================================ *)
Theorem rtk_tv_identity_strict :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk2_kept k kd))
         (Hst : real_lt (real_inv_pos rtk2_Z rtk2_Zpos)
                        (real_inv_pos (rtk2_kept k kd) Hkpos)),
    real_eq (rtk2_tv_dist k kd Hkpos)
            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)).
Proof.
  intros k kd Hkpos Hst.
  (* 逐点替换（件16） *)
  assert (Hpt : real_eq
           (real_sum_over_S (fun s : S =>
              real_abs (real_minus_r
                          (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                          (rtk2_topk_renorm k kd Hkpos s))))
           (real_sum_over_S (fun s : S =>
              if kd s
              then real_mult (rtk2_bfactor s)
                             (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                           (real_inv_pos rtk2_Z rtk2_Zpos))
              else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))).
  { apply real_sum_over_S_ext. intro s.
    exact (rtk_tv_pointwise k kd Hkpos s Hst). }
  apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                      (real_sum_over_S (fun s : S =>
                         if kd s
                         then real_mult (rtk2_bfactor s)
                                        (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                      (real_inv_pos rtk2_Z rtk2_Zpos))
                         else real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                        (rtk2_bfactor s)))) _).
  - (* inv2·Σ|…| == inv2·Σif（unfold rtk2_tv_dist 端点定义性） *)
    apply (RealSetoid.real_eq_mult_compat
             (real_inv_pos (real_plus real_one real_one) real_two_pos)
             (real_sum_over_S (fun s : S =>
                real_abs (real_minus_r
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s))
                            (rtk2_topk_renorm k kd Hkpos s))))
             (real_inv_pos (real_plus real_one real_one) real_two_pos)
             (real_sum_over_S (fun s : S =>
                if kd s
                then real_mult (rtk2_bfactor s)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos))
                else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
             (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
             Hpt).
  - apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                        (real_plus
                           (real_mult (rtk2_kept k kd)
                                      (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                                    (real_inv_pos rtk2_Z rtk2_Zpos)))
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))) _).
    + (* 件17：求和分解 *)
      apply (RealSetoid.real_eq_mult_compat
               (real_inv_pos (real_plus real_one real_one) real_two_pos)
               (real_sum_over_S (fun s : S =>
                  if kd s
                  then real_mult (rtk2_bfactor s)
                                 (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                               (real_inv_pos rtk2_Z rtk2_Zpos))
                  else real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_bfactor s)))
               (real_inv_pos (real_plus real_one real_one) real_two_pos)
               (real_plus
                  (real_mult (rtk2_kept k kd)
                             (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                           (real_inv_pos rtk2_Z rtk2_Zpos)))
                  (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
               (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
               (rtk_sum_decomp k kd Hkpos Hst)).
    + apply (real_eq_trans _ (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                          (real_mult (real_plus real_one real_one)
                                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                                (rtk2_tail k kd)))) _).
      * (* 件18：完成代数 *)
        apply (RealSetoid.real_eq_mult_compat
                 (real_inv_pos (real_plus real_one real_one) real_two_pos)
                 (real_plus
                    (real_mult (rtk2_kept k kd)
                               (real_minus_r (real_inv_pos (rtk2_kept k kd) Hkpos)
                                             (real_inv_pos rtk2_Z rtk2_Zpos)))
                    (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_inv_pos (real_plus real_one real_one) real_two_pos)
                 (real_mult (real_plus real_one real_one)
                            (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                 (real_eq_refl (real_inv_pos (real_plus real_one real_one) real_two_pos))
                 (rtk_sum_collapse k kd Hkpos)).
      * (* inv2·((1+1)·X) == X：assoc + inv_pos_correct + one *)
        apply (real_eq_trans _ (real_mult
                    (real_mult (real_inv_pos (real_plus real_one real_one) real_two_pos)
                               (real_plus real_one real_one))
                    (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))) _).
        -- exact (real_mult_assoc
                     (real_inv_pos (real_plus real_one real_one) real_two_pos)
                     (real_plus real_one real_one)
                     (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
        -- apply (real_eq_trans _ (real_mult real_one
                                (real_mult (real_inv_pos rtk2_Z rtk2_Zpos)
                                           (rtk2_tail k kd))) _).
           ++ apply (RealSetoid.real_eq_mult_compat
                       (real_mult
                          (real_inv_pos (real_plus real_one real_one) real_two_pos)
                          (real_plus real_one real_one))
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))
                       real_one
                       (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd))).
              ** exact (real_eq_trans _ _ _
                            (real_mult_comm
                               (real_inv_pos (real_plus real_one real_one) real_two_pos)
                               (real_plus real_one real_one))
                            (real_inv_pos_correct
                               (real_plus real_one real_one) real_two_pos)).
              ** apply real_eq_refl.
           ++ exact (real_eq_trans _ _ _
                        (real_mult_comm real_one
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))
                        (real_mult_one
                           (real_mult (real_inv_pos rtk2_Z rtk2_Zpos) (rtk2_tail k kd)))).
Qed.

End RealTopKTVFinish.

(* ============================================================ *)
(* 【 后半段结果核对（本件 8 引理件 + 2 辅件 + 6 定义载体 + 1 补位）】 *)
(*   件12 rtk_tv_pointwise_keep<-5667   件13 rtk_tv_pointwise_evict<-5725*)
(*   件14 rtk_if_split<-5742            件15 rtk_eviction_if_linear_else  *)
(*   件16 rtk_tv_pointwise<-5764        件17 rtk_sum_decomp<-5780         *)
(*   件18 rtk_sum_collapse<-5840        件19 rtk_tv_identity_strict<-5886 *)
(*   （主定理闭合：TV(boltzmann, topk 重归一) == tail/Z 精确恒等）          *)
(*   辅件：rtk_minus_plus_cancel_r_cc（Id minus_plus_cancel_r 副本）      *)
(*   rtk_eviction_if_linear<-4653；载体：rtk2_bfactor/rtk2_Z/rtk2_invZ    *)
(*   rtk2_kept/rtk2_tail/rtk2_invK/rtk2_topk_renorm/rtk2_boltzmann_dist_ *)
(*   attn/rtk2_tv_dist（TopK 家 8 载体全平移）。                          *)
(*   补位：real_sum_over_S_linear（Id SumOver 字段同位， 头注预留）。   *)

(*   G1 禁词 0（自查脚本）；G3 Print Assumptions 全闭（全量模式，         *)

(* ============================================================ *)
