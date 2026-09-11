(* ============================================================ *)
(* UpReqTopKTVChain.v —— 席T16：定理 7.6 topk_tv_identity        *)
(*   Real 层平移·前半段（Id 层 19 引理链前 10 件）2026-09-11      *)
(* ------------------------------------------------------------------ *)
(* 【使命】定理 7.6 topk_tv_identity_strict（论文2 P2 项 9）：        *)
(*   TV(boltzmann, topk 重归一) == tail_mass / Z_thermo（精确恒等）。  *)
(*   Id 层全绿（S06 Section AttentionGibbsBridge @5554-5886，19 引理   *)
(*   四段组装）；req 对位 ag_topk_tv_identity_strict 已交付            *)
(*   UpReqAttnGibbs.v @1721（Print Assumptions 闭）；Real 层平移未做   *)
(*   （附录 B L1387「Real 层 TV 恒等未复刻，grep 无命中」）。          *)
(*   本件 = Id 原件顺序前 10 件的 real_eq / real_le / real_lt 载体     *)
(*   平移（kept 家 6 件 + _cc 符号辅件 4 件）；余件 9 件留滚动席 T17。 *)
(* ------------------------------------------------------------------ *)
(* 【Id 锚（S06 分片行号，Live_X 版）】                                *)
(*   定义件：topk_tail_mass @5537 / topk_kept_partition @5541          *)
(*     / topk_renorm @5548（boltzmann 载体 @3840-3845）。              *)
(*   引理件（本席前半段 11 件 = 前 10 件 + _cc 家族收尾件）：           *)
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
(*   余件（T17 续作清单，8 件，自 TV 点态链起）：                       *)
(*     topk_tv_pointwise_keep @5667 / topk_tv_pointwise_evict @5725    *)
(*     / topk_if_split @5742 / eviction_if_linear_else @5753           *)
(*     / topk_tv_pointwise @5764 / topk_sum_decomp @5780               *)
(*     / topk_sum_collapse @5840 / topk_tv_identity_strict @5886        *)
(*     （旗舰）。                                                       *)
(* ------------------------------------------------------------------ *)
(* 【载体选择（req 对位 UpReqAttnGibbs 同轴）】                        *)
(*   Id 固定 keep_dec 的 tail/kept 家统一为 (k : S -> Set) + kd 可判定  *)
(*   保留集形参（req 版参数化归一台账同轴，Id @30289-30294 实例统一）； *)
(*  相等/序载体：real_eq（逐 eps 函数型 Set 值等价，S02 L387）/        *)
(*   real_lt（见证 eps 的 sigT，S02 L456）/ real_le = Or(lt,eq)        *)
(*   （S02 L460）——全 Set 载体，零 Prop 泄露。                         *)
(*   减法载体：real_minus_r a b := real_plus a (real_opp b)            *)
(*   （S12 L13224 顶层，Id minus 同形）。                              *)
(* ------------------------------------------------------------------ *)
(* 【诚实接口申报（Id SumOver 字段镜像，先例 UpReqSteadyThermo/E246）】*)
(*   求和载体三槽为 Real 层平行接口（S08 RealAttnSteady 同位）：        *)
(*     real_sum_over_S       <- Id sum_over_S                          *)
(*     real_sum_over_S_ext   <- Id sum_over_S_ext（件4 消费）          *)
(*     real_sum_over_S_add   <- Id sum_over_S_add（件4 消费）          *)
(*     real_sum_over_S_le    <- Id sum_over_S_le（件5 消费；req 位      *)
(*                                诚实新增先例 UpReqAttnGibbs sum_le）  *)
(*   热力学载体：D/D_pos/energy/Z_thermo_pos 逐位对位 Id @3837-3845     *)
(*   （boltzmann_factor := exp_neg(inv(D)·energy) 同构镜像）。          *)
(*   全件无非推导假设：Print Assumptions 十件全闭（G3 探针 _t16_g3）。  *)
(* ------------------------------------------------------------------ *)
(* 【消费锚（前置 .vo 直引，零重建）】                                  *)
(*   real_inv_pos/real_inv_pos_correct（S03 L6653/L6722）；             *)
(*   real_inv_pos_le_compat（S07 L6775，inv 反序引擎）；                *)
(*   real_exp_neg_pos（S07 L7765）；real_lt_le_iff_req/real_lt_id_r     *)
(*   （S07 Module RealSetoid L105/L446，限定名纪律 E-STAGING-T1）；     *)
(*   real_lt_plus_compat_lt_le（S07 L6109）；real_opp_lt_compat         *)
(*   （S07 L6667）；real_abs_pos_req（S07 L7280）；real_abs_opp         *)
(*   （S03 L6522）；real_opp_zero（S08 L386，件8 直引——Id @5628        *)
(*   节内自证防前向引用，Real 基座已在盘，直引即诚实）；                *)
(*   real_lt_zero_one（S07 L6928，件7 one 正性 witnesses 位）。         *)
(* ------------------------------------------------------------------ *)
(* 【红线】纯构造性；Set 层零 Prop 泄露（real_eq/real_lt/real_le 全     *)
(*   Set 载体，kd 的 Or/Not 为 Stdlib Set 级析取，req 对位同构）；      *)
(*   real_eq 非 Id 禁改写——全链 real_eq_trans + RealSetoid 运输        *)
(*   （E393 纪律）；全件 Qed 闭合。                                    *)
(* 编译配方：_t16_run.ps1 + cpu_guard（CoreN 3，LoadLimit 65）          *)
(*   coqc -q -vos -Q <vo树> "" -Q . "" UpReqTopKTVChain.v   （秒审）    *)
(*   coqc -q -Q <vo树> "" -Q . "" UpReqTopKTVChain.v        （全量 G2） *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* Section RealTopKTVChain：与 Id AttentionGibbsBridge（topk 段）同构  *)
(* ============================================================ *)
Section RealTopKTVChain.

(* 世界：状态类型（Id @3177 Context 位镜像；Id 经 RealInterface 取 S， *)
(*   Real 层直取 Type 形参——求和载体三槽同取抽象位，E246 坑2 同款）。 *)
Variable S : Type.

(* ---- 求和载体三槽（Id SumOver 字段镜像；本席件4/件5 消费面） ---- *)
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

(* ---- Boltzmann 载体（Id @3837-3843 逐位镜像；req 版 L537-541 同构） ---- *)
Variable D : Real.
Variable D_pos : real_lt real_zero D.
Variable energy : S -> Real.

Definition rtk_boltzmann_factor (s : S) : Real :=
  real_exp_neg (real_mult (real_inv_pos D D_pos) (energy s)).

Definition rtk_Z_thermo : Real := real_sum_over_S rtk_boltzmann_factor.

Variable rtk_Z_thermo_pos : real_lt real_zero rtk_Z_thermo.

(* ---- 定义件（Id @5537/@5541 参数化镜像；req 版 tail_mass_of_r 同轴） -- *)
(* Top-K 版尾部质量（Id topk_tail_mass：逐出态质量） *)
Definition rtk_tail_mass
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then real_zero else rtk_boltzmann_factor s).

(* Top-K 版保留质量（Id topk_kept_partition：重归一化分母） *)
Definition rtk_kept_partition
  (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) : Real :=
  real_sum_over_S (fun s : S => if kd s then rtk_boltzmann_factor s else real_zero).

(* ---- 件1（Id @5554）：单参 boltzmann 因子正性 ---- *)
(* Id 证明 = exp_neg_pos 直引；Real 层同型（real_exp_neg_pos 引擎位）。 *)
Lemma rtk_boltzmann_factor_pos_attn :
  forall s : S, real_lt real_zero (rtk_boltzmann_factor s).
Proof.
  intro s. unfold rtk_boltzmann_factor. apply real_exp_neg_pos.
Qed.

(* ---- 件2（Id @5560）：if 保留项非负（keep 时 > 0，else == 0） ---- *)
Lemma rtk_kept_term_nonneg :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))) (s : S),
    real_le real_zero (if kd s then rtk_boltzmann_factor s else real_zero).
Proof.
  intros k kd s. destruct (kd s) as [Hk | Hnk].
  - apply (RealSetoid.real_lt_le_iff_req real_zero (rtk_boltzmann_factor s)).
    left. apply rtk_boltzmann_factor_pos_attn.
  - apply real_le_refl.
Qed.

(* ---- 件3（Id @5569）：if 保留项 ≤ 因子（keep 时自反，else 0 < b） ---- *)
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

(* ---- 件4（Id @5578）：守恒 kept + tail == Z_thermo ---- *)
(* Id 证明链：逐点 plus 消零（plus_zero 两向）→ 求和外延 → 求和可加；   *)
(* Real 层同构重放（real_eq_trans 链 + ext/add 双腿；E393 纪律）。      *)
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

(* ---- 件5（Id @5603）：kept ≤ Z_thermo（子集和 ≤ 全和） ---- *)
Lemma rtk_kept_le_Zthermo :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s))),
    real_le (rtk_kept_partition k kd) rtk_Z_thermo.
Proof.
  intros k kd. unfold rtk_kept_partition, rtk_Z_thermo.
  apply real_sum_over_S_le.
  intro s. apply rtk_kept_term_le_factor.
Qed.

(* ---- 件6（Id @5611）：inv 反序 kept ≤ Z ⟹ 1/Z ≤ 1/kept ---- *)
(* 引擎：real_inv_pos_le_compat（S07 L6775；Id inv_pos_le_compat 同位）。 *)
Lemma rtk_inv_Z_le_inv_kept :
  forall (k : S -> Set) (kd : forall s : S, Or (k s) (Not (k s)))
         (Hkpos : real_lt real_zero (rtk_kept_partition k kd)),
    real_le (real_inv_pos rtk_Z_thermo rtk_Z_thermo_pos)
            (real_inv_pos (rtk_kept_partition k kd) Hkpos).
Proof.
  intros k kd Hkpos.
  apply (real_inv_pos_le_compat (rtk_kept_partition k kd) rtk_Z_thermo
             Hkpos rtk_Z_thermo_pos).
  exact (rtk_kept_le_Zthermo k kd).
Qed.

(* ============================================================ *)
(* _cc 符号辅件四件（Id @5620-@5647；与 topk 载体解耦，纯 Real 代数）  *)
(* ============================================================ *)

(* ---- 件7（Id @5620）：inv one == one ---- *)
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

(* ---- 件8（Id @5628）：opp zero == zero ---- *)
(* Id 节内自证防前向引用；Real 基座 S08 L386 real_opp_zero 已在盘，      *)
(* 直引消费（前置锚零重建纪律；探针核验 Closed，见 _t16_probe）。        *)
Lemma rtk_opp_zero_cc : real_eq (real_opp real_zero) real_zero.
Proof.
  exact real_opp_zero.
Qed.

(* ---- 件9（Id @5637）：a < b ⟹ a − b < 0 ---- *)
(* Id 链：minus 展开 → lt_id_r（b + opp b == 0）→ 混合 plus 兼容；       *)
(* Real 层：real_minus_r 展开 → real_lt_id_r + real_plus_opp 腿          *)
(* + real_lt_plus_compat_lt_le 混合兼容（S07 L6109，req 版假设位          *)
(* req_lt_plus_compat_lt_le_h 的 Real 实例引擎——req 接口无混合字段，     *)
(* Real 层可直接消费，假设位自然放电，见头注 T4.3 对位）。               *)
Lemma rtk_lt_minus_cc :
  forall a b : Real, real_lt a b -> real_lt (real_minus_r a b) real_zero.
Proof.
  intros a b Hab. unfold real_minus_r.
  apply (RealSetoid.real_lt_id_r (real_plus a (real_opp b))
                                 (real_plus b (real_opp b)) real_zero
                                 (real_plus_opp b)).
  exact (real_lt_plus_compat_lt_le a b (real_opp b) (real_opp b)
             Hab (real_le_refl (real_opp b))).
Qed.

(* ---- 件10（Id @5647）：a < 0 ⟹ |a| == −a ---- *)
(* Id 链：abs_opp 对称 → abs_pos（负支）→ opp 保序换向；                 *)
(* Real 层：real_abs_opp 对称腿 + real_abs_pos_req（负号消去引擎，       *)
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

(* ---- 件11（Id @5658，_cc 家族收尾件）：x − 0 == x ---- *)
(* Id 链：minus 展开 → opp zero == zero 换元 → plus_zero；Real 层：     *)
(* real_minus_r 展开 → RealSetoid.real_eq_plus_compat 换右元（opp 0 ≈ 0）*)
(* → real_plus_zero 收口。至此 _cc 符号辅件五件全平移，T17 自 TV 点态   *)
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
(* 【前半段交付对账（本席 11 引理件 + 5 定义载体，四关验证见尾注）】    *)
(*   rtk_boltzmann_factor_pos_attn<-5554  rtk_kept_term_nonneg<-5560    *)
(*   rtk_kept_term_le_factor<-5569        rtk_kept_plus_tail_full<-5578 *)
(*   rtk_kept_le_Zthermo<-5603            rtk_inv_Z_le_inv_kept<-5611   *)
(*   rtk_inv_one_cc<-5620                 rtk_opp_zero_cc<-5628         *)
(*   rtk_lt_minus_cc<-5637                rtk_abs_neg_cc<-5647          *)
(*   rtk_minus_zero_cc<-5658                                            *)
(*   定义载体：rtk_boltzmann_factor<-3840 rtk_Z_thermo<-3843            *)
(*   rtk_tail_mass<-5537                  rtk_kept_partition<-5541      *)
(*   （topk_renorm<-5548 属 TV 链后半段消费面，留 T17 与件 12-19 同批）。 *)
(* 【T17 续作清单（Id @5667-@5886，8 件）】                              *)
(*   topk_tv_pointwise_keep<-5667 / topk_tv_pointwise_evict<-5725 /      *)
(*   topk_if_split<-5742 / eviction_if_linear_else<-5753 /               *)
(*   topk_tv_pointwise<-5764 / topk_sum_decomp<-5780 /                   *)
(*   topk_sum_collapse<-5840 / topk_tv_identity_strict<-5886（旗舰）。   *)
(*   T17 消费面：本节三求和槽 + linear 槽（tv 链点态/分解需               *)
(*   real_sum_over_S_linear，Id sum_over_S_linear 字段同位，诚实新增）；  *)
(*   件9 rtk_lt_minus_cc / 件10 rtk_abs_neg_cc / 件11 rtk_minus_zero_cc  *)
(*   为逐点差分解符号腿引擎。                                            *)
(* 【四关验证】G2 全量 coqc EXIT=0（cpu_guard CoreN 3）；                 *)
(*   G1 禁词 0（自查脚本）；G3 Print Assumptions 十一件全闭               *)
(*   （_t16_g3.v）+ Recursive Extraction 顶级名 Obj.magic=0；             *)
(*   G4 coqchk 无 unsafe。                                               *)
(* ============================================================ *)
