(* ============================================================ *)
(* UpReqConcMixSel.v —— 席 AT6：混合时间选择器 req 面镜像（S2）        *)
(*   + 合龙件 req 面镜像（S3）。路线①（req 镜像系补齐）第二棒。        *)
(* 论文7 §10.2 第 7 项 · 无条件合龙（attn/_tat4_侦察报告切片工单        *)
(*   S2/S3 · attn/_tat5_交付报告余切片清单）2026-09-18                *)
(*                                                              *)
(* 母本：Live_X/UpReqUMixSelect.v（Id 面 ums_ 系，AT1 席）逐件镜像；      *)
(*   合龙胶水母本：Live_X/UpReqAttnMixTime.v（Id 面 amt_ 系）。           *)
(* 面定谳（AT5 S1 探针 P4 实测）：Id 面 System A 实例不可建，req 面       *)
(*   （RealInterfaceEnhancedSetoid + 实例 RealEnhancedReal，S07）为      *)
(*   唯一具体层基座；本件全部语句 Set 值 req/le/lt 面。                  *)
(*                                                              *)
(* S2（本件主增量）：k 选取器 req 化——cmk_scale/cmk_r_pow 累加器与幂、    *)
(*   抽象环账 req 链（bernoulli_cancel/ring_sc/minus_le）、Bernoulli     *)
(*   上界 cmk_bernoulli_upper、逆元腿 cmk_le_inv、尾链核 cmk_pow_tail、  *)
(*   选择器双头 cmk_k_select/cmk_pow_budget/cmk_k_select_le。            *)
(*   混合加法保序 lt_plus_compat_lt_le 与 Id 面同位保持诚实 Variable      *)
(*   （req 类字段仅 strict-strict 形 lt_plus_compat，混合形抽象层        *)
(*   不可内证——UpReqSampling bs_lpc 同位先例），镜像签名同构。            *)
(*                                                              *)
(* S3（同件下半）：合龙件 req 化——cmk_ds_lt_one/cmk_omd_pos/              *)
(*   cmk_omd_lt_one/cmk_one_eq 四胶水 + cmk_tv + 合龙定理双头            *)
(*   cmk_attention_mixing_time（±le），消费：                            *)
(*   ① S2 选择器 cmk_k_select（本件上半）；                              *)
(*   ② rsq_bounded_softmax_tv_iter（UpReqSampling 旗舰 2，全显式证书参）  *)
(*     ——其 abs_sum_le 槽为 plain 形冻结位（AT5 槽位警告：Or 编码对       *)
(*     混合号 f 真墙），本节保持同位诚实 Hypothesis（具体层由             *)
(*     csm_abs_sum_le_eps（UpReqConcSoftmax）供逐 eps 形或 B1 一元        *)
(*     enum 平推，终装消解归 S8）；                                      *)
(*   ③ real_expf_realizable（AttnDoeblin Part C）req 面拆件镜像           *)
(*     cmk_expf_realizable（expf 五性质一件全供，具体 Real 层）。          *)
(*   TV₀ 非负槽位警告：req 面 abs≥0 的 plain le 形同属 Or 墙              *)
(*   （类字段 abs_nonneg 仅 Bishop 逐 eps 形），合龙定理以显式证书参      *)
(*   Htv0 : le zero (tv mu nu) 保持诚实（Id 面 amt_tv_nonneg 的          *)
(*   tv_dist_nonneg 依赖 Id 面 abs 公理组，req 面无同款无条件件）。        *)
(*                                                              *)
(* 消费面（全 Require 已认证 .vo，零改上游）：CW219（S02/S07 req 面       *)
(*   字段全套直用——plus_assoc/mult_comm/le_id_l/lt_le_iff/inv_pos 系）；  *)
(*   UpReqAlgebra（req_minus/req_opp_mult_l/req_double_neg/req_opp_plus/  *)
(*   req_minus_plus_cancel/req_two_pos）；UpReqSumD+UpReqConcSoftmax      *)
(*   （req 面有限和供给，S3 槽位注记锚点）；UpReqSampling（req_r_pow +    *)
(*   rsq 旗舰链）；AttnDoeblin（real_expf_realizable）。                  *)
(*                                                              *)
(* 公理面自审：全件语句 Set 值（req/le/lt/sigT 均 Set 值面）；前提位全    *)
(*   显式证书参数（接口前件=显式参数，探针应 Closed）；无未证断言；       *)
(*   雞经典逻辑、无选择公理、无排中律；选择器/合龙件全 Defined 收束       *)
(*   可提取。本件零新增未证假设位（lpc/abs_sum_le_h/Htv0 均为母本同位    *)
(*   诚实接口，跨席可全显式证书参数消费）。                                *)
(* 红线自审：①real_arch 的 And(2<=n)%nat Prop 组件未入 Set 值 sigT 槽     *)
(*   （本件不消费 real_arch，Arch 前件保持 nat-尺度 ums_scale 形）；      *)
(*   ②零 enum_nonempty 消去位（S3 走 rsq 链，其内部先例合规）；           *)
(*   ③面-面搬运逐字面对面（Id→req 全件重镜像，零 retype）。              *)
(* 编译配方（9.1 直调轨，COQLIB/ROCQLIB 必设——E-STAGING-AT5 卡①）：      *)
(*   cpu_guard → _tat6_run.cmd（coqc -q -native-compiler no -Q . ""）；   *)
(*   前台编译（后台挂死坑②）；${PIPESTATUS[0]} 收口。                    *)
(* 撞名检查：cmk_ 前缀全树 grep 零撞名（20260918 实测，花名册条目除外）。  *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import AttnDoeblin.
Import RealInterfaceEnhancedMod.
Import ListNotations.

(* ============================================================ *)
(* Section CmkMixSelect：S2 · k 选取器 req 面镜像（ums_ 系逐件）        *)
(* ============================================================ *)

Section CmkMixSelect.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* 诚实接口：混合 lt+le 加法保序（Id 面 UMixSelect 同位 Variable 镜像；   *)
(*   req 类字段仅 strict-strict lt_plus_compat，混合形抽象层不可内证） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

(* ---- 双向等式保序helper（req 面 id_cong 限制形：plus/mult 各双侧） ---- *)

Lemma cmk_plus_congr_l : forall (a x y : R), req x y -> req (plus a x) (plus a y).
Proof. intros a x y H. exact (req_plus_compat a a x y (req_refl a) H). Defined.

Lemma cmk_plus_congr_r : forall (b x y : R), req x y -> req (plus x b) (plus y b).
Proof. intros b x y H. exact (req_plus_compat x y b b H (req_refl b)). Defined.

Lemma cmk_mult_congr_l : forall (a x y : R), req x y -> req (mult a x) (mult a y).
Proof. intros a x y H. exact (req_mult_compat a a x y (req_refl a) H). Defined.

Lemma cmk_mult_congr_r : forall (b x y : R), req x y -> req (mult x b) (mult y b).
Proof. intros b x y H. exact (req_mult_compat x y b b H (req_refl b)). Defined.

(* 端点 x y 由证书类型唯一确定，置隐（长链换形书写简洁位） *)
Arguments cmk_plus_congr_l a {x y} _.
Arguments cmk_plus_congr_r b {x y} _.
Arguments cmk_mult_congr_l a {x y} _.
Arguments cmk_mult_congr_r b {x y} _.

(* ============================================================ *)
(* Part 1：nat-尺度部分和累加器（ums_scale req 镜像）                  *)
(* ============================================================ *)

Fixpoint cmk_scale (k : nat) (w : R) : R :=
  match k with
  | Datatypes.O => zero
  | Datatypes.S m => plus w (cmk_scale m w)
  end.

(* nat-尺度非负：0 ≤ w ⟹ 0 ≤ k·w（@ums_scale_nonneg） *)
Lemma cmk_scale_nonneg : forall (w : R) (k : nat),
  le zero w -> le zero (cmk_scale k w).
Proof.
  intros w k Hw. induction k as [| k IH].
  - exact (le_refl zero).
  - exact (le_id_l zero (plus zero zero) (plus w (cmk_scale k w))
             (req_sym _ _ (plus_zero zero))
             (le_plus_compat zero w zero (cmk_scale k w) Hw IH)).
Defined.

(* nat-尺度严格正：0 < w ⟹ 0 < (S k)·w（@ums_scale_S_pos） *)
Lemma cmk_scale_S_pos : forall (w : R) (k : nat),
  lt zero w -> lt zero (cmk_scale (Datatypes.S k) w).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus w (cmk_scale k w))
           (req_sym _ _ (plus_zero zero))
           (lt_plus_compat_lt_le zero w zero (cmk_scale k w)
              Hw (cmk_scale_nonneg w k (lt_le_iff zero w (inl Hw))))).
Defined.

(* boost 正性：1 + k·w > 0（@ums_boost_pos） *)
Lemma cmk_boost_pos : forall (w : R) (k : nat),
  le zero w -> lt zero (plus one (cmk_scale k w)).
Proof.
  intros w k Hw.
  exact (lt_id_l zero (plus zero zero) (plus one (cmk_scale k w))
           (req_sym _ _ (plus_zero zero))
           (lt_plus_compat_lt_le zero one zero (cmk_scale k w)
              one_pos (cmk_scale_nonneg w k Hw))).
Defined.

(* ============================================================ *)
(* Part 2：抽象环账小件（@ums 环账 req 链重放）                        *)
(* ============================================================ *)

(* 1·x == x（@ums_mult_one_l） *)
Lemma cmk_mult_one_l : forall x : R, req (mult one x) x.
Proof.
  intro x. exact (req_trans _ _ _ (mult_comm one x) (mult_one x)).
Defined.

(* x·(−y) == −(x·y)（@ums_mult_opp_r；UpReqAlgebra req_opp_mult_l 直连） *)
Lemma cmk_mult_opp_r : forall x y : R, req (mult x (opp y)) (opp (mult x y)).
Proof.
  intros x y. exact (req_opp_mult_l x y).
Defined.

(* 乘法换位：(a·b)·c == b·(a·c)（@ums_mult_swap） *)
Lemma cmk_mult_swap : forall a b c : R,
  req (mult (mult a b) c) (mult b (mult a c)).
Proof.
  intros a b c.
  exact (req_trans _ _ _
           (req_mult_compat (mult a b) (mult b a) c c
              (mult_comm a b) (req_refl c))
           (req_sym _ _ (mult_assoc b a c))).
Defined.

(* 逆元消去：x·(y·inv(x)) == y（0 < x；@ums_mult_div） *)
Lemma cmk_mult_div : forall (x y : R) (H : lt zero x),
  req (mult x (mult y (inv_pos x H))) y.
Proof.
  intros x y H.
  apply (req_trans _ (mult (mult x y) (inv_pos x H)) _).
  { exact (mult_assoc x y (inv_pos x H)). }
  apply (req_trans _ (mult (mult y x) (inv_pos x H)) _).
  { exact (cmk_mult_congr_r (inv_pos x H) (mult_comm x y)). }
  apply (req_trans _ (mult y (mult x (inv_pos x H))) _).
  { exact (req_sym _ _ (mult_assoc y x (inv_pos x H))). }
  apply (req_trans _ (mult y one) _).
  { exact (cmk_mult_congr_l y (inv_pos_correct x H)). }
  exact (mult_one y).
Defined.

(* 右加平移（le）：0 ≤ d ⟹ x ≤ x + d（@ums_le_plus_r） *)
Lemma cmk_le_plus_r : forall x d : R, le zero d -> le x (plus x d).
Proof.
  intros x d Hd.
  exact (le_id_l x (plus x zero) (plus x d) (req_sym _ _ (plus_zero x))
           (le_plus_compat x x zero d (le_refl x) Hd)).
Defined.

(* 减法可逆：(a − b) + b == a（@ums_minus_plus_cancel） *)
Lemma cmk_minus_plus_cancel : forall a b : R, req (plus (req_minus a b) b) a.
Proof.
  intros a b. unfold req_minus.
  apply (req_trans _ (plus a (plus (opp b) b)) _).
  { exact (req_sym _ _ (plus_assoc a (opp b) b)). }
  apply (req_trans _ (plus a zero) _).
  { exact (cmk_plus_congr_l a
             (req_trans _ _ _ (plus_comm (opp b) b) (plus_opp b))). }
  exact (plus_zero a).
Defined.

(* 减法 ≤ 本体：0 ≤ d ⟹ X − d ≤ X（@ums_minus_le） *)
Lemma cmk_minus_le : forall X d : R, le zero d -> le (req_minus X d) X.
Proof.
  intros X d Hd.
  exact (le_id_r (req_minus X d) (plus (req_minus X d) d) X
           (cmk_minus_plus_cancel X d) (cmk_le_plus_r (req_minus X d) d Hd)).
Defined.

(* ============================================================ *)
(* Part 3：率证书小件与幂面（@ums omd/rpow 系）                        *)
(* ============================================================ *)

(* 0 < w < 1 ⟹ 0 < 1−w（@ums_omd_lt_one） *)
Lemma cmk_omd_lt_one : forall w : R,
  lt zero w -> lt w one -> lt zero (req_minus one w).
Proof.
  intros w Hw0 Hw1. unfold req_minus.
  apply (lt_id_l zero (plus w (opp w)) (plus one (opp w))
           (req_sym _ _ (plus_opp w))).
  exact (lt_plus_compat_lt_le w one (opp w) (opp w) Hw1 (le_refl (opp w))).
Defined.

(* omd 双重补：x == 1−(1−x)（@ums_omd_id；req 链式重放） *)
Lemma cmk_omd_id : forall x : R, req x (req_minus one (req_minus one x)).
Proof.
  intro x. apply req_sym. unfold req_minus.
  exact (req_trans _ _ _
           (cmk_plus_congr_l one (req_opp_plus one (opp x)))
           (req_trans _ _ _
              (cmk_plus_congr_l one
                 (cmk_plus_congr_l (opp one) (req_double_neg x)))
              (req_trans _ _ _
                 (plus_assoc one (opp one) x)
                 (req_trans _ _ _
                    (cmk_plus_congr_r x (plus_opp one))
                    (req_trans _ _ _ (plus_comm zero x) (plus_zero x)))))).
Defined.

(* 幂外延：底相等 ⟹ 幂相等（@ums_rpow_eq_compat） *)
Fixpoint cmk_r_pow (x : R) (n : nat) : R :=
  match n with
  | Datatypes.O => one
  | Datatypes.S m => mult x (cmk_r_pow x m)
  end.

Lemma cmk_rpow_eq_compat : forall (x y : R) (k : nat),
  req x y -> req (cmk_r_pow x k) (cmk_r_pow y k).
Proof.
  intros x y k Hxy. induction k as [| k IH].
  - exact (req_refl one).
  - exact (req_mult_compat x y _ _ Hxy IH).
Defined.

(* 幂正：0 < a ⟹ 0 < a^k（@ums_rpow_pos） *)
Lemma cmk_rpow_pos : forall (a : R) (k : nat),
  lt zero a -> lt zero (cmk_r_pow a k).
Proof.
  intros a k Ha. induction k as [| k IH].
  - exact (one_pos).
  - exact (mult_positive a (cmk_r_pow a k) Ha IH).
Defined.

(* 幂对底的 req 外延：w == w' ⟹ cmk_scale k w == cmk_scale k w'           *)
Lemma cmk_scale_congr : forall (k : nat) (x y : R),
  req x y -> req (cmk_scale k x) (cmk_scale k y).
Proof.
  intros k. induction k as [| k IH]; intros x y Hxy.
  - exact (req_refl zero).
  - exact (req_plus_compat x y (cmk_scale k x) (cmk_scale k y) Hxy (IH x y Hxy)).
Defined.

(* nat-尺度对右因子的分配：(k·x)·z == k·(x·z)（@ums_scale_mult_distrib） *)
Lemma cmk_scale_mult_distrib : forall (k : nat) (x z : R),
  req (mult (cmk_scale k x) z) (cmk_scale k (mult x z)).
Proof.
  intros k. induction k as [| k IH]; intros x z.
  - exact (req_trans _ _ _ (mult_comm zero z) (mult_zero z)).
  - apply (req_trans _ (mult z (plus x (cmk_scale k x))) _).
    { exact (mult_comm (plus x (cmk_scale k x)) z). }
    apply (req_trans _ (plus (mult z x) (mult z (cmk_scale k x))) _).
    { exact (distrib z x (cmk_scale k x)). }
    apply (req_trans _ (plus (mult x z) (mult z (cmk_scale k x))) _).
    { exact (cmk_plus_congr_r (mult z (cmk_scale k x)) (mult_comm z x)). }
    apply (req_trans _ (plus (mult x z) (mult (cmk_scale k x) z)) _).
    { exact (cmk_plus_congr_l (mult x z) (mult_comm z (cmk_scale k x))). }
    apply (req_trans _ (plus (mult x z) (cmk_scale k (mult x z))) _).
    { exact (cmk_plus_congr_l (mult x z) (IH x z)). }
    exact (req_refl _).
Defined.

(* ============================================================ *)
(* Part 4：Bernoulli 上形式（@ums_bernoulli_upper 承重墙 req 镜像）      *)
(* ============================================================ *)

(* 泛型环主件（cancel-ready 形）：(1−w)(1+w+s) + (w+s)·w == 1+s           *)
(* （@ums_bernoulli_cancel req 链式重放，cmk_plus_congr 系逐步换形） *)
Lemma cmk_bernoulli_cancel : forall w s : R,
  req (plus (mult (req_minus one w) (plus one (plus w s))) (mult (plus w s) w))
       (plus one s).
Proof.
  intros w s. unfold req_minus.
  apply (req_trans _ (plus (plus (mult (plus one (opp w)) one)
                                 (mult (plus one (opp w)) (plus w s)))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (distrib (plus one (opp w)) one (plus w s))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (mult (plus one (opp w)) (plus w s)))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_r (mult (plus one (opp w)) (plus w s))
                (mult_one (plus one (opp w))))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (mult (plus w s) (plus one (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (mult_comm (plus one (opp w)) (plus w s)))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (mult (plus w s) one)
                                       (mult (plus w s) (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (distrib (plus w s) one (opp w)))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (plus w s) (mult (plus w s) (opp w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (cmk_plus_congr_r (mult (plus w s) (opp w))
                   (mult_one (plus w s))))). }
  apply (req_trans _ (plus (plus (plus one (opp w))
                                 (plus (plus w s) (opp (mult (plus w s) w))))
                             (mult (plus w s) w)) _).
  { exact (cmk_plus_congr_r (mult (plus w s) w)
             (cmk_plus_congr_l (plus one (opp w))
                (cmk_plus_congr_l (plus w s)
                   (cmk_mult_opp_r (plus w s) w)))). }
  apply (req_trans _ (plus (plus one (opp w))
                           (plus (plus (plus w s) (opp (mult (plus w s) w)))
                                 (mult (plus w s) w))) _).
  { exact (req_sym _ _ (plus_assoc (plus one (opp w))
                          (plus (plus w s) (opp (mult (plus w s) w)))
                          (mult (plus w s) w))). }
  apply (req_trans _ (plus (plus one (opp w))
                           (plus (plus w s) (plus (opp (mult (plus w s) w))
                                                  (mult (plus w s) w)))) _).
  { exact (cmk_plus_congr_l (plus one (opp w))
             (req_sym _ _ (plus_assoc (plus w s)
                             (opp (mult (plus w s) w))
                             (mult (plus w s) w)))). }
  apply (req_trans _ (plus (plus one (opp w)) (plus (plus w s) zero)) _).
  { exact (cmk_plus_congr_l (plus one (opp w))
             (cmk_plus_congr_l (plus w s)
                (req_trans _ _ _
                   (plus_comm (opp (mult (plus w s) w)) (mult (plus w s) w))
                   (plus_opp (mult (plus w s) w))))). }
  apply (req_trans _ (plus (plus one (opp w)) (plus w s)) _).
  { exact (cmk_plus_congr_l (plus one (opp w)) (plus_zero (plus w s))). }
  apply (req_trans _ (plus one (plus (opp w) (plus w s))) _).
  { exact (req_sym _ _ (plus_assoc one (opp w) (plus w s))). }
  apply (req_trans _ (plus one (plus (plus (opp w) w) s)) _).
  { exact (cmk_plus_congr_l one (plus_assoc (opp w) w s)). }
  apply (req_trans _ (plus one (plus zero s)) _).
  { exact (cmk_plus_congr_l one
             (cmk_plus_congr_r s
                (req_trans _ _ _ (plus_comm (opp w) w) (plus_opp w)))). }
  apply (req_trans _ (plus one (plus s zero)) _).
  { exact (cmk_plus_congr_l one (plus_comm zero s)). }
  exact (cmk_plus_congr_l one (plus_zero s)).
Defined.

(* 消去转减法形：X + Y == Z ⟹ X == Z − Y（@ums_cancel_to_minus） *)
Lemma cmk_cancel_to_minus : forall X Y Z : R,
  req (plus X Y) Z -> req X (req_minus Z Y).
Proof.
  intros X Y Z HC. unfold req_minus.
  exact (req_trans _ _ _
           (req_sym _ _ (plus_zero X))
           (req_trans _ _ _
              (cmk_plus_congr_l X (req_sym _ _ (plus_opp Y)))
              (req_trans _ _ _
                 (plus_assoc X Y (opp Y))
                 (cmk_plus_congr_r (opp Y) HC)))).
Defined.

(* 环账承接口：(1−u)(1+u+a) == (1+a) − (u+a)·u（@ums_ring_sc） *)
Lemma cmk_ring_sc : forall u a : R,
  req (mult (req_minus one u) (plus one (plus u a)))
       (req_minus (plus one a) (mult (plus u a) u)).
Proof.
  intros u a.
  exact (cmk_cancel_to_minus
           (mult (req_minus one u) (plus one (plus u a)))
           (mult (plus u a) u) (plus one a)
           (cmk_bernoulli_cancel u a)).
Defined.

(* 主墙：(1−w)^k·(1+k·w) ≤ 1（0 < w < 1；@ums_bernoulli_upper） *)
Lemma cmk_bernoulli_upper : forall (w : R) (k : nat),
  lt zero w -> lt w one ->
  le (mult (cmk_r_pow (req_minus one w) k) (plus one (cmk_scale k w))) one.
Proof.
  intros w k Hwp Hwlt. induction k as [| k IH].
  - (* k = 0：1·(1+0) == 1 *)
    change (le (mult one (plus one (cmk_scale 0 w))) one).
    exact (le_id_l (mult one (plus one (cmk_scale 0 w))) one one
             (req_trans _ _ _ (mult_comm one (plus one (cmk_scale 0 w)))
                (req_trans _ _ _ (mult_one (plus one (cmk_scale 0 w)))
                           (plus_zero one)))
             (le_refl one)).
  - (* 归纳步：环账 (1−w)(1+(k+1)w) == (1+kw) − ((k+1)w)·w ≤ 1+kw；        *)
    (* 再乘幂正腿接 IH 换位（@ums 同构） *)
    assert (Hbpos : lt zero (req_minus one w))
      by exact (cmk_omd_lt_one w Hwp Hwlt).
    assert (HPk : lt zero (cmk_r_pow (req_minus one w) k))
      by exact (cmk_rpow_pos (req_minus one w) k Hbpos).
    assert (HC : lt zero (mult (cmk_scale (Datatypes.S k) w) w))
      by exact (mult_positive (cmk_scale (Datatypes.S k) w) w
                  (cmk_scale_S_pos w k Hwp) Hwp).
    assert (HSC : le (mult (req_minus one w)
                             (plus one (cmk_scale (Datatypes.S k) w)))
                       (plus one (cmk_scale k w))).
    { apply (le_id_l (mult (req_minus one w)
                             (plus one (plus w (cmk_scale k w))))
                       (req_minus (plus one (cmk_scale k w))
                                  (mult (cmk_scale (Datatypes.S k) w) w))
                       (plus one (cmk_scale k w))).
      - exact (cmk_ring_sc w (cmk_scale k w)).
      - exact (cmk_minus_le (plus one (cmk_scale k w))
                 (mult (cmk_scale (Datatypes.S k) w) w)
                 (lt_le_iff zero (mult (cmk_scale (Datatypes.S k) w) w)
                              (inl HC))). }
    assert (HeqR : req (mult (mult (req_minus one w)
                                     (cmk_r_pow (req_minus one w) k))
                               (plus one (cmk_scale (Datatypes.S k) w)))
                          (mult (mult (req_minus one w)
                                      (plus one (cmk_scale (Datatypes.S k) w)))
                                (cmk_r_pow (req_minus one w) k)))
      by exact (req_trans _ _ _
                  (cmk_mult_swap (req_minus one w)
                     (cmk_r_pow (req_minus one w) k)
                     (plus one (cmk_scale (Datatypes.S k) w)))
                  (mult_comm (cmk_r_pow (req_minus one w) k)
                     (mult (req_minus one w)
                           (plus one (cmk_scale (Datatypes.S k) w))))).
    assert (IH' : le (mult (plus one (cmk_scale k w))
                               (cmk_r_pow (req_minus one w) k))
                       one).
    { exact (le_id_l (mult (plus one (cmk_scale k w))
                               (cmk_r_pow (req_minus one w) k))
                       (mult (cmk_r_pow (req_minus one w) k)
                             (plus one (cmk_scale k w)))
                       one
                       (mult_comm (plus one (cmk_scale k w))
                                  (cmk_r_pow (req_minus one w) k))
                       IH). }
    apply (le_trans _ (mult (plus one (cmk_scale k w))
                                (cmk_r_pow (req_minus one w) k))).
    + exact (le_id_l (mult (cmk_r_pow (req_minus one w) (Datatypes.S k))
                               (plus one (cmk_scale (Datatypes.S k) w)))
                       (mult (mult (req_minus one w)
                                   (plus one (cmk_scale (Datatypes.S k) w)))
                             (cmk_r_pow (req_minus one w) k))
                       (mult (plus one (cmk_scale k w))
                             (cmk_r_pow (req_minus one w) k))
                       HeqR
                       (le_mult_compat (mult (req_minus one w)
                                           (plus one (cmk_scale (Datatypes.S k) w)))
                                       (plus one (cmk_scale k w))
                                       (cmk_r_pow (req_minus one w) k) HPk HSC)).
    + exact IH'.
Defined.

(* ============================================================ *)
(* Part 5：逆元腿（@ums_le_inv）                                       *)
(* ============================================================ *)

Lemma cmk_le_inv : forall (A B : R) (HB : lt zero B),
  le (mult A B) one -> le A (inv_pos B HB).
Proof.
  intros A B HB HAB.
  assert (HBp : lt zero (inv_pos B HB)) by exact (inv_pos_pos B HB).
  apply (le_trans A (mult (mult A B) (inv_pos B HB)) (inv_pos B HB)).
  - exact (le_id_l A (mult (mult A B) (inv_pos B HB))
                     (mult (mult A B) (inv_pos B HB))
             (req_trans _ _ _
                (req_trans _ _ _
                   (req_sym _ _ (mult_one A))
                   (cmk_mult_congr_l A (req_sym _ _ (inv_pos_correct B HB))))
                (mult_assoc A B (inv_pos B HB)))
             (le_refl (mult (mult A B) (inv_pos B HB)))).
  - exact (le_id_r (mult (mult A B) (inv_pos B HB))
                     (mult one (inv_pos B HB)) (inv_pos B HB)
             (cmk_mult_one_l (inv_pos B HB))
             (le_mult_compat (mult A B) one (inv_pos B HB) HBp HAB)).
Defined.

(* ============================================================ *)
(* Part 6：k 选取尾链核（@ums_pow_tail）                                *)
(* ============================================================ *)

Lemma cmk_pow_tail :
  forall (kappa TV0 budget w : R) (N : nat)
         (Hwb : lt zero (mult w budget)),
    lt zero w -> lt w one -> req kappa (req_minus one w) ->
    le zero TV0 -> le zero budget ->
    lt (mult TV0 (inv_pos (mult w budget) Hwb))
       (cmk_scale (Datatypes.S N) one) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget w N Hwb Hw0 Hwlt1 Heqk Ha Hbudget0 HN.
  assert (Hwle : le zero w) by exact (lt_le_iff zero w (inl Hw0)).
  set (wb := mult w budget).
  set (invwb := inv_pos wb Hwb).
  set (Ms := cmk_scale (Datatypes.S N) w).
  set (boost := plus one Ms).
  assert (Hboost0 : lt zero boost)
    by exact (cmk_boost_pos w (Datatypes.S N) Hwle).
  set (invB := inv_pos boost Hboost0).
  assert (HinvB : lt zero invB) by exact (inv_pos_pos boost Hboost0).
  (* ---- 预算腿：TV0 < Ms·budget ---- *)
  assert (Hstep : lt (mult (mult TV0 invwb) wb)
                       (mult (cmk_scale (Datatypes.S N) one) wb))
    by exact (lt_mult_compat (mult TV0 invwb)
                (cmk_scale (Datatypes.S N) one) wb Hwb HN).
  assert (HeqL : req (mult (mult TV0 invwb) wb) TV0)
    by exact (req_trans _ _ _
                (mult_comm (mult TV0 invwb) wb)
                (cmk_mult_div wb TV0 Hwb)).
  assert (HeqR : req (mult (cmk_scale (Datatypes.S N) one) wb)
                       (mult Ms budget))
    by exact (req_trans _ _ _
           (req_trans _ _ _
              (cmk_scale_mult_distrib (Datatypes.S N) one wb)
              (cmk_scale_congr (Datatypes.S N) (mult one wb) wb
                 (cmk_mult_one_l wb)))
           (req_sym _ _ (cmk_scale_mult_distrib (Datatypes.S N) w budget))).
  assert (Hb0 : lt TV0 (mult Ms budget)).
  { exact (lt_id_r TV0 (mult (cmk_scale (Datatypes.S N) one) wb)
             (mult Ms budget) HeqR
             (lt_id_l TV0 (mult (mult TV0 invwb) wb)
                (mult (cmk_scale (Datatypes.S N) one) wb)
                (req_sym _ _ HeqL) Hstep)). }
  assert (HeqBud : req (mult budget boost) (plus budget (mult Ms budget)))
    by exact (req_trans _ _ _
                (distrib budget one Ms)
                (req_trans _ _ _
                   (cmk_plus_congr_r (mult budget Ms) (mult_one budget))
                   (cmk_plus_congr_l budget (mult_comm budget Ms)))).
  assert (Hbud : lt TV0 (mult budget boost)).
  { exact (lt_id_r TV0 (plus (mult Ms budget) budget) (mult budget boost)
             (req_sym _ _ (req_trans _ _ _ HeqBud
                             (plus_comm budget (mult Ms budget))))
             (lt_le_trans TV0 (mult Ms budget)
                (plus (mult Ms budget) budget) Hb0
                (cmk_le_plus_r (mult Ms budget) budget Hbudget0))). }
  exists (Datatypes.S N).
  (* ---- 主链：κ^(S N)·TV0 < budget ---- *)
  assert (Heqp : req (cmk_r_pow kappa (Datatypes.S N))
                       (cmk_r_pow (req_minus one w) (Datatypes.S N)))
    by exact (cmk_rpow_eq_compat kappa (req_minus one w) (Datatypes.S N) Heqk).
  assert (Hbern : le (mult (cmk_r_pow (req_minus one w) (Datatypes.S N)) boost) one)
    by exact (cmk_bernoulli_upper w (Datatypes.S N) Hw0 Hwlt1).
  assert (Hinvleg : le (cmk_r_pow (req_minus one w) (Datatypes.S N)) invB)
    by exact (cmk_le_inv (cmk_r_pow (req_minus one w) (Datatypes.S N)) boost
                Hboost0 Hbern).
  apply (le_lt_trans _ (mult invB TV0) budget).
  + exact (le_id_l (mult (cmk_r_pow kappa (Datatypes.S N)) TV0)
                     (mult (cmk_r_pow (req_minus one w) (Datatypes.S N)) TV0)
                     (mult invB TV0)
             (cmk_mult_congr_r TV0 Heqp)
             (le_mult_compat_weak (cmk_r_pow (req_minus one w) (Datatypes.S N))
                invB TV0 Ha Hinvleg)).
  + exact (lt_id_r (mult invB TV0)
              (mult (mult budget boost) invB) budget
              (req_trans _ _ _
                 (cmk_mult_congr_r invB (mult_comm budget boost))
                 (req_trans _ _ _
                    (req_sym _ _ (mult_assoc boost budget invB))
                    (cmk_mult_div boost budget Hboost0)))
              (lt_id_l (mult invB TV0) (mult TV0 invB)
                 (mult (mult budget boost) invB)
                 (mult_comm invB TV0)
                 (lt_mult_compat TV0 (mult budget boost) invB HinvB Hbud))).
Defined.

(* ============================================================ *)
(* Part 7：选择器双头（@ums_k_select / ums_pow_budget / ums_k_select_le）  *)
(* ============================================================ *)

(* 主形：le 前件 + le 形 Arch 直给（@ums_k_select 同形镜像） *)
Lemma cmk_k_select :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (req_minus one kappa))
    by exact (cmk_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (req_minus one kappa) one).
  { apply (lt_id_r (req_minus one kappa)
             (plus kappa (req_minus one kappa)) one
             (req_trans _ _ _ (plus_comm kappa (req_minus one kappa))
                       (cmk_minus_plus_cancel one kappa))).
    apply (lt_id_l (req_minus one kappa) (plus zero (req_minus one kappa))
             (plus kappa (req_minus one kappa))
             (req_sym _ _
                (req_trans _ _ _ (plus_comm zero (req_minus one kappa))
                           (plus_zero (req_minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (req_minus one kappa)
               (req_minus one kappa) Hk1 (le_refl (req_minus one kappa))). }
  assert (Heqk : req kappa (req_minus one (req_minus one kappa)))
    by exact (cmk_omd_id kappa).
  assert (Hwb : lt zero (mult (req_minus one kappa) budget))
    by exact (mult_positive (req_minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (req_minus one kappa) budget) Hwb).
  (* Arch 应用点：TV0·inv(w·budget) ≥ 0（le 前件经 weak 乘法保序） *)
  assert (Hxle : le zero (mult TV0
                     (inv_pos (mult (req_minus one kappa) budget) Hwb))).
  { exact (le_id_l zero
             (mult zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
             (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
             (req_sym _ _
                (req_trans _ _ _
                   (mult_comm zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
                   (mult_zero (inv_pos (mult (req_minus one kappa) budget) Hwb))))
             (le_mult_compat_weak zero TV0
                (inv_pos (mult (req_minus one kappa) budget) Hwb)
                (lt_le_iff zero
                   (inv_pos (mult (req_minus one kappa) budget) Hwb)
                   (inl Hinvwbp)) Ha)). }
  destruct (Harch (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
                  Hxle) as [N HN].
  exact (cmk_pow_tail kappa TV0 budget (req_minus one kappa) N Hwb
           hwp hwlt Heqk Ha (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* 严格版（lt 前件 + lt 形 Arch；@ums_pow_budget 同形镜像） *)
Lemma cmk_pow_budget :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    lt zero TV0 -> lt zero budget ->
    (forall x : R, lt zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => lt (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  assert (hwp : lt zero (req_minus one kappa))
    by exact (cmk_omd_lt_one kappa Hk1 Hk2).
  assert (hwlt : lt (req_minus one kappa) one).
  { apply (lt_id_r (req_minus one kappa)
             (plus kappa (req_minus one kappa)) one
             (req_trans _ _ _ (plus_comm kappa (req_minus one kappa))
                       (cmk_minus_plus_cancel one kappa))).
    apply (lt_id_l (req_minus one kappa) (plus zero (req_minus one kappa))
             (plus kappa (req_minus one kappa))
             (req_sym _ _
                (req_trans _ _ _ (plus_comm zero (req_minus one kappa))
                           (plus_zero (req_minus one kappa))))).
    exact (lt_plus_compat_lt_le zero kappa (req_minus one kappa)
               (req_minus one kappa) Hk1 (le_refl (req_minus one kappa))). }
  assert (Heqk : req kappa (req_minus one (req_minus one kappa)))
    by exact (cmk_omd_id kappa).
  assert (Hwb : lt zero (mult (req_minus one kappa) budget))
    by exact (mult_positive (req_minus one kappa) budget hwp Hbudget).
  assert (Hinvwbp : lt zero (inv_pos (mult (req_minus one kappa) budget) Hwb))
    by exact (inv_pos_pos (mult (req_minus one kappa) budget) Hwb).
  (* Arch 应用点：TV0·inv(w·budget) > 0（严格前件经乘法保序） *)
  assert (Hx : lt zero (mult TV0
                   (inv_pos (mult (req_minus one kappa) budget) Hwb)))
    by exact (mult_positive TV0
                (inv_pos (mult (req_minus one kappa) budget) Hwb) Ha Hinvwbp).
  destruct (Harch (mult TV0 (inv_pos (mult (req_minus one kappa) budget) Hwb))
                  Hx) as [N HN].
  exact (cmk_pow_tail kappa TV0 budget (req_minus one kappa) N Hwb
           hwp hwlt Heqk (lt_le_iff zero TV0 (inl Ha))
           (lt_le_iff zero budget (inl Hbudget)) HN).
Defined.

(* ≤ 版（同前件，结论降温 lt→le；@ums_k_select_le 同形镜像） *)
Lemma cmk_k_select_le :
  forall (kappa TV0 budget : R),
    lt zero kappa -> lt kappa one ->
    le zero TV0 -> lt zero budget ->
    (forall x : R, le zero x ->
       sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
    sigT (fun k : nat => le (mult (cmk_r_pow kappa k) TV0) budget).
Proof.
  intros kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch.
  destruct (cmk_k_select kappa TV0 budget Hk1 Hk2 Ha Hbudget Harch)
    as [k Hk].
  exists k.
  exact (lt_le_iff (mult (cmk_r_pow kappa k) TV0) budget (inl Hk)).
Defined.

End CmkMixSelect.

(* 幂机器换形桥：cmk_r_pow == req_r_pow（两同构 Fixpoint 的 req 逐步转换；     *)
(*   中性 k 上两种 fix 非转换可判——须归纳证明，恰为 S2/S3 两幂机器的缝合位） *)
Section CmkRPowBridge.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Lemma cmk_r_pow_req_r_pow : forall (x : R) (k : nat),
  req (cmk_r_pow x k) (req_r_pow x k).
Proof.
  intro x. induction k as [| k IH].
  - exact (req_refl one).
  - exact (req_mult_compat x x _ _ (req_refl x) IH).
Defined.
End CmkRPowBridge.

(* ============================================================ *)
(* Section CmkMixTime：S3 · 合龙件 req 面镜像（amt_ 系逐件）            *)
(*   求和诚实接口六槽（rsq ReqBoundedSoftmax 同位，abs_sum_le_h 为       *)
(*   plain 形冻结槽——AT5 槽位警告：具体层由 csm_abs_sum_le_eps 供        *)
(*   逐 eps 形或 B1 一元 enum 平推，终装消解归 S8）。                    *)
(* ============================================================ *)

Section CmkMixTime.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* 诚实接口：混合 lt+le 加法保序（与 S2 同位） *)
Variable lt_plus_compat_lt_le : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和诚实接口（rsq 同位六槽） ---- *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s : S => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
(* 求和三角：|Σ f| ≤ Σ |f|（plain 形冻结槽；UpReqSampling abs_sum_le_h 同位） *)
Hypothesis abs_sum_le_h :
  forall f : S -> R, le (abs (sumf f)) (sumf (fun s : S => abs (f s))).

(* ---- 有限世界数据（Id 面 amt 节 Variable 全集 req 镜像） ---- *)
Variable enum : list S.
Variable enum_nonempty : Not (enum = nil).
Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable z : S -> S -> R.
Variable z_lb : forall s s' : S, le (opp Delta) (z s s').
Variable z_ub : forall s s' : S, le (z s s') Delta.
Variable bs_swap : forall f : S -> S -> R,
  req (sumf (fun s : S => sumf (fun s' : S => f s s')))
      (sumf (fun s' : S => sumf (fun s : S => f s s'))).
Variable bs_abs : forall a : R, le zero a -> req (abs a) a.
Variable bs_lpc : forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Variable sum_eq_list : forall g : S -> R, req (sumf g) (rsq_bs_list_sum S g enum).

(* ---- 核实例数据（rsq 混合率形：expf := rsq_exp_pos_fn，AT5 expf 供给予   *)
(*      cmk_expf_realizable（件尾）一件全供镜像） ---- *)
Let invT := inv_pos temp temp_pos.
Let lo := rsq_exp_pos_fn (mult invT (opp Delta)).
Let delta_star := mult lo lo.
Let omd := req_minus one delta_star.

(* TV 算子与迭代器（rsq tv_req/k_titer 形req 自持；出节与 rsq 链可转换） *)
Let inv_two := inv_pos (plus one one) req_two_pos.
Let cmk_tv (mu nu : S -> R) : R :=
  mult inv_two (sumf (fun s : S => abs (req_minus (mu s) (nu s)))).
Let cmk_titer (n : nat) (mu : S -> R) : S -> R :=
  k_titer S sumf enum enum_nonempty temp temp_pos Delta z z_lb sum_eq_list n mu.

(* ================= B 档：放电件消费桥（@amt B 档镜像） ================= *)

(* δ* < 1（消费 rsq_bs_delta_star_lt_one；@amt_ds_lt_one） *)
Lemma cmk_ds_lt_one : lt delta_star one.
Proof.
  exact (rsq_bs_delta_star_lt_one temp temp_pos Delta Delta_pos).
Qed.

(* 1 − δ* > 0（@amt_omd_pos；lpc 槽同位喂 bs_lpc） *)
Lemma cmk_omd_pos : lt zero omd.
Proof.
  exact (lt_id_l zero (plus delta_star (opp delta_star)) omd
           (req_sym _ _ (plus_opp delta_star))
           (lt_plus_compat_lt_le delta_star one (opp delta_star)
              (opp delta_star) cmk_ds_lt_one (le_refl (opp delta_star)))).
Qed.

(* ================= A 档：自证胶水（@amt A 档镜像） ================= *)

(* one = 1−δ*+δ* （@amt_one_eq；req 链三段）*)
Lemma cmk_one_eq : req one (plus omd delta_star).
Proof.
  apply req_sym.
  exact (req_trans (plus (plus one (opp delta_star)) delta_star)
                     (plus one (plus (opp delta_star) delta_star)) one
           (req_sym _ _ (plus_assoc one (opp delta_star) delta_star))
           (req_trans (plus one (plus (opp delta_star) delta_star))
                      (plus one zero) one
              (req_plus_compat one one
                 (plus (opp delta_star) delta_star) zero
                 (req_refl one)
                 (req_trans (plus (opp delta_star) delta_star)
                            (plus delta_star (opp delta_star)) zero
                            (plus_comm (opp delta_star) delta_star)
                            (plus_opp delta_star)))
              (plus_zero one))).
Qed.

(* 1−δ* < one：δ* > 0 退化端（@amt_omd_lt_one；bs_lpc 严格缝合 + 双侧换形） *)
Lemma cmk_ds_omd_lt_one : lt omd one.
Proof.
  assert (Hds : lt zero delta_star).
  { exact (mult_positive lo lo
             (exp_neg_pos (opp (mult invT (opp Delta))))
             (exp_neg_pos (opp (mult invT (opp Delta))))). }
  assert (Hcore : lt (plus zero (plus one (opp delta_star)))
                     (plus delta_star (plus one (opp delta_star)))).
  { exact (bs_lpc zero delta_star (plus one (opp delta_star))
                  (plus one (opp delta_star))
                  Hds (le_refl (plus one (opp delta_star)))). }
  assert (Hshift : lt (plus one (opp delta_star))
                      (plus (plus one (opp delta_star)) delta_star)).
  { exact (req_lt_id_r_loc _ _ _
             (plus_comm delta_star (plus one (opp delta_star)))
             (lt_id_l _ _ _
                (req_sym _ _
                   (req_trans _ _ _ (plus_comm zero (plus one (opp delta_star)))
                              (plus_zero (plus one (opp delta_star)))))
                Hcore)). }
  exact (req_lt_id_r_loc _ _ _ (req_sym _ _ cmk_one_eq) Hshift).
Qed.

(* ================= C 档：合龙主件（@amt C 档镜像） ================= *)

(* 合龙定理（严格版）：TV(T^k μ, T^k ν) < budget
   TV₀ 非负诚实证书位 Htv0：req 面 abs≥0 的 plain le 形属 Or 墙（类字段
   abs_nonneg 仅 Bishop 逐 eps 形），Id 面 tv_dist_nonneg 的无条件件在
   req 面无同款——显式证书参数保持面诚实（AT5 槽位警告同族申报）。 *)
Theorem cmk_attention_mixing_time :
  forall mu nu : S -> R,
  req (sumf mu) one -> req (sumf nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  le zero (cmk_tv mu nu) ->
  sigT (fun k : nat =>
    lt (cmk_tv (cmk_titer k mu) (cmk_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  destruct (cmk_k_select lt_plus_compat_lt_le omd (cmk_tv mu nu) budget
              cmk_omd_pos cmk_ds_omd_lt_one Htv0 Hbudget Harch) as [k Hk].
  exists k.
  apply (le_lt_trans _ (mult (cmk_r_pow omd k) (cmk_tv mu nu))).
  - (* req_r_pow（rsq 链幂机器）→ cmk_r_pow（S2 选择器幂机器）req 换形 *)
    exact (le_id_r (cmk_tv (cmk_titer k mu) (cmk_titer k nu))
                     (mult (req_r_pow omd k) (cmk_tv mu nu))
                     (mult (cmk_r_pow omd k) (cmk_tv mu nu))
             (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                (cmk_tv mu nu) (cmk_tv mu nu)
                (req_sym _ _ (cmk_r_pow_req_r_pow omd k))
                (req_refl (cmk_tv mu nu)))
             (rsq_bounded_softmax_tv_iter S sumf sum_ext sum_linear sum_add
                sum_le abs_sum_le_h enum enum_nonempty temp temp_pos Delta
                Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc sum_eq_list
                k mu nu Hmu Hnu)).
  - exact Hk.
Defined.

(* 合龙定理（非严格版）：TV(T^k μ, T^k ν) ≤ budget *)
Theorem cmk_attention_mixing_time_le :
  forall mu nu : S -> R,
  req (sumf mu) one -> req (sumf nu) one ->
  forall budget : R, lt zero budget ->
  (forall x : R, le zero x ->
     sigT (fun N : nat => lt x (cmk_scale (Datatypes.S N) one))) ->
  le zero (cmk_tv mu nu) ->
  sigT (fun k : nat =>
    le (cmk_tv (cmk_titer k mu) (cmk_titer k nu)) budget).
Proof.
  intros mu nu Hmu Hnu budget Hbudget Harch Htv0.
  destruct (cmk_k_select_le lt_plus_compat_lt_le omd (cmk_tv mu nu) budget
              cmk_omd_pos cmk_ds_omd_lt_one Htv0 Hbudget Harch) as [k Hk].
  exists k.
  apply (le_trans _ (mult (cmk_r_pow omd k) (cmk_tv mu nu))).
  - (* req_r_pow（rsq 链幂机器）→ cmk_r_pow（S2 选择器幂机器）req 换形 *)
    exact (le_id_r (cmk_tv (cmk_titer k mu) (cmk_titer k nu))
                     (mult (req_r_pow omd k) (cmk_tv mu nu))
                     (mult (cmk_r_pow omd k) (cmk_tv mu nu))
             (req_mult_compat (req_r_pow omd k) (cmk_r_pow omd k)
                (cmk_tv mu nu) (cmk_tv mu nu)
                (req_sym _ _ (cmk_r_pow_req_r_pow omd k))
                (req_refl (cmk_tv mu nu)))
             (rsq_bounded_softmax_tv_iter S sumf sum_ext sum_linear sum_add
                sum_le abs_sum_le_h enum enum_nonempty temp temp_pos Delta
                Delta_pos z z_lb z_ub bs_swap bs_abs bs_lpc sum_eq_list
                k mu nu Hmu Hnu)).
  - exact Hk.
Defined.

End CmkMixTime.

(* ============================================================ *)
(* 具体层锚点：expf 迷你接口 req 面一件全供（AttnDoeblin Part C 镜像）     *)
(*   real_expf_realizable 的五性质即 req 面语句（real_lt/real_eq/real_le  *)
(*   = 实例 RealEnhancedReal 的 lt/req/le 字段值），拆件直给终装 S8。      *)
(* ============================================================ *)

Lemma cmk_expf_realizable :
  sigT (fun f : Real -> Real => And (forall x : Real, lt zero (f x))
        (And (req (f zero) one)
        (And (forall a b : Real, req (f (plus a b)) (mult (f a) (f b)))
        (And (forall a b : Real, lt a b -> lt (f a) (f b))
             (forall a b : Real, le a b -> le (f a) (f b)))))).
Proof. exact real_expf_realizable. Qed.

(* ============ G4 证据：新件零外部未证假设（全 Closed，前提=显式参数） ============ *)
Print Assumptions cmk_k_select.
Print Assumptions cmk_pow_budget.
Print Assumptions cmk_k_select_le.
Print Assumptions cmk_bernoulli_upper.
Print Assumptions cmk_attention_mixing_time.
Print Assumptions cmk_attention_mixing_time_le.
Print Assumptions cmk_expf_realizable.
