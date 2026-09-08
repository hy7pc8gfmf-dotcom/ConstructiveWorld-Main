(* ========================================================================= *)
(* UpEvictIdReq.v — 签名迁移批 4 第二席：UpEvictId 的 req 伴件（14 件）      *)
(*   母件：attn\UpEvictId.v（§6 KV 逐出恒等式批，2026-09-07）                *)
(*   规划书：docs\签名迁移规划书-20260908.md 批 4「模块伴件」                *)
(*   伴件形态：req_* 独立伴 Section，与母件同树（attn 目录）                 *)
(* ------------------------------------------------------------------------- *)
(* 覆盖对账（req 件名 -> 母件 Id 原件 @ 行号；件数规则：陈述含 Id 或证明核    *)
(* 为 Id 搬运的声明，Variable 假设位计入；grep 实测 16 声明，冻结扣除 2）：   *)
(*   件 1  req 假设位 transition_normalization    <- 母件 L65（Id 求和归一） *)
(*   件 2  req 假设位 detailed_balance            <- 母件 L68（Id 详细平衡） *)
(*   件 3  req_boltzmann_factor_detailed_balance  <- 母件 L117               *)
(*   件 4  req_evicted_db_products                <- 母件 L154               *)
(*   件 5  req_eviction_db_breaking_zero          <- 母件 L185（旗舰一）     *)
(*   件 6  req_evicted_boltzmann_steady_exact     <- 母件 L202（旗舰二）     *)
(*   件 7  req_eviction_transition_pointwise_full <- 母件 L216               *)
(*   件 8  req_evicted_transition_row_sum_one     <- 母件 L230               *)
(*   件 9  req_evicted_boltzmann_steady_full_keep <- 母件 L242               *)
(*   件 10 req_eviction_steady_deviation_zero     <- 母件 L259               *)
(*   件 11 req_eviction_steady_deviation_le_zero  <- 母件 L274               *)
(*   件 12 req_partition_increment_pointwise      <- 母件 L290               *)
(*   件 13 req_eviction_partition_increment       <- 母件 L313               *)
(*   件 14 req_eviction_partition_le_full_exact   <- 母件 L336               *)
(*   冻结扣除（2 件，批 4 (d) 清单理由回写）：                                *)
(*   - 母件 opp_zero_u @L101：req 同位件批 2 已交付（UpReqDist               *)
(*     ReqDistCommon reqd_opp_zero），本件消费不重建。                        *)
(*   - 母件 minus_zero_r_u @L107：req 同位件批 2 已交付（UpReqDist           *)
(*     ReqDistCommon reqd_minus_zero_r），件 12/14 直接消费。                 *)
(* ------------------------------------------------------------------------- *)
(* 每处 Id→req 差异真证非抄写：母件 id_trans/id_cong/id_sym 链逐处换         *)
(* req_trans/req_mult_compat/req_sym；母件局部 minus_self_zero 换批 1        *)
(* req_minus_self_zero；求和换形换 req_sum 假设位 + 批 2 reqd_sum_minus。    *)
(* 假设位纪律：件 1/2 逐位保留母件 Id 前提的 req 同形（req 归一/req 详细      *)
(* 平衡），不放大主张；transition_nonneg 母件同位保留（14 件未消费，同位     *)
(* 声明以保世界逐字对齐）。                                                  *)
(* 非平凡性分级：件 3/4/6/13/14 = A（req 链真证，分支工艺逐支构造）；        *)
(* 件 5/9/10 = A-（引擎件一步装配）；件 7/12 = B（分支枚举 + 矛盾消去，     *)
(* 仅 req_refl 换形）；件 8/11 = B（字段直引）；件 1/2 = 假设位迁移。       *)
(* 纪律：纯 term-mode（零 rewrite/零 Morphisms）；语句全 Set 层              *)
(* （req/le/lt/Or/sigT 皆 Set 值，零 Prop 泄露）；全 Qed 收口；零禁词。      *)
(* ========================================================================= *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Import RealInterfaceEnhancedMod.

Section EvictIdReq.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let opp := @opp R RIS.
Let abs := @abs R RIS.
Let lt := @lt R RIS.
Let le := @le R RIS.
Let inv_pos := @inv_pos R RIS.
Let exp_neg := @exp_neg R RIS.

(* ---- req 求和假设位（母件 SumOver 类 CW219 L1400 本件消费字段逐位 req 化：
   linear / add / ext 三件；le / nonneg / zero_nonneg / abs 三角字段母件
   14 件未消费，不设槽） ---- *)
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).

(* ---- 与母件同款逐出世界（变量名/前提形态逐行对齐） ---- *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sumf boltzmann_factor.

Variable Z_thermo_pos : lt zero Z_thermo.

Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').

(* 件 1：母件 L65 Id 求和归一的 req 同形（假设位逐位保留） *)
Variable transition_normalization :
  forall s, req (sumf (fun s' => transition s s')) one.

(* 件 2：母件 L68 Id 详细平衡的 req 同形（假设位逐位保留） *)
Variable detailed_balance :
  forall s s',
    req (mult (boltzmann_dist_attn s) (transition s s'))
        (mult (boltzmann_dist_attn s') (transition s' s)).

Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evicted_partition : R :=
  sumf (fun s => if keep_dec s then boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evicted_partition.

Definition evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition evicted_partition_pos) (boltzmann_factor s)
  else zero.

Definition db_breaking (s s' : S) : R :=
  abs (req_minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                 (mult (evicted_boltzmann s') (evicted_transition s' s))).

(* 保留集参数化的条件配分函数（母件 L96 同形） *)
Definition evicted_partition_of (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sumf (fun s => if kd s then boltzmann_factor s else zero).

(* ---- 件 3：因子层详细平衡（req 链真证：母件 id_trans/id_cong 全链换
   req_trans/req_mult_compat；inv_pos_correct 字段吸收 Z_thermo 逆元） ---- *)

(* Z·(invZ·f) == f（逆元缩放核，s/s' 两支共用） *)
Lemma req_evict_zinv_scale :
  forall s0 : S,
    req (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s0)))
        (boltzmann_factor s0).
Proof.
  intro s0.
  assert (Hinv : req (mult Z_thermo (inv_pos Z_thermo Z_thermo_pos)) one).
  { exact (inv_pos_correct Z_thermo Z_thermo_pos). }
  apply (req_trans (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s0)))
                   (mult (mult Z_thermo (inv_pos Z_thermo Z_thermo_pos)) (boltzmann_factor s0))
                   (boltzmann_factor s0)).
  - apply mult_assoc.
  - apply (req_trans (mult (mult Z_thermo (inv_pos Z_thermo Z_thermo_pos)) (boltzmann_factor s0))
                     (mult one (boltzmann_factor s0))
                     (boltzmann_factor s0)).
    + exact (req_mult_compat (mult Z_thermo (inv_pos Z_thermo Z_thermo_pos)) one
                             (boltzmann_factor s0) (boltzmann_factor s0)
                             Hinv (req_refl (boltzmann_factor s0))).
    + exact (req_trans (mult one (boltzmann_factor s0))
                       (mult (boltzmann_factor s0) one)
                       (boltzmann_factor s0)
                       (mult_comm one (boltzmann_factor s0))
                       (mult_one (boltzmann_factor s0))).
Qed.

Lemma req_boltzmann_factor_detailed_balance :
  forall s s' : S,
    req (mult (boltzmann_factor s) (transition s s'))
        (mult (boltzmann_factor s') (transition s' s)).
Proof.
  intros s s'.
  pose proof (detailed_balance s s') as Hdb.
  unfold boltzmann_dist_attn in Hdb.
  (* HZl : Z·((invZ·f s)·t s s') == f s·t s s' *)
  assert (HZl : req (mult Z_thermo
                          (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                                (transition s s')))
                    (mult (boltzmann_factor s) (transition s s'))).
  { apply (req_trans
             (mult Z_thermo
                   (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                         (transition s s')))
             (mult (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
                   (transition s s'))
             (mult (boltzmann_factor s) (transition s s'))).
    - apply mult_assoc.
    - exact (req_mult_compat
                (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s)))
                (boltzmann_factor s)
                (transition s s') (transition s s')
                (req_evict_zinv_scale s)
                (req_refl (transition s s'))). }
  (* HZr : Z·((invZ·f s')·t s' s) == f s'·t s' s *)
  assert (HZr : req (mult Z_thermo
                          (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                                (transition s' s)))
                    (mult (boltzmann_factor s') (transition s' s))).
  { apply (req_trans
             (mult Z_thermo
                   (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                         (transition s' s)))
             (mult (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s')))
                   (transition s' s))
             (mult (boltzmann_factor s') (transition s' s))).
    - apply mult_assoc.
    - exact (req_mult_compat
                (mult Z_thermo (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s')))
                (boltzmann_factor s')
                (transition s' s) (transition s' s)
                (req_evict_zinv_scale s')
                (req_refl (transition s' s))). }
  exact (req_trans
           (mult (boltzmann_factor s) (transition s s'))
           (mult Z_thermo
                 (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                       (transition s s')))
           (mult (boltzmann_factor s') (transition s' s))
           (req_sym (mult Z_thermo
                          (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                                (transition s s')))
                    (mult (boltzmann_factor s) (transition s s'))
                    HZl)
           (req_trans
              (mult Z_thermo
                    (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                          (transition s s')))
              (mult Z_thermo
                    (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                          (transition s' s)))
              (mult (boltzmann_factor s') (transition s' s))
              (req_mult_compat Z_thermo Z_thermo
                 (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                       (transition s s'))
                 (mult (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                       (transition s' s))
                 (req_refl Z_thermo) Hdb)
              HZr)).
Qed.

(* ---- 件 4：掩码核逐点详细平衡（req 真证：4 分支全构造性，双保留支
   由件 3 + mult assoc/compat req 字段缩放 evicted_partition 逆元） ---- *)
Lemma req_evicted_db_products :
  forall s s' : S,
    req (mult (evicted_boltzmann s') (evicted_transition s' s))
        (mult (evicted_boltzmann s) (evicted_transition s s')).
Proof.
  intros s s'.
  unfold evicted_boltzmann, evicted_transition.
  destruct (keep_dec s) as [Hs | Hs]; destruct (keep_dec s') as [Hs' | Hs'].
  - (* 双保留：inv_ev·f(s')·t(s',s) == inv_ev·f(s)·t(s,s')（三跳 req 链） *)
    apply (req_trans
             (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                         (boltzmann_factor s'))
                   (transition s' s))
             (mult (inv_pos evicted_partition evicted_partition_pos)
                   (mult (boltzmann_factor s') (transition s' s)))
             (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                         (boltzmann_factor s))
                   (transition s s'))).
    + exact (req_sym (mult (inv_pos evicted_partition evicted_partition_pos)
                           (mult (boltzmann_factor s') (transition s' s)))
                     (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                                 (boltzmann_factor s'))
                           (transition s' s))
                     (mult_assoc (inv_pos evicted_partition evicted_partition_pos)
                                 (boltzmann_factor s') (transition s' s))).
    + apply (req_trans
                (mult (inv_pos evicted_partition evicted_partition_pos)
                      (mult (boltzmann_factor s') (transition s' s)))
                (mult (inv_pos evicted_partition evicted_partition_pos)
                      (mult (boltzmann_factor s) (transition s s')))
                (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                            (boltzmann_factor s))
                      (transition s s'))).
      * exact (req_mult_compat
                  (inv_pos evicted_partition evicted_partition_pos)
                  (inv_pos evicted_partition evicted_partition_pos)
                  (mult (boltzmann_factor s') (transition s' s))
                  (mult (boltzmann_factor s) (transition s s'))
                  (req_refl (inv_pos evicted_partition evicted_partition_pos))
                  (req_sym (mult (boltzmann_factor s) (transition s s'))
                           (mult (boltzmann_factor s') (transition s' s))
                           (req_boltzmann_factor_detailed_balance s s'))).
      * apply mult_assoc.
  - (* s 保留、s' 逐出：两积同为零 *)
    exact (req_trans (mult zero zero) zero
                     (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                                 (boltzmann_factor s))
                           zero)
                     (mult_zero zero)
                     (req_sym (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                                          (boltzmann_factor s))
                                    zero)
                              zero
                              (mult_zero (mult (inv_pos evicted_partition evicted_partition_pos)
                                               (boltzmann_factor s))))).
  - (* s 逐出、s' 保留：两积同为零 *)
    exact (req_trans (mult (mult (inv_pos evicted_partition evicted_partition_pos)
                                 (boltzmann_factor s'))
                           zero)
                     zero
                     (mult zero zero)
                     (mult_zero (mult (inv_pos evicted_partition evicted_partition_pos)
                                      (boltzmann_factor s')))
                     (req_sym (mult zero zero) zero (mult_zero zero))).
  - (* 双逐出 *)
    exact (req_refl (mult zero zero)).
Qed.

(* ================= 件 5（旗舰一）：破缺恒为零 ============================= *)
(* 母件 L185：|db| 恒零。req 差异真证：母件局部 minus_self_zero 换批 1
   req_minus_self_zero（引擎 L728），abs 换形走 req_abs_compat + abs_zero。 *)
Theorem req_eviction_db_breaking_zero :
  forall s s' : S, req (db_breaking s s') zero.
Proof.
  intros s s'.
  unfold db_breaking.
  exact (req_trans
           (abs (req_minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                           (mult (evicted_boltzmann s') (evicted_transition s' s))))
           (abs zero)
           zero
           (req_abs_compat
              (req_minus (mult (evicted_boltzmann s) (evicted_transition s s'))
                         (mult (evicted_boltzmann s') (evicted_transition s' s)))
              zero
              (req_minus_self_zero
                 (mult (evicted_boltzmann s) (evicted_transition s s'))
                 (mult (evicted_boltzmann s') (evicted_transition s' s))
                 (req_sym (mult (evicted_boltzmann s') (evicted_transition s' s))
                          (mult (evicted_boltzmann s) (evicted_transition s s'))
                          (req_evicted_db_products s s'))))
           abs_zero).
Qed.

(* ================= 件 6（旗舰二）：截断核稳态方程（精确恒等式） ============ *)
(* 母件 L202：Σ ev_b·ev_t == ev_b(s)·Σ ev_t。req 差异真证：sum_over_S_ext 换
   req sum_ext 假设位（逐点 req_sym 件 4），sum_over_S_linear 换 req
   sum_linear 假设位。 *)
Theorem req_evicted_boltzmann_steady_exact :
  forall s : S,
    req (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
        (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s'))).
Proof.
  intro s.
  apply (req_trans
           (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
           (sumf (fun s' => mult (evicted_boltzmann s) (evicted_transition s s')))
           (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))).
  - exact (sum_ext
             (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))
             (fun s' => mult (evicted_boltzmann s) (evicted_transition s s'))
             (fun s' => req_sym (mult (evicted_boltzmann s) (evicted_transition s s'))
                                (mult (evicted_boltzmann s') (evicted_transition s' s))
                                (req_evicted_db_products s' s))).
  - exact (sum_linear (evicted_boltzmann s) (fun s' => evicted_transition s s')).
Qed.

(* ---- 件 7：全保留桥（母件 L216；req 差异仅 req_refl 换形——
   evicted_transition 定义零 Id 内容，分支枚举 + 矛盾消去同母件） ---- *)
Lemma req_eviction_transition_pointwise_full :
  (forall s, keep s) ->
  forall s s' : S, req (evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + exact (req_refl (transition s s')).
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* ---- 件 8：全保留时掩码核行归一化（母件 L230；req 求和假设位直引） ---- *)
Lemma req_evicted_transition_row_sum_one :
  (forall s, keep s) ->
  forall s : S, req (sumf (fun s' => evicted_transition s s')) one.
Proof.
  intros Hkall s.
  apply (req_trans (sumf (fun s' => evicted_transition s s'))
                   (sumf (fun s' => transition s s')) one).
  - exact (sum_ext (fun s' => evicted_transition s s')
                   (fun s' => transition s s')
                   (fun s' => req_eviction_transition_pointwise_full Hkall s s')).
  - exact (transition_normalization s).
Qed.

(* ---- 件 9：全保留特例（母件 L242；req_mult_one_r 收口） ---- *)
Corollary req_evicted_boltzmann_steady_full_keep :
  (forall s, keep s) ->
  forall s : S,
    req (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
        (evicted_boltzmann s).
Proof.
  intros Hkall s.
  apply (req_trans
           (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
           (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))
           (evicted_boltzmann s)).
  - exact (req_evicted_boltzmann_steady_exact s).
  - exact (req_trans
             (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))
             (mult (evicted_boltzmann s) one)
             (evicted_boltzmann s)
             (req_mult_compat (evicted_boltzmann s) (evicted_boltzmann s)
                              (sumf (fun s' => evicted_transition s s')) one
                              (req_refl (evicted_boltzmann s))
                              (req_evicted_transition_row_sum_one Hkall s))
             (req_mult_one_r (evicted_boltzmann s))).
Qed.

(* ---- 件 10：定理 6.1 偏差恒为零（母件 L259；req_minus_self_zero 引擎件） ---- *)
Theorem req_eviction_steady_deviation_zero :
  forall s : S,
    req (abs (req_minus
                 (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                 (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))))
         zero.
Proof.
  intro s.
  exact (req_trans
           (abs (req_minus
                   (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))))
           (abs zero)
           zero
           (req_abs_compat
              (req_minus
                 (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                 (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s'))))
              zero
              (req_minus_self_zero
                 (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                 (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))
                 (req_evicted_boltzmann_steady_exact s)))
           abs_zero).
Qed.

(* ---- 件 11：le 形态并列（母件 L274；req 接口 le_id_l 字段直引） ---- *)
Corollary req_eviction_steady_deviation_le_zero :
  forall s : S,
    le (abs (req_minus
                (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))))
       zero.
Proof.
  intro s.
  exact (le_id_l
           (abs (req_minus
                   (sumf (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sumf (fun s' => evicted_transition s s')))))
           zero zero
           (req_eviction_steady_deviation_zero s)
           (le_refl zero)).
Qed.

(* ---- 件 12：增量逐点式（母件 L290；req 差异真证：req_minus_self_zero +
   批 2 reqd_minus_zero_r（冻结扣除件的消费位）） ---- *)
Lemma req_partition_increment_pointwise :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    req (req_minus (if kd2 s then boltzmann_factor s else zero)
                   (if kd1 s then boltzmann_factor s else zero))
        (if kd2 s then (if kd1 s then zero else boltzmann_factor s) else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | H1]; destruct (kd2 s) as [H2 | H2].
  - (* kd1 s ∧ kd2 s：f − f == 0 *)
    exact (req_minus_self_zero (boltzmann_factor s) (boltzmann_factor s)
                               (req_refl (boltzmann_factor s))).
  - (* kd1 s ∧ ¬kd2 s：与 Hsub 矛盾 *)
    exact (match H2 (Hsub s H1) with end).
  - (* ¬kd1 s ∧ kd2 s：f − 0 == f（批 2 reqd_minus_zero_r 消费位） *)
    exact (reqd_minus_zero_r (boltzmann_factor s)).
  - (* ¬kd1 s ∧ ¬kd2 s：0 − 0 == 0 *)
    exact (req_minus_self_zero zero zero (req_refl zero)).
Qed.

(* ---- 件 13：保留集扩张的精确增量恒等式（母件 L313；req 差异真证：
   sum_over_S_minus 换批 2 reqd_sum_minus（显式假设位逐位对位），再
   req sum_ext 重排逐点收口） ---- *)
Theorem req_eviction_partition_increment :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    req (req_minus (evicted_partition_of k2 kd2) (evicted_partition_of k1 kd1))
        (sumf (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s)
                            else zero)).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of.
  apply (req_trans
           (req_minus (sumf (fun s => if kd2 s then boltzmann_factor s else zero))
                      (sumf (fun s => if kd1 s then boltzmann_factor s else zero)))
           (sumf (fun s => req_minus (if kd2 s then boltzmann_factor s else zero)
                                     (if kd1 s then boltzmann_factor s else zero)))
           (sumf (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s)
                                 else zero))).
  - exact (req_sym
             (sumf (fun s => req_minus (if kd2 s then boltzmann_factor s else zero)
                                       (if kd1 s then boltzmann_factor s else zero)))
             (req_minus (sumf (fun s => if kd2 s then boltzmann_factor s else zero))
                        (sumf (fun s => if kd1 s then boltzmann_factor s else zero)))
             (reqd_sum_minus S sumf sum_ext sum_add sum_linear
                (fun s => if kd2 s then boltzmann_factor s else zero)
                (fun s => if kd1 s then boltzmann_factor s else zero))).
  - apply sum_ext.
    intro s.
    exact (req_partition_increment_pointwise k1 k2 Hsub kd1 kd2 s).
Qed.

(* ---- 件 14：全配分差恒等式（母件 L336；req 差异真证同件 13 工艺） ---- *)
Corollary req_eviction_partition_le_full_exact :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    req (req_minus Z_thermo (evicted_partition_of k kd))
        (sumf (fun s => if kd s then zero else boltzmann_factor s)).
Proof.
  intros k kd.
  unfold Z_thermo, evicted_partition_of.
  apply (req_trans
           (req_minus (sumf boltzmann_factor)
                      (sumf (fun s => if kd s then boltzmann_factor s else zero)))
           (sumf (fun s => req_minus (boltzmann_factor s)
                                     (if kd s then boltzmann_factor s else zero)))
           (sumf (fun s => if kd s then zero else boltzmann_factor s))).
  - exact (req_sym
             (sumf (fun s => req_minus (boltzmann_factor s)
                                       (if kd s then boltzmann_factor s else zero)))
             (req_minus (sumf boltzmann_factor)
                        (sumf (fun s => if kd s then boltzmann_factor s else zero)))
             (reqd_sum_minus S sumf sum_ext sum_add sum_linear
                boltzmann_factor
                (fun s => if kd s then boltzmann_factor s else zero))).
  - apply sum_ext.
    intro s.
    destruct (kd s) as [Hk | Hk].
    + (* kd s：f − f == 0 *)
      exact (req_minus_self_zero (boltzmann_factor s) (boltzmann_factor s)
                                 (req_refl (boltzmann_factor s))).
    + (* ¬kd s：f − 0 == f（批 2 reqd_minus_zero_r 消费位） *)
      exact (reqd_minus_zero_r (boltzmann_factor s)).
Qed.

End EvictIdReq.

(* ---- 提取探针（G3 关卡对象；Obj.magic 计数验后即删） ----
From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "b4b_evictid_g3.ml" req_evicted_db_products
  req_eviction_db_breaking_zero req_evicted_boltzmann_steady_exact
  req_evicted_boltzmann_steady_full_keep req_eviction_steady_deviation_zero
  req_eviction_partition_increment req_eviction_partition_le_full_exact.
*)
