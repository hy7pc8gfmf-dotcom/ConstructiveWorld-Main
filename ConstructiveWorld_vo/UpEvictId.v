(* ========================================================================= *)
(* UpEvictId.v — §6 KV 逐出恒等式批（王中王 A1/B3 + A6/B1，2026-09-07）      *)
(*                                                                           *)
(* 本文件以与根 AttentionGibbsBridge 区段同款 Section（变量名/前提形态      *)
(* 逐行对齐）重建逐出世界，交付四组恒等式升级：                              *)
(*                                                                           *)
(* 件 1a  eviction_db_breaking_zero        ：破缺恒为零（拆冗余假设         *)
(*         fluctuation_dissipation_bound 的核心件——本文件全程不使用该      *)
(*         假设；所需前提仅为 Section 自带 detailed_balance）。              *)
(* 件 1b  evicted_boltzmann_steady_exact   ：截断核稳态方程精确成立          *)
(*         （保留因子形态 = 扫描报告 A1 草案逐字）；并列交付全保留特例      *)
(*         evicted_boltzmann_steady_full_keep（右端裸 ev_b(s) 形态，核行    *)
(*         归一化 Σ ev_t(s,·) == 1 在全保留时成立并吸收）。                  *)
(* 件 1c  eviction_steady_deviation_zero   ：定理 6.1 偏差恒为零（Id 形态   *)
(*         + le 形态并列），供论文"定理 6.1 右端恒为零"直接引用。           *)
(* 件 2   eviction_partition_increment     ：保留集扩张的精确增量恒等式     *)
(*         （L29485 单调 ≤ 的等式升级）；并列交付全配分差恒等式             *)
(*         eviction_partition_le_full_exact（L29526 的等式升级）。           *)
(*                                                                           *)
(* 分界注记（对照根 Real-KV 区）：本件零破缺严格依赖 detailed_balance      *)
(* 前提；对称核世界（无 detailed_balance）破缺非零，两层不可互相无条件化。  *)
(* 纯构造性：Set 层语句、Type 版 Or/Not/Id/le/lt，零经典逻辑。              *)
(* ========================================================================= *)

Require Import CW_ConstructiveWorld_219.

Section UpEvictId.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.
Let inv_pos := @inv_pos RI.
Let exp_neg := @exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

(* ---- 与根 AttentionGibbsBridge 同款世界（变量名/前提形态对齐） ---- *)

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.

Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition Z_thermo : R := sum_over_S boltzmann_factor.

Variable Z_thermo_pos : lt zero Z_thermo.

Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Variable transition : S -> S -> R.
Variable transition_nonneg : forall s s', le zero (transition s s').
Variable transition_normalization :
  forall s, Id (sum_over_S (fun s' => transition s s')) one.

Variable detailed_balance :
  forall s s',
    Id (mult (boltzmann_dist_attn s) (transition s s'))
       (mult (boltzmann_dist_attn s') (transition s' s)).

Variable keep : S -> Set.
Variable keep_dec : forall s, Or (keep s) (Not (keep s)).

Definition evicted_transition (s s' : S) : R :=
  if keep_dec s then
    if keep_dec s' then transition s s' else zero
  else zero.

Definition evicted_partition : R :=
  sum_over_S (fun s => if keep_dec s then boltzmann_factor s else zero).

Variable evicted_partition_pos : lt zero evicted_partition.

Definition evicted_boltzmann (s : S) : R :=
  if keep_dec s then
    mult (inv_pos evicted_partition evicted_partition_pos) (boltzmann_factor s)
  else zero.

Definition db_breaking (s s' : S) : R :=
  abs (minus (mult (evicted_boltzmann s) (evicted_transition s s'))
             (mult (evicted_boltzmann s') (evicted_transition s' s))).

(* 保留集参数化的条件配分函数（单调性/增量比较所需，同根 L29446） *)
Definition evicted_partition_of (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))) : R :=
  sum_over_S (fun s => if kd s then boltzmann_factor s else zero).

(* ---- 局部代数辅助（根内无现成 Set 层 minus_zero_r / opp_zero） ---- *)

Lemma opp_zero_u : Id (opp zero) zero.
Proof.
  apply (plus_inv_unique zero (opp zero) zero (plus_opp zero)).
  exact (plus_zero zero).
Qed.

Lemma minus_zero_r_u : forall a : R, Id (minus a zero) a.
Proof.
  intro a.
  unfold minus.
  apply (id_trans (id_cong (fun x => plus a x) opp_zero_u) (plus_zero a)).
Qed.

(* ---- 因子层详细平衡：detailed_balance 消去 Z_thermo 逆元 ----
   （件 1a 的代数核心：bd(s)·t(s,s') == bd(s')·t(s',s) 两侧乘 Z_thermo
     后由 inv_pos_correct + mult_one 吸收逆元。） *)
Lemma boltzmann_factor_detailed_balance :
  forall s s' : S,
    Id (mult (boltzmann_factor s) (transition s s'))
       (mult (boltzmann_factor s') (transition s' s)).
Proof.
  intros s s'.
  pose proof (detailed_balance s s') as Hdb.
  unfold boltzmann_dist_attn in Hdb.
  pose proof (inv_pos_correct Z_thermo Z_thermo_pos) as HZinv.
  pose proof
    (id_trans
       (mult_assoc Z_thermo
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s))
                   (transition s s'))
       (id_cong (fun x => mult x (transition s s'))
                (id_trans (mult_assoc Z_thermo (inv_pos Z_thermo Z_thermo_pos)
                                        (boltzmann_factor s))
                          (id_trans (id_cong (fun x => mult x (boltzmann_factor s)) HZinv)
                                    (id_trans (mult_comm one (boltzmann_factor s))
                                              (mult_one (boltzmann_factor s))))))) as HZl.
  pose proof
    (id_trans
       (mult_assoc Z_thermo
                   (mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s'))
                   (transition s' s))
       (id_cong (fun x => mult x (transition s' s))
                (id_trans (mult_assoc Z_thermo (inv_pos Z_thermo Z_thermo_pos)
                                        (boltzmann_factor s'))
                          (id_trans (id_cong (fun x => mult x (boltzmann_factor s')) HZinv)
                                    (id_trans (mult_comm one (boltzmann_factor s'))
                                              (mult_one (boltzmann_factor s'))))))) as HZr.
  exact (id_trans (id_sym HZl) (id_trans (id_cong (fun x => mult Z_thermo x) Hdb) HZr)).
Qed.

(* ---- 掩码核逐点详细平衡（件 1a/1b 共用核心）：任一端逐出则两积同为
   零；双保留时由因子层详细平衡 + evicted_partition 逆元缩放。4 分支全
   构造性（对照根 L29573 全保留特例的同款分支工艺）。 *)
Lemma evicted_db_products :
  forall s s' : S,
    Id (mult (evicted_boltzmann s') (evicted_transition s' s))
       (mult (evicted_boltzmann s) (evicted_transition s s')).
Proof.
  intros s s'.
  unfold evicted_boltzmann, evicted_transition.
  destruct (keep_dec s) as [Hs | Hs]; destruct (keep_dec s') as [Hs' | Hs'].
  - (* 双保留：inv_ev·f(s')·t(s',s) == inv_ev·f(s)·t(s,s') *)
    pose proof (id_sym (boltzmann_factor_detailed_balance s s')) as Hf.
    apply (id_trans (id_sym (mult_assoc
                               (inv_pos evicted_partition evicted_partition_pos)
                               (boltzmann_factor s') (transition s' s)))).
    apply (id_trans (id_cong (fun x => mult (inv_pos evicted_partition evicted_partition_pos) x)
                             Hf)).
    apply (mult_assoc (inv_pos evicted_partition evicted_partition_pos)
                      (boltzmann_factor s) (transition s s')).
  - (* s 保留、s' 逐出：两积同为零 *)
    exact (id_trans (mult_zero zero)
                    (id_sym (mult_zero (mult (inv_pos evicted_partition evicted_partition_pos)
                                             (boltzmann_factor s))))).
  - (* s 逐出、s' 保留：两积同为零 *)
    exact (id_trans (mult_zero (mult (inv_pos evicted_partition evicted_partition_pos)
                                     (boltzmann_factor s')))
                    (id_sym (mult_zero zero))).
  - (* 双逐出 *)
    reflexivity.
Qed.

(* ================= 件 1a：破缺恒为零（涨落-耗散假设整体多余） ============ *)

Theorem eviction_db_breaking_zero :
  forall s s' : S, Id (db_breaking s s') zero.
Proof.
  intros s s'.
  unfold db_breaking.
  apply (id_trans (id_cong abs
    (minus_self_zero (mult (evicted_boltzmann s) (evicted_transition s s'))
                     (mult (evicted_boltzmann s') (evicted_transition s' s))
                     (id_sym (evicted_db_products s s'))))).
  exact abs_zero.
Qed.

(* ================= 件 1b：截断核稳态方程（精确恒等式） ====================
   形态 = 扫描报告 A1 草案逐字：Σ_{s'} ev_b(s')·ev_t(s',s)
   == ev_b(s)·Σ_{s'} ev_t(s,s')（保留因子显式出现在右端——掩码核行和
   Σ ev_t(s,·) 一般 < 1，等于 1 仅在全保留时成立，见下方特例）。 *)

Theorem evicted_boltzmann_steady_exact :
  forall s : S,
    Id (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
       (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s'))).
Proof.
  intro s.
  apply (id_trans (sum_over_S_ext
                    (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s))
                    (fun s' => mult (evicted_boltzmann s) (evicted_transition s s'))
                    (fun s' => id_sym (evicted_db_products s' s)))).
  apply (sum_over_S_linear (evicted_boltzmann s) (fun s' => evicted_transition s s')).
Qed.

(* 全保留桥：ev_t 逐点回到 t（对照根 L29506 eviction_transition_full） *)
Lemma eviction_transition_pointwise_full :
  (forall s, keep s) ->
  forall s s' : S, Id (evicted_transition s s') (transition s s').
Proof.
  intros Hkall s s'.
  unfold evicted_transition.
  destruct (keep_dec s) as [Hks | Hnks].
  - destruct (keep_dec s') as [Hks' | Hnks'].
    + reflexivity.
    + exact (match Hnks' (Hkall s') with end).
  - exact (match Hnks (Hkall s) with end).
Qed.

(* 全保留时掩码核行归一化：Σ ev_t(s,·) == 1（transition_normalization 吸收） *)
Lemma evicted_transition_row_sum_one :
  (forall s, keep s) ->
  forall s : S, Id (sum_over_S (fun s' => evicted_transition s s')) one.
Proof.
  intros Hkall s.
  apply (id_trans (sum_over_S_ext (fun s' => evicted_transition s s')
                                  (fun s' => transition s s')
                                  (fun s' => eviction_transition_pointwise_full Hkall s s'))).
  apply (transition_normalization s).
Qed.

(* 特例（右端裸 ev_b(s) 形态）：全保留时截断核稳态方程即完整稳态方程 *)
Corollary evicted_boltzmann_steady_full_keep :
  (forall s, keep s) ->
  forall s : S,
    Id (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
       (evicted_boltzmann s).
Proof.
  intros Hkall s.
  apply (id_trans (evicted_boltzmann_steady_exact s)).
  apply (id_trans (id_cong (fun x => mult (evicted_boltzmann s) x)
                           (evicted_transition_row_sum_one Hkall s))).
  apply (mult_one (evicted_boltzmann s)).
Qed.

(* ================= 件 1c：定理 6.1 偏差恒为零（1b 一步推论） =============
   根 L29626 的界 |稳态差| ≤ Σ db_breaking 之右端逐项为零，故稳态差
   恒为零——"逐出代价在支撑收缩而非平稳性破坏"的精确形态。 *)

Theorem eviction_steady_deviation_zero :
  forall s : S,
    Id (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
       zero.
Proof.
  intro s.
  apply (id_trans (id_cong abs
    (minus_self_zero
       (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
       (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))
       (evicted_boltzmann_steady_exact s)))).
  exact abs_zero.
Qed.

Corollary eviction_steady_deviation_le_zero :
  forall s : S,
    le (abs (minus (sum_over_S (fun s' => mult (evicted_boltzmann s') (evicted_transition s' s)))
                   (mult (evicted_boltzmann s) (sum_over_S (fun s' => evicted_transition s s')))))
       zero.
Proof.
  intro s.
  apply (le_id_l _ zero zero).
  - apply (eviction_steady_deviation_zero s).
  - apply le_refl.
Qed.

(* ================= 件 2：保留集扩张的精确增量恒等式 ======================
   L29485 单调 ≤ 的等式升级：k1 ⊆ k2 时新增保留质量的精确值 =
   "新入选状态（kd2 真、kd1 假）的 Boltzmann 质量之和"。 *)

Lemma partition_increment_pointwise :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
  forall s : S,
    Id (minus (if kd2 s then boltzmann_factor s else zero)
              (if kd1 s then boltzmann_factor s else zero))
       (if kd2 s then (if kd1 s then zero else boltzmann_factor s) else zero).
Proof.
  intros k1 k2 Hsub kd1 kd2 s.
  destruct (kd1 s) as [H1 | H1]; destruct (kd2 s) as [H2 | H2].
  - (* kd1 s ∧ kd2 s：f − f = 0 *)
    apply (minus_self_zero (boltzmann_factor s) (boltzmann_factor s)).
    apply id_refl.
  - (* kd1 s ∧ ¬kd2 s：与 Hsub 矛盾 *)
    exact (match H2 (Hsub s H1) with end).
  - (* ¬kd1 s ∧ kd2 s：f − 0 = f（新入选态贡献全额质量） *)
    apply (minus_zero_r_u (boltzmann_factor s)).
  - (* ¬kd1 s ∧ ¬kd2 s：0 − 0 = 0 *)
    apply (minus_self_zero zero zero).
    apply id_refl.
Qed.

Theorem eviction_partition_increment :
  forall (k1 k2 : S -> Set) (Hsub : forall s, k1 s -> k2 s)
    (kd1 : forall s, Or (k1 s) (Not (k1 s)))
    (kd2 : forall s, Or (k2 s) (Not (k2 s))),
    Id (minus (evicted_partition_of k2 kd2) (evicted_partition_of k1 kd1))
       (sum_over_S (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s)
                            else zero)).
Proof.
  intros k1 k2 Hsub kd1 kd2.
  unfold evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus
                            (fun s => if kd2 s then boltzmann_factor s else zero)
                            (fun s => if kd1 s then boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (if kd2 s then boltzmann_factor s else zero)
                           (if kd1 s then boltzmann_factor s else zero))
           (fun s => if kd2 s then (if kd1 s then zero else boltzmann_factor s) else zero)).
  intro s.
  apply (partition_increment_pointwise k1 k2 Hsub kd1 kd2 s).
Qed.

(* 并列：全配分差恒等式（L29526 ≤ 的等式升级）——
   逐出质量损失 Z_thermo − evicted_partition(k) = 被逐出态质量之和。 *)
Corollary eviction_partition_le_full_exact :
  forall (k : S -> Set) (kd : forall s, Or (k s) (Not (k s))),
    Id (minus Z_thermo (evicted_partition_of k kd))
       (sum_over_S (fun s => if kd s then zero else boltzmann_factor s)).
Proof.
  intros k kd.
  unfold Z_thermo, evicted_partition_of.
  apply (id_trans (id_sym (sum_over_S_minus boltzmann_factor
                            (fun s => if kd s then boltzmann_factor s else zero)))).
  apply (sum_over_S_ext
           (fun s => minus (boltzmann_factor s) (if kd s then boltzmann_factor s else zero))
           (fun s => if kd s then zero else boltzmann_factor s)).
  intro s.
  destruct (kd s) as [Hk | Hk].
  - apply (minus_self_zero (boltzmann_factor s) (boltzmann_factor s)).
    apply id_refl.
  - apply (minus_zero_r_u (boltzmann_factor s)).
Qed.

End UpEvictId.

(* ---- 提取探针（可提取性验证；G3 关卡对象） ---- *)
