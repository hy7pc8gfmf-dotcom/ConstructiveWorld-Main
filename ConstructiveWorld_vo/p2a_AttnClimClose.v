(* ============================================================ *)
(* ToyR 玩具证替换件 —— T269 台账席 战役包AD（tier2 末批二）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   p2a_attn_tv_seq_clim_zero（原 L112，2 句玩具证）                     *)
(* ============================================================ *)

(* ============================================================ *)
(* p2a_AttnClimClose.v —— 席 CZC10（E-STAGING-CZC10）              *)
(*   论文2《自由能原理与注意力Gibbs桥》假设消融施工：T56 普查档条 2-8   *)
(*   （B 可消融，坐标 L978；§9.4 开放项 5 的 clim 半边）。            *)
(*                                                                *)
(*   槽语句：注意力核迭代收敛已有 attention_tv_iter_contraction        *)
(*   （S06_DiffSamplingGibbs.v:4544，几何率 (1−δ)ⁿ）与 sigT 预算形     *)
(*   attention_iterate_converges（根文件）+ UpArchAttn.attention_       *)
(*   iterate_converges_real，但【序列 clim 收敛面】开放——TV 序列        *)
(*   n ↦ TV(iterate attention_step n μ₀, p_b) 对极限零点的 real_lim     *)
(*   收敛无库内定理。                                                  *)
(*                                                                *)
(*   施工：clim 收敛引擎——消费基座件四绿：                             *)
(*     ① real_lim + real_const（S02_CauchyComplete.v:883/860，          *)
(*        "∀eps>0 ∃N ∀n≥N 双向夹逼"的构造性 clim 谓词）；              *)
(*     ② r_arch_pow_real（UpBudgetReal.v:310，几何击穿显式 N 预算）；   *)
(*     ③ real_pow_anti_mono（UpBudgetReal.v:655，幂反单调）；           *)
(*     ④ one_minus_delta_pos_real / one_minus_delta_lt_one_real         *)
(*        （UpArchAttn.v，δ↦κ:=1−δ 良定桥）。                          *)
(*   交付面：                                                          *)
(*   引擎 p2a_attn_clim_zero：逐步几何收缩 + 非负 + 初值正 ⟹ real_lim   *)
(*        u real_zero（收敛到零点的 clim 全谓词，双向夹逼）；            *)
(*   注意力镜面 p2a_attn_tv_seq_clim_zero：κ := 1−δ 特化形，             *)
(*        单步收缩前提对位 attention_tv_contraction 的 Real 镜像口        *)
(*        （UpArchAttn 件2 同款 Hstep 显式前提纪律）；                   *)
(*   预算伴件 p2a_attn_clim_budget：clim 的单向 Q-eps 预算形。           *)
(*                                                                *)
(*   纪律：纯构造性；Set 层语句（real_lim 值居 Set、sigT 见证）；        *)
(*   全部 Qed 闭合；只消费库内已证机器；G1-G4 四关候跑。                 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
Require Import CW_ConstructiveWorld_219.
Require Import UpBudgetReal.
Require Import UpArchAttn.

(* ============ 几何迭代上界：u n ≤ κ^n·u 0 ============ *)

Theorem p2a_geo_iter_le : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  forall n : nat, real_le (u n) (real_mult (real_pow kappa n) (u 0%nat)).
Proof.
  intros u kappa Hk1 Hstep n.
  induction n as [| n IH].
  - apply real_eq_le_bridge. apply real_eq_sym. apply real_mult_one_l.
  - apply (real_le_trans _ (real_mult kappa (u n))).
    + apply Hstep.
    + apply (real_le_trans _
               (real_mult kappa (real_mult (real_pow kappa n) (u 0%nat)))).
      * apply real_le_mult_compat_r.
        -- exact (real_lt_le_bridge real_zero kappa Hk1).
        -- exact IH.
      * apply real_eq_le_bridge. apply real_mult_assoc.
Qed.

(* ============ 引擎：几何收缩序列的 clim 收敛（收敛到零点） ============ *)

Theorem p2a_attn_clim_zero : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  real_lim u real_zero.
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 (u 0%nat) Hu0 (real_const eps)
              (real_const_pos eps Heps)) as [N HN].
  exists N. intros n Hn.
  split.
  - (* 上侧：u n ≤ κ^n·u0 ≤ κ^N·u0 < eps；再换装 0+eps 形 *)
    apply (real_lt_eq_lt (u n) (real_const eps)
             (real_plus real_zero (real_const eps))).
    + apply (real_le_lt_trans (u n)
               (real_mult (real_pow kappa N) (u 0%nat))).
      * apply (real_le_trans _
                 (real_mult (real_pow kappa n) (u 0%nat))).
        -- exact (p2a_geo_iter_le u kappa Hk1 Hstep n).
        -- apply real_le_mult_compat.
           ++ exact Hu0.
           ++ exact (real_pow_anti_mono kappa Hk1
                       (real_lt_le_bridge kappa real_one Hk2) N n Hn).
      * apply (real_eq_lt_lt
                 (real_mult (real_pow kappa N) (u 0%nat))
                 (real_mult (u 0%nat) (real_pow kappa N))).
        -- apply real_mult_comm.
        -- exact HN.
    + apply real_eq_sym.
      apply (real_eq_trans (real_plus real_zero (real_const eps))
                           (real_plus (real_const eps) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
  - (* 下侧：0 − eps < u n（非负性单边供给） *)
    apply (real_lt_le_trans (real_plus real_zero (real_opp (real_const eps))) real_zero).
    + apply (real_eq_lt_lt
               (real_plus real_zero (real_opp (real_const eps)))
               (real_opp (real_const eps)) real_zero).
      * apply (real_eq_trans
                 (real_plus real_zero (real_opp (real_const eps)))
                 (real_plus (real_opp (real_const eps)) real_zero)).
        -- apply real_plus_comm.
        -- apply real_plus_zero.
      * exact (real_lt_zero_opp (real_const eps) (real_const_pos eps Heps)).
    + exact (Hnonneg n).
Qed.

(* ============ 注意力镜面：κ := 1−δ 特化形（论文2 §5.5/§9.4 口） ============ *)
(*   单步收缩前提 Hstep 对位 attention_tv_contraction 的 Real 镜像口         *)
(*   （S06 几何率 (1−δ) 的实例面；UpArchAttn 件2 同款显式前提纪律——          *)
(*   抽象 Section 世界的 TV/iterate 对象整体实例化属天级工程，不属本件）。     *)

Theorem p2a_attn_tv_seq_clim_zero :
  forall (tv_seq : nat -> Real) (delta : Real),
  real_lt real_zero delta -> real_lt delta real_one ->
  (forall n : nat,
     real_le (tv_seq (Datatypes.S n))
             (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  (forall n : nat, real_le real_zero (tv_seq n)) ->
  real_lt real_zero (tv_seq 0%nat) ->
  real_lim tv_seq real_zero.
Proof.
  intros tv_seq delta Hd0 Hd1 Hstep Hnonneg Hu0.
  exact (p2a_attn_clim_zero tv_seq (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd1)           (one_minus_delta_lt_one_real delta Hd0)           Hstep Hnonneg Hu0).
Qed.

(* ============ 预算伴件：clim 的单向 Q-eps 预算形 ============ *)

Theorem p2a_attn_clim_budget : forall (u : nat -> Real) (kappa : Real),
  real_lt real_zero kappa -> real_lt kappa real_one ->
  (forall n : nat, real_le (u (Datatypes.S n)) (real_mult kappa (u n))) ->
  (forall n : nat, real_le real_zero (u n)) ->
  real_lt real_zero (u 0%nat) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (u n) (real_plus real_zero (real_const eps))).
Proof.
  intros u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps.
  destruct (p2a_attn_clim_zero u kappa Hk1 Hk2 Hstep Hnonneg Hu0 eps Heps)
    as [N HN].
  exists N. intros n Hn.
  destruct (HN n Hn) as [Hup _].
  exact Hup.
Qed.

(* ---- 四关备件：PA 口径 + G3 提取探针 ---- *)

Print Assumptions p2a_geo_iter_le.
Print Assumptions p2a_attn_clim_zero.
Print Assumptions p2a_attn_tv_seq_clim_zero.
Print Assumptions p2a_attn_clim_budget.

From Stdlib Require Import Extraction.
Set Extraction Output Directory ".".
Extraction "p2a_attnclimclose.ml" p2a_geo_iter_le p2a_attn_clim_budget.
