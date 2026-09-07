(* ============================================================ *)
(* UpProjBPC.v — BPC：KL 区间乘法复合链（席 6 杂交增量）           *)
(*                                                              *)
(* 上游：UpProj.v（抽象投影核母定理，807 行 32 引理，四关全绿）。   *)
(* 本文件在母定理件 1/4 直推半径内，给出封口链经复合掩码的          *)
(* 代价区间端点精确乘法复合：                                     *)
(*   Z_{P1∩P2} == Z1·(Z2|kept1)，其中 Z2|kept1 为 P1 保留集内     *)
(*   二级掩码的条件保留质量（构造性比值形态 Z12·inv Z1）。          *)
(*   代价侧：−log Z12 == (−log Z1) + (−log Zc) 精确分裂，          *)
(*   KL 代价沿封口链可加：KL_{P1}(q) == KL_{P12}(q) + (−log Zc)。  *)
(*                                                              *)
(* 件 4（对照注记，注释级）——四近邻均无 KL 区间乘法链语义：        *)
(*   · PCD 并集界：并集质量重算只给界，无乘法分解恒等式；           *)
(*   · PKI notAfter：时点有效性陈述，无 KL 记账；                  *)
(*   · 级数余项：|S−S_t| ≤ B 型余项界，非端点级精确分裂；           *)
(*   · Doob 塔性质：L2 收敛定理，无可计算证书与代价记账。           *)
(*   本件新度 = 封口点的代数：复合掩码上端点恒等式 + 链式可加。     *)
(*                                                              *)
(* 世界：Real 层 list 世界（UpProj 同款，CW219 根）。              *)
(* 全部 Set 层（Id/And/Or/sigT）；语句零 Prop 泄露；              *)
(* 纯构造性：仅依赖 CW_ConstructiveWorld_219 与 UpProj，           *)
(* 零外部假设；log 正性证书随身（透明 Definition 纪律）。          *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpProj.
Require Import UpProj.

(* ============================================================ *)
(* 顶层助推（Set 层 real_eq 代数小工具，命名前缀 bpc_ 独占）       *)
(* ============================================================ *)

(* −0 == 0（有符号零桥；区间端点 0 形态归零用） *)
Lemma bpc_opp_zero : real_eq (real_opp real_zero) real_zero.
Proof.
  apply (real_eq_trans _ (real_plus (real_opp real_zero) real_zero) _).
  - apply real_eq_sym. apply real_plus_zero.
  - apply (real_eq_trans _ (real_plus real_zero (real_opp real_zero)) _).
    + apply real_plus_comm.
    + apply real_plus_opp.
Qed.

(* 1·x == x（右单位桥；real_mult_one 是 x·1 形态的镜像） *)
Lemma bpc_one_mult : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one) _).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* (−t)+t == 0（反序消去零；plus_opp 是 t+(−t) 形态的镜像） *)
Lemma bpc_opp_plus_zero : forall t : Real, real_eq (real_plus (real_opp t) t) real_zero.
Proof.
  intro t.
  apply (real_eq_trans _ (real_plus t (real_opp t)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* 消去律：(a+(−t))+t == a（链式 KL 恒等式的两侧搬移臂） *)
Lemma bpc_cancel_add_opp : forall a t : Real,
  real_eq (real_plus (real_plus a (real_opp t)) t) a.
Proof.
  intros a t.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp t) t)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a real_zero) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus (real_opp t) t)
               a real_zero).
      * apply real_eq_refl.
      * apply bpc_opp_plus_zero.
    + apply real_plus_zero.
Qed.

(* 加法交换重排：(a+b)+c == (a+c)+b（链式恒等式的中项换位臂） *)
Lemma bpc_assoc_swap : forall a b c : Real,
  real_eq (real_plus (real_plus a b) c) (real_plus (real_plus a c) b).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus b c)) _).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans _ (real_plus a (real_plus c b)) _).
    + apply (RealSetoid.real_eq_plus_compat a (real_plus b c)
               a (real_plus c b)).
      * apply real_eq_refl.
      * apply real_plus_comm.
    + apply real_plus_assoc.
Qed.

(* 乘法换位：x·(y·z) == y·(x·z)（吸收链的中项重排臂） *)
Lemma bpc_mult_swap : forall x y z : Real,
  real_eq (real_mult x (real_mult y z)) (real_mult y (real_mult x z)).
Proof.
  intros x y z.
  apply (real_eq_trans _ (real_mult (real_mult x y) z) _).
  - apply real_mult_assoc.
  - apply (real_eq_trans _ (real_mult (real_mult y x) z) _).
    + apply (RealSetoid.real_eq_mult_compat (real_mult x y) z
               (real_mult y x) z).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply real_eq_sym. apply real_mult_assoc.
Qed.

(* ============================================================ *)
(* 母 Section：两级掩码复合（与 UpProj 母 Section 同形扩展）        *)
(*   I/f/idx/f_norm/f_pos 与 UpProj 逐参对齐；P1 P2 两级掩码，     *)
(*   各带非空见证（P1_witness 复用母件 0，P12_witness 复合级）。    *)
(* ============================================================ *)
Section BPChain.

Variable I : Set.                          (* 索引类型（同母） *)
Variable f : I -> Real.                    (* 被投影权重（同母） *)
Variable P1 : I -> bool.                   (* 一级保留谓词 *)
Variable P2 : I -> bool.                   (* 二级保留谓词 *)
Variable idx : list I.                     (* 枚举（同母） *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P1_witness : sigT (fun i : I => And (Id (P1 i) true) (InT i idx)).

(* 复合掩码：P1∩P2（bool 合取） *)
Definition P12 (i : I) : bool := andb (P1 i) (P2 i).

Variable P12_witness : sigT (fun i : I => And (Id (P12 i) true) (InT i idx)).

(* ---------- 质量与证书（透明 Definition：log 证书随身纪律） ------ *)
(* Z1 = 一级保留质量；Z12 = 复合保留质量（即 Z_{P1∩P2}） *)
Definition Z1 : Real := Z_P I f P1 idx.
Definition Z12 : Real := Z_P I f P12 idx.

Definition p1 : real_lt real_zero Z1 := ZP_pos I f P1 idx f_pos P1_witness.
Definition p12 : real_lt real_zero Z12 := ZP_pos I f P12 idx f_pos P12_witness.

(* 条件保留质量 Zc := Z12·inv Z1（= Σ_{P1∧P2} f / Z1，即 Z2|kept1） *)
Definition Zc : Real := real_mult Z12 (real_inv_pos Z1 p1).
(* 正性证书随身（透明，非 Qed 封死） *)
Definition Zc_pos : real_lt real_zero Zc :=
  real_mult_positive Z12 (real_inv_pos Z1 p1) p12 (real_inv_pos_pos Z1 p1).

(* 一级投影核（母形态实例化）与条件质量和的核上形态 *)
Definition Proj1 (i : I) : Real := Proj I f P1 idx f_pos P1_witness i.
Definition Zc_proj1 : Real :=
  real_list_sum I (fun i : I => if P12 i then Proj1 i else real_zero) idx.

(* ---------- 件 1 核 A：点级四支掩码桥 -------------------------- *)
(* P12 支的 Proj1 == P12 支的 f·inv Z1（P1∧P2 保留 ⟹ 一级保留支）； *)
(* P12 逐出支两侧归零。destruct 逐支独立放电，无空 match。          *)
Lemma bpc_pt_bridge : forall y : I,
  real_eq (if P12 y then Proj1 y else real_zero)
          (real_mult (if P12 y then f y else real_zero)
                     (real_inv_pos Z1 p1)).
Proof.
  intro y. unfold P12, Proj1, Proj.
  destruct (P1 y) eqn:H1y; destruct (P2 y) eqn:H2y; cbn [andb].
  - (* true,true：双侧 f·inv Z1，conversion 相等 *)
    apply real_eq_refl.
  - (* true,false：0·inv == 0（sym 转 mult 头，comm + mult_zero） *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,true：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
  - (* false,false：0·inv == 0 *)
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) real_zero) _).
    + apply real_mult_comm.
    + apply real_mult_zero.
Qed.

(* ---------- 件 1 核 B：两级掩码和的分解（线性提取） ------------- *)
(* Σ_{P12} Proj1 == inv Z1 · Z12：条件质量和（二级掩码在一级投影核  *)
(* 上的和）经逐点桥 + real_list_sum_linear_r 提取线性因子。         *)
Lemma bpc_Zc_proj1_sum : real_eq Zc_proj1
  (real_mult (real_inv_pos Z1 p1) Z12).
Proof.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P12 i then f i else real_zero)
                           (real_inv_pos Z1 p1))
              idx) _).
  - apply (real_list_sum_ext I
             (fun i : I => if P12 i then Proj1 i else real_zero)
             (fun i : I =>
                real_mult (if P12 i then f i else real_zero)
                          (real_inv_pos Z1 p1))
             idx).
    intro y. apply bpc_pt_bridge.
  - apply (real_list_sum_linear_r I (real_inv_pos Z1 p1)
             (fun i : I => if P12 i then f i else real_zero) idx).
Qed.

(* ---------- 复合支配：Z12 ≤ Z1（两级掩码和 ≤ 一级掩码和） ------- *)
Lemma bpc_Z12_le_Z1 : real_le Z12 Z1.
Proof.
  apply (real_list_sum_le I
           (fun i : I => if P12 i then f i else real_zero)
           (fun i : I => if P1 i then f i else real_zero) idx).
  intro y. unfold P12. destruct (P1 y); destruct (P2 y).
  - apply real_le_refl.
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
  - apply real_le_refl.
Qed.

(* ---------- 件 1（主件·乘法分解）：Z12 == Z1·Zc ----------------- *)
(* 纸笔推导：Z1·Zc == Z1·(Z12·inv Z1) == Z12·(Z1·inv Z1)（换位）    *)
(*   == Z12·1 == Z12。核心 = inv 的分配吸收（换位 + inv_correct     *)
(*   + mult_one）；条件占比形态的循环由「Zc 由 Z12/Z1/见证构造、    *)
(*   分解核独立（核 A/B）」排除。                                   *)
Theorem Z_compound_mul : real_eq Z12 (real_mult Z1 Zc).
Proof.
  apply real_eq_sym.
  apply (real_eq_trans _ (real_mult Z1 (real_mult Z12 (real_inv_pos Z1 p1))) _).
  - apply (RealSetoid.real_eq_mult_compat Z1 Zc Z1
             (real_mult Z12 (real_inv_pos Z1 p1))).
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult Z12 (real_mult Z1 (real_inv_pos Z1 p1))) _).
    + apply bpc_mult_swap.
    + apply (real_eq_trans _ (real_mult Z12 real_one) _).
      * apply (RealSetoid.real_eq_mult_compat Z12
                 (real_mult Z1 (real_inv_pos Z1 p1)) Z12 real_one).
        -- apply real_eq_refl.
        -- apply real_inv_pos_correct.
      * apply real_mult_one.
Qed.

(* ---------- 件 1 卫星（语义桥）：条件质量和 == 比值形态 ---------- *)
(* Z2|kept1 的两个构造形态重合：Σ_{P12} Proj1 == Z12·inv Z1。       *)
Lemma bpc_cond_semantics : real_eq Zc_proj1 Zc.
Proof.
  apply (real_eq_trans _ (real_mult (real_inv_pos Z1 p1) Z12) _).
  - apply bpc_Zc_proj1_sum.
  - unfold Zc. apply real_mult_comm.
Qed.

(* ---------- 复合件 0：条件质量 ∈ (0,1] ------------------------- *)
(* Zc ≤ 1：Zc == Z12·inv Z1 ≤ Z1·inv Z1 == 1（支配 + inv 吸收）。   *)
Theorem Zc_le_one : real_le Zc real_one.
Proof.
  apply (real_le_trans _ (real_mult Z1 (real_inv_pos Z1 p1))).
  - exact (real_le_mult_compat Z12 Z1 (real_inv_pos Z1 p1)
             (real_inv_pos_pos Z1 p1) bpc_Z12_le_Z1).
  - apply (RealSetoid.real_eq_le (real_mult Z1 (real_inv_pos Z1 p1)) real_one).
    apply real_inv_pos_correct.
Qed.

(* ---------- log 复合核：log Z12 == log Z1 + log Zc -------------- *)
(* 端点乘法复合的 log 侧形态；real_log_mult 证书槽与 wd 桥同形       *)
(* （real_mult_positive Z1 Zc p1 Zc_pos，透明证书纪律）。            *)
Lemma bpc_log_Z12_split :
  real_eq (real_log Z12 p12)
          (real_plus (real_log Z1 p1) (real_log Zc Zc_pos)).
Proof.
  apply (real_eq_trans _
           (real_log (real_mult Z1 Zc) (real_mult_positive Z1 Zc p1 Zc_pos)) _).
  - exact (real_log_wd Z12 (real_mult Z1 Zc) p12
             (real_mult_positive Z1 Zc p1 Zc_pos) Z_compound_mul).
  - exact (real_log_mult Z1 Zc p1 Zc_pos).
Qed.

(* ---------- 代价端点乘法复合：−log Z1 + −log Zc == −log Z12 ----- *)
Lemma bpc_cost_mul_split :
  real_eq (real_plus (real_opp (real_log Z1 p1))
                     (real_opp (real_log Zc Zc_pos)))
          (real_opp (real_log Z12 p12)).
Proof.
  apply (real_eq_trans _
           (real_opp (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))) _).
  - apply real_eq_sym. apply real_opp_plus.
  - apply (RealSetoid.real_eq_opp_compat
             (real_plus (real_log Z1 p1) (real_log Zc Zc_pos))
             (real_log Z12 p12)).
    apply real_eq_sym. apply bpc_log_Z12_split.
Qed.

(* ---------- 件 2（主件·KL 代价链可加）--------------------------- *)
(* 母定理两次（P1 与 P12）+ 代价端点分裂 + 三臂消元：                *)
(*   A+(−(real_log Z1 p1)) == KLqf == B+(−l12) == B+((−(real_log Z1 p1))+(−lc)) == (B+(−(real_log Z1 p1)))+(−lc) *)
(*   两侧经 (x+(−t))+t 搬移得 A == B+(−lc)。                         *)
(* q 前提诚实给出：归一化 + 逐点正 + 复合掩码兼容（P12 假 ⟹ q=0，    *)
(* 由 andb false 支定义性导出一级兼容，单一前提覆盖两级）。           *)
Theorem proj_kl_chain : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (andb (P1 i) (P2 i)) false -> real_eq (q i) real_zero),
  real_eq (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
          (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                     (real_opp (real_log Zc Zc_pos))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  assert (Hqf1 : forall i : I, Id (P1 i) false -> real_eq (q i) real_zero).
  { intro i. intro Heq1. apply (Hq_fail i).
    exact (projp_id_transport bool false (P1 i)
             (fun b : bool => Id (andb b (P2 i)) false)
             id_refl (id_sym Heq1)). }
  pose proof (proj_kl_cost I f P1 idx f_pos P1_witness q Hq_norm Hq_pos Hqf1) as H1.
  pose proof (proj_kl_cost I f P12 idx f_pos P12_witness q Hq_norm Hq_pos Hq_fail) as H2.
  assert (Hj1 : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                   (real_opp (real_log Z1 p1)))
                        (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))).
  { apply (real_eq_trans _ (KLqf I f idx f_pos q Hq_pos) _).
    - apply real_eq_sym. exact H1.
    - exact H2. }
  assert (Hj2 : real_eq (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                   (real_opp (real_log Z12 p12)))
                        (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                        (real_plus (real_opp (real_log Z1 p1))
                                   (real_opp (real_log Zc Zc_pos)))) _).
    - apply (RealSetoid.real_eq_plus_compat
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Z12 p12))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_plus (real_opp (real_log Z1 p1))
                          (real_opp (real_log Zc Zc_pos)))).
      + apply real_eq_refl.
      + apply real_eq_sym. apply bpc_cost_mul_split.
    - apply real_plus_assoc. }
  assert (Hjoin : real_eq (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                                (real_opp (real_log Z1 p1)))
                                     (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _ (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                      (real_opp (real_log Z12 p12))) _).
    - exact Hj1.
    - exact Hj2. }
  assert (Hright : real_eq
    (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos)))
               (real_log Z1 p1))
    (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos)))).
  { apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1))) (real_log Z1 p1))
                        (real_opp (real_log Zc Zc_pos))) _) .
    - exact (bpc_assoc_swap (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                       (real_opp (real_log Z1 p1)))
                            (real_opp (real_log Zc Zc_pos)) (real_log Z1 p1)) .
    - apply (RealSetoid.real_eq_plus_compat
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1))) (real_log Z1 p1))
               (real_opp (real_log Zc Zc_pos))
               (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
               (real_opp (real_log Zc Zc_pos))).
      + apply bpc_cancel_add_opp.
      + apply real_eq_refl. }
  apply (real_eq_trans _
           (real_plus (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                                 (real_opp (real_log Z1 p1))) (real_log Z1 p1)) _).
  - apply real_eq_sym. apply bpc_cancel_add_opp.
  - apply (real_eq_trans _
             (real_plus (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                              (real_opp (real_log Z1 p1)))
                                   (real_opp (real_log Zc Zc_pos)))
                        (real_log Z1 p1)) _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus (KLqp I f P1 idx f_pos P1_witness q Hq_pos)
                          (real_opp (real_log Z1 p1))) (real_log Z1 p1)
               (real_plus (real_plus (KLqp I f P12 idx f_pos P12_witness q Hq_pos)
                                     (real_opp (real_log Z1 p1)))
                          (real_opp (real_log Zc Zc_pos))) (real_log Z1 p1)).
      * exact Hjoin.
      * apply real_eq_refl.
    + exact Hright.
Qed.

(* ---------- 件 3a：封口代价区间端点（质量夹逼）------------------- *)
(* 单侧信息投影版：S ≤ Z12 ≤ S+U（S,U,S+U > 0 的证书前提）⟹          *)
(*   −log(S+U) ≤ −log Z12 ≤ −log S。                                  *)
(* 两端皆定理：log 单调（real_log_le_mono）+ 取负反向                  *)
(* （real_opp_le_compat）；端点乘法复合见 bpc_cost_mul_split。         *)
Theorem proj_cost_interval : forall (S U : Real)
  (HSp : real_lt real_zero S)
  (HUp : real_lt real_zero (real_plus S U))
  (Hlo : real_le S Z12) (Hhi : real_le Z12 (real_plus S U)),
  And (real_le (real_opp (real_log (real_plus S U) HUp))
               (real_opp (real_log Z12 p12)))
      (real_le (real_opp (real_log Z12 p12))
               (real_opp (real_log S HSp))).
Proof.
  intros S U HSp HUp Hlo Hhi.
  split.
  - apply (real_opp_le_compat (real_log Z12 p12)
             (real_log (real_plus S U) HUp)).
    apply (real_log_le_mono Z12 (real_plus S U) p12 HUp).
    exact Hhi.
  - apply (real_opp_le_compat (real_log S HSp) (real_log Z12 p12)).
    apply (real_log_le_mono S Z12 HSp p12).
    exact Hlo.
Qed.

(* ---------- 件 3b：全保留端点（下端点精确值 0）------------------- *)
(* P12 ≡ true ⟹ Z12 == 1（f_norm 桥）⟹ −log Z12 == 0：                *)
(* 封口代价区间 [−log(S_t+U_t), −log S_t] 的 U_t→0 / S_t→1 退化象，    *)
(* 与件 3a 夹逼件在端点处精确闭合。                                   *)
Theorem proj_cost_full_mask_zero :
  (forall i : I, Id (P12 i) true) ->
  real_eq (real_opp (real_log Z12 p12)) real_zero.
Proof.
  intro Hall.
  assert (HZ1 : real_eq Z12 real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P12 i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P12 y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (Hall y)).
    - exact f_norm. }
  assert (Hlog : real_eq (real_log Z12 p12) real_zero).
  { apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
    - exact (real_log_wd Z12 real_one p12 real_lt_zero_one HZ1).
    - apply (real_log_one real_lt_zero_one). }
  apply (real_eq_trans _ (real_opp real_zero) _).
  - apply (RealSetoid.real_eq_opp_compat (real_log Z12 p12) real_zero Hlog).
  - apply bpc_opp_zero.
Qed.

End BPChain.
