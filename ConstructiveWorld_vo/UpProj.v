(* ============================================================ *)
(* UpProj.v — 四象归一：抽象投影核母定理（Real 层 list 世界）      *)
(*                                                              *)
(*   三象 grep 实证定义同构（KV 逐出 / 安全过滤 / Min-P 截断），    *)
(*   本文件提取母定理并回接三象实例：                             *)
(*     母签名：I（索引）、f（被投影权重）、P（bool 保留谓词）、     *)
(*     idx（枚举）、f_norm（f 归一化）、f_pos（f 逐点正）、        *)
(*     P_witness（保留集非空见证 sigT——ZP_pos 由之升级为定理）。   *)
(*   件 0 ZP_le_one / 件 1 proj_normalized / 件 2 proj_keep_ge    *)
(*   件 3 proj_drop_zero / 件 4 proj_kl_cost（代价恒等·主件）      *)
(*   件 5 proj_minor_uncond（minorization 传送）/ 件 6            *)
(*   proj_uniform_full（P≡true 退化象 = 温度极限象的推论级连接）。  *)
(*                                                              *)
(*   全部 Set 层（Id/And/Or/sigT），语句零 Prop 泄露；            *)
(*   纯构造性：仅依赖 CW_ConstructiveWorld_219，无外部假设。       *)
(*   日志证书形态：real_log 正性证书随身（keep_form_pos 透明       *)
(*   Definition，对齐 UpAuditBridge 透明证书纪律）。              *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ---------- 通用助推（Set 层，规避根内 match-Hin 污染源） ---------- *)
(* Id 沿 Bool 的双子目标投影（UpKVEv kvev_id_transport 先例：       *)
(* 规避 destruct-eqn 对前提的静默代换）。                           *)
Lemma projp_id_transport : forall (A : Set) (x y : A) (M : A -> Set),
  M x -> Id x y -> M y.
Proof.
  intros A x y M m H. exact (match H with id_refl => m end).
Qed.

(* 单项 ≤ 全和（对 InT 推导本身归纳，Nil 矛盾支不进证明项——       *)
(* 根内 single_le_sum_aux 的空 match 提取会产生魔力包装，不复用）。  *)
Lemma projp_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* ---------- 基础代数（real_eq 层小工具） ---------- *)

Lemma projp_plus_zero_l : forall x : Real, real_eq (real_plus real_zero x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_plus x real_zero) _).
  - apply real_plus_comm.
  - apply real_plus_zero.
Qed.

Lemma projp_plus_zero_opp : forall a : Real, real_eq (real_plus (real_opp a) a) real_zero.
Proof.
  intro a. apply (real_eq_trans _ (real_plus a (real_opp a)) _).
  - apply real_plus_comm.
  - apply real_plus_opp.
Qed.

(* a − c == (a − b) + (b − c)（minus_split 的 Real 形态） *)
Lemma projp_minus_split : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof.
  intros a b c.
  apply (real_eq_trans _ (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c)))) _).
  - apply (RealSetoid.real_eq_plus_compat a (real_opp c) a
             (real_plus (real_opp b) (real_plus b (real_opp c)))
             (real_eq_refl a)
             (real_eq_sym _ _
               (real_eq_trans (real_plus (real_opp b) (real_plus b (real_opp c)))
                              (real_plus (real_plus (real_opp b) b) (real_opp c))
                              (real_opp c)
                              (real_plus_assoc (real_opp b) b (real_opp c))
                              (real_eq_trans
                                 (real_plus (real_plus (real_opp b) b) (real_opp c))
                                 (real_plus real_zero (real_opp c))
                                 (real_opp c)
                                 (RealSetoid.real_eq_plus_compat
                                    (real_plus (real_opp b) b) (real_opp c)
                                    real_zero (real_opp c)
                                    (projp_plus_zero_opp b) (real_eq_refl _))
                                 (projp_plus_zero_l (real_opp c)))))).
  - apply (real_plus_assoc a (real_opp b) (real_plus b (real_opp c))).
Qed.

(* (x − L) − x == −L（minus_plus_opp 的 Real 形态） *)
Lemma projp_minus_plus_opp : forall x L : Real,
  real_eq (real_plus (real_plus x (real_opp L)) (real_opp x)) (real_opp L).
Proof.
  intros x L.
  exact (real_eq_trans _ _ _
    (real_eq_sym _ _ (real_plus_assoc x (real_opp L) (real_opp x)))
    (real_eq_trans _ _ _
      (RealSetoid.real_eq_plus_compat x (real_plus (real_opp L) (real_opp x))
                                      x (real_plus (real_opp x) (real_opp L))
                                      (real_eq_refl x)
                                      (real_plus_comm (real_opp L) (real_opp x)))
      (real_eq_trans _ _ _
        (real_plus_assoc x (real_opp x) (real_opp L))
        (real_eq_trans _ _ _
          (RealSetoid.real_eq_plus_compat (real_plus x (real_opp x)) (real_opp L)
                                          real_zero (real_opp L)
                                          (real_plus_opp x) (real_eq_refl _))
          (projp_plus_zero_l (real_opp L)))))). 
Qed.

(* log inv == −log x（log_inv_one_inv 的 Real 层形态） *)
Lemma projp_log_inv_neg : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
          (real_opp (real_log x Hx)).
Proof.
  intros x Hx.
  assert (Hsum : real_eq (real_plus (real_log x Hx)
                                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                         real_zero).
  { apply (real_eq_trans _ (real_log (real_mult x (real_inv_pos x Hx))
                                     (real_mult_positive x (real_inv_pos x Hx) Hx
                                       (real_inv_pos_pos x Hx))) _).
    - apply (real_eq_sym _ _ (real_log_mult x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))).
    - apply (real_eq_trans _ (real_log real_one real_lt_zero_one) _).
      + apply (real_log_wd (real_mult x (real_inv_pos x Hx)) real_one
                 (real_mult_positive x (real_inv_pos x Hx) Hx (real_inv_pos_pos x Hx))
                 real_lt_zero_one (real_inv_pos_correct x Hx)).
      + apply (real_log_one real_lt_zero_one). }
  assert (Hdir : real_eq (real_opp (real_log x Hx))
                         (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
  { apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx)) real_zero) _).
    - apply (real_eq_sym _ _ (real_plus_zero (real_opp (real_log x Hx)))).
    - apply (real_eq_trans _ (real_plus (real_opp (real_log x Hx))
                                        (real_plus (real_log x Hx)
                                                   (real_log (real_inv_pos x Hx)
                                                             (real_inv_pos_pos x Hx)))) _).
      + apply (RealSetoid.real_eq_plus_compat (real_opp (real_log x Hx)) real_zero
                 (real_opp (real_log x Hx))
                 (real_plus (real_log x Hx)
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx)))
                 (real_eq_refl _)
                 (real_eq_sym (real_plus (real_log x Hx)
                                         (real_log (real_inv_pos x Hx)
                                                   (real_inv_pos_pos x Hx)))
                              real_zero Hsum)).
      + apply (real_eq_trans _
                 (real_plus (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                            (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
        * apply (real_plus_assoc (real_opp (real_log x Hx)) (real_log x Hx)
                    (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))).
        * apply (real_eq_trans _ (real_plus real_zero
                                   (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))) _).
          -- apply (RealSetoid.real_eq_plus_compat
                       (real_plus (real_opp (real_log x Hx)) (real_log x Hx))
                       (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       real_zero (real_log (real_inv_pos x Hx) (real_inv_pos_pos x Hx))
                       (projp_plus_zero_opp (real_log x Hx)) (real_eq_refl _)).
          -- apply projp_plus_zero_l. }
  apply (real_eq_sym _ _ Hdir).
Qed.

(* ============================================================ *)
(* 母 Section：抽象投影核（四象归一的规范形）                      *)
(*   Z_P = 保留质量；Proj = 保留支 f·inv(Z_P)、逐出支零。          *)
(* ============================================================ *)
Section AbstractProjection.

Variable I : Set.                          (* 索引类型 *)
Variable f : I -> Real.                    (* 被投影权重 *)
Variable P : I -> bool.                    (* 保留谓词 *)
Variable idx : list I.                     (* 枚举 *)
Variable f_norm : real_eq (real_list_sum I f idx) real_one.   (* f 归一化 *)
Variable f_pos : forall i : I, real_lt real_zero (f i).       (* f 逐点正 *)
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

(* 保留质量（三象分母的公共形态：Σ if P then f else 0） *)
Definition Z_P : Real :=
  real_list_sum I (fun i : I => if P i then f i else real_zero) idx.

(* ---------- 件 0a：Z_P > 0（由 P 有点 + f_pos + single_le_sum 放电） ---------- *)
(* UpKVEv Z_keep_pos 同款——ZP_pos 由 Variable 升级为定理。           *)
Lemma Z_P_entry_nonneg : forall (y : I),
  real_le real_zero (if P y then f y else real_zero).
Proof.
  intro y. destruct (P y).
  - apply real_le_from_lt_aux. apply f_pos.
  - apply real_le_refl.
Qed.

Theorem ZP_pos : real_lt real_zero Z_P.
Proof.
  destruct P_witness as [i0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if P i0 then f i0 else real_zero)).
  { apply (projp_id_transport bool true (P i0)
             (fun b : bool => real_lt real_zero (if b then f i0 else real_zero))).
    - exact (f_pos i0).
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if P i0 then f i0 else real_zero) Z_P).
  { apply (projp_single_le_sum I
             (fun y : I => if P y then f y else real_zero) i0 idx Hin0).
    intro y. apply Z_P_entry_nonneg. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if P i0 then f i0 else real_zero) Z_P Hlt0 Heq).
Qed.

(* ---------- 件 0b：Z_P ≤ 1（保留子集和 ≤ 全和 + f_norm 桥） ---------- *)
Theorem ZP_le_one : real_le Z_P real_one.
Proof.
  apply (real_le_trans _ (real_list_sum I f idx)).
  - apply (real_list_sum_le I
             (fun i : I => if P i then f i else real_zero) f idx).
    intro y. destruct (P y).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply f_pos.
  - apply (RealSetoid.real_eq_le _ _). exact f_norm.
Qed.

(* 保留支形态（Proj 的 keep 支；log 证书的载体） *)
Definition keep_form (i : I) : Real :=
  real_mult (f i) (real_inv_pos Z_P ZP_pos).

(* keep 支正性证书（透明 Definition——log 项的随身证书） *)
Definition keep_form_pos (i : I) : real_lt real_zero (keep_form i) :=
  real_mult_positive (f i) (real_inv_pos Z_P ZP_pos)
                     (f_pos i) (real_inv_pos_pos Z_P ZP_pos).

(* 投影核（母形态：if P i then f i·inv(Z_P) else 0） *)
Definition Proj (i : I) : Real :=
  if P i then real_mult (f i) (real_inv_pos Z_P ZP_pos) else real_zero.

(* ---------- 件 3：逐出支归零 ---------- *)
Theorem proj_drop_zero : forall i : I,
  Id (P i) false -> real_eq (Proj i) real_zero.
Proof.
  intros i Hb.
  apply (projp_id_transport bool false (P i)
           (fun b : bool =>
              real_eq (if b then
                         real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 real_zero)).
  - apply real_eq_refl.
  - exact (id_sym Hb).
Qed.

(* ---------- keep 支放大器：f i ≤ f i·inv(Z_P)（Z_P ≤ 1 + inv 反单调） ---------- *)
Lemma proj_keep_form_ge : forall i : I,
  real_le (f i) (real_mult (f i) (real_inv_pos Z_P ZP_pos)).
Proof.
  intro i.
  apply (real_le_trans _ (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
  - (* f i == f·inv(1) 的 eq→le 桥 *)
    apply (RealSetoid.real_eq_le (f i)
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one))).
    apply real_eq_sym.
    apply (real_eq_trans _ (real_mult (f i) real_one) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos real_one real_lt_zero_one)
                (f i) real_one).
      * apply real_eq_refl.
      * apply (real_eq_trans _
                  (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
        -- apply real_eq_sym. apply b4_one_mult.
        -- apply real_inv_pos_correct.
    + apply real_mult_one.
  - apply (real_le_mult_compat_r (f i)
             (real_inv_pos real_one real_lt_zero_one)
             (real_inv_pos Z_P ZP_pos)).
    + apply real_le_from_lt_aux. apply f_pos.
    + apply (real_inv_pos_le_compat Z_P real_one ZP_pos real_lt_zero_one).
      apply ZP_le_one.
Qed.

(* ---------- 件 2：保留者放大（keep 支 f ≤ Proj） ---------- *)
Theorem proj_keep_ge : forall i : I,
  Id (P i) true -> real_le (f i) (Proj i).
Proof.
  intros i Hb.
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_le (f i)
                (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                 else real_zero))).
  - apply proj_keep_form_ge.
  - exact (id_sym Hb).
Qed.

(* ---------- 件 1：行归一化 Σ Proj == 1 ---------- *)
Theorem proj_normalized :
  real_eq (real_list_sum I (fun i : I => Proj i) idx) real_one.
Proof.
  (* 第一步：逐点改写 Proj 为 g(i)·inv(Z_P)，drop 支经 0·x == 0 归零 *)
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I =>
                 real_mult (if P i then f i else real_zero)
                           (real_inv_pos Z_P ZP_pos))
              idx) _).
  { apply (real_list_sum_ext I (fun i : I => Proj i) _ idx).
    intro y. destruct (P y) eqn:Hk.
    - unfold Proj. rewrite Hk. apply real_eq_refl.
    - unfold Proj. rewrite Hk.
      apply (real_eq_trans _
               (real_mult (real_inv_pos Z_P ZP_pos) real_zero) _).
      + apply real_eq_sym. apply real_mult_zero.
      + apply real_mult_comm. }
  (* 第二步：linear_r 提取常数 inv(Z_P) *)
  apply (real_eq_trans _
           (real_mult (real_inv_pos Z_P ZP_pos) Z_P) _).
  { apply (real_list_sum_linear_r I
             (real_inv_pos Z_P ZP_pos)
             (fun i : I => if P i then f i else real_zero) idx). }
  (* 第三步：inv(Z_P)·Z_P == 1（comm 桥 + real_inv_pos_correct） *)
  apply (real_eq_trans _ (real_mult Z_P (real_inv_pos Z_P ZP_pos)) _).
  - apply real_mult_comm.
  - apply real_inv_pos_correct.
Qed.

(* ---------- 件 5：minorization 传送（δ·u ≤ f ⟹ δ·u ≤ Proj，无条件式） ---------- *)
Variable u : I -> Real.                    (* 参考分布 *)
Variable delta : Real.
Variable delta_minor : forall i : I,
  real_le (real_mult delta (u i)) (f i).

Theorem proj_minor_uncond : forall i : I,
  real_le (if P i then real_mult delta (u i) else real_zero) (Proj i).
Proof.
  intro i. destruct (P i) eqn:Hk.
  - unfold Proj. rewrite Hk.
    apply (real_le_trans _ (f i)).
    + apply delta_minor.
    + apply proj_keep_form_ge.
  - unfold Proj. rewrite Hk. apply real_le_refl.
Qed.

(* ---------- 件 6：退化象（P ≡ true ⟹ Proj ≡ f；温度极限象的推论级连接） ---------- *)
Theorem proj_uniform_full :
  (forall i : I, Id (P i) true) -> forall i : I, real_eq (Proj i) (f i).
Proof.
  intro P_all. intro i.
  assert (HZ1 : real_eq Z_P real_one).
  { apply (real_eq_trans _ (real_list_sum I f idx) _).
    - apply (real_list_sum_ext I
               (fun i : I => if P i then f i else real_zero) f idx).
      intro y. apply (projp_id_transport bool true (P y)
                 (fun b : bool => real_eq (if b then f y else real_zero) (f y))).
      + apply real_eq_refl.
      + exact (id_sym (P_all y)).
    - exact f_norm. }
  apply (projp_id_transport bool true (P i)
           (fun b : bool =>
              real_eq (if b then real_mult (f i) (real_inv_pos Z_P ZP_pos)
                       else real_zero)
                 (f i))).
  - apply (real_eq_trans _
             (real_mult (f i) (real_inv_pos real_one real_lt_zero_one)) _).
    + apply (RealSetoid.real_eq_mult_compat
                (f i) (real_inv_pos Z_P ZP_pos)
                (f i) (real_inv_pos real_one real_lt_zero_one)).
      * apply real_eq_refl.
      * apply (real_inv_pos_ext Z_P real_one ZP_pos real_lt_zero_one HZ1).
    + apply (real_eq_trans _ (real_mult (f i) real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                  (f i) (real_inv_pos real_one real_lt_zero_one) (f i) real_one).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _
                      (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) _).
           ++ apply real_eq_sym. apply b4_one_mult.
           ++ apply real_inv_pos_correct.
      * apply real_mult_one.
  - exact (id_sym (P_all i)).
Qed.

End AbstractProjection.

(* ============================================================ *)
(* 件 4：代价恒等（母形态，root kl_sum_split/kl_tail_eval 的       *)
(*   Real 层 list 版）。KL 项按「log 正性证书随身」纪律定义：       *)
(*   对 Proj 的 KL 用掩码形态（keep 支即 keep_form，delta 相等）    *)
(*   规避 drop 支 log 零前提；fail 支由 Hq_fail 归零。             *)
(* ============================================================ *)
Section AbstractKL.

Variable I : Set.
Variable f : I -> Real.
Variable P : I -> bool.
Variable idx : list I.
Variable f_norm : real_eq (real_list_sum I f idx) real_one.
Variable f_pos : forall i : I, real_lt real_zero (f i).
Variable P_witness : sigT (fun i : I => And (Id (P i) true) (InT i idx)).

Definition ZK : Real := Z_P I f P idx.
Definition keepK (i : I) : Real := keep_form I f P idx f_pos P_witness i.
Definition keepK_pos (i : I) : real_lt real_zero (keepK i) :=
  keep_form_pos I f P idx f_pos P_witness i.

(* KL 逐项（q‖f：无条件正性；q‖Proj 与尾项：P 掩码形态） *)
Definition KL_f_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  real_mult (q i) (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (f i) (f_pos i)))).
Definition KL_P_term (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (q i) (Hq i))
                               (real_opp (real_log (keepK i) (keepK_pos i))))
  else real_zero.
Definition KL_T_term (q : I -> Real) (i : I) : Real :=
  if P i then
    real_mult (q i) (real_plus (real_log (keepK i) (keepK_pos i))
                               (real_opp (real_log (f i) (f_pos i))))
  else real_zero.
Definition KL_f_masked (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i))
  (i : I) : Real :=
  if P i then KL_f_term q Hq i else real_zero.

Definition KLqf (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_term q Hq) idx.
Definition KLfm (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_f_masked q Hq) idx.
Definition KLqp (q : I -> Real) (Hq : forall i : I, real_lt real_zero (q i)) : Real :=
  real_list_sum I (KL_P_term q Hq) idx.
Definition KLqt (q : I -> Real) : Real :=
  real_list_sum I (KL_T_term q) idx.

(* 第 1 步：桥——兼容 q 在 drop 支归零后，无掩码和 == 掩码和 *)
Lemma proj_kl_bridge : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqf q Hq) (KLfm q Hq).
Proof.
  intros q Hq Hq_fail.
  apply (real_list_sum_ext I (KL_f_term q Hq) (KL_f_masked q Hq) idx).
  intro y. unfold KL_f_masked. destruct (P y) eqn:Hb.
  - apply real_eq_refl.
  - assert (Hid : Id (P y) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail y Hid) as Hq0.
    apply (real_eq_trans _ (real_mult real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q y)
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               real_zero
               (real_plus (real_log (q y) (Hq y))
                          (real_opp (real_log (f y) (f_pos y))))
               Hq0 (real_eq_refl _)).
    + apply (real_eq_trans _
               (real_mult (real_plus (real_log (q y) (Hq y))
                                     (real_opp (real_log (f y) (f_pos y))))
                          real_zero) _).
      * apply real_mult_comm.
      * apply real_mult_zero.
Qed.

(* 第 2 步：掩码逐点分解（keep 支经 minus_split+distrib；drop 支零和零） *)
Lemma proj_kl_pointwise_split : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)) (i : I),
  real_eq (KL_f_masked q Hq i) (real_plus (KL_P_term q Hq i) (KL_T_term q i)).
Proof.
  intros q Hq i. unfold KL_f_masked, KL_P_term, KL_T_term.
  destruct (P i).
  - apply (real_eq_trans _
             (real_mult (q i)
                (real_plus
                   (real_plus (real_log (q i) (Hq i))
                              (real_opp (real_log (keepK i) (keepK_pos i))))
                   (real_plus (real_log (keepK i) (keepK_pos i))
                              (real_opp (real_log (f i) (f_pos i)))))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_plus
                  (real_plus (real_log (q i) (Hq i))
                             (real_opp (real_log (keepK i) (keepK_pos i))))
                  (real_plus (real_log (keepK i) (keepK_pos i))
                             (real_opp (real_log (f i) (f_pos i)))))
               (real_eq_refl _)
               (projp_minus_split (real_log (q i) (Hq i))
                                  (real_log (keepK i) (keepK_pos i))
                                  (real_log (f i) (f_pos i)))).
    + apply (real_distrib (q i)
               (real_plus (real_log (q i) (Hq i))
                          (real_opp (real_log (keepK i) (keepK_pos i))))
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))).
  - apply real_eq_sym. apply real_plus_zero.
Qed.

(* 第 3 步：和级分解 Σ(q‖f 掩码) == Σ(q‖Proj) + Σ 尾项 *)
Lemma proj_kl_split_sum : forall (q : I -> Real)
  (Hq : forall i : I, real_lt real_zero (q i)),
  real_eq (KLfm q Hq) (real_plus (KLqp q Hq) (KLqt q)).
Proof.
  intros q Hq.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx) _).
  - apply (real_list_sum_ext I (KL_f_masked q Hq)
             (fun i : I => real_plus (KL_P_term q Hq i) (KL_T_term q i)) idx).
    exact (proj_kl_pointwise_split q Hq).
  - apply (real_list_sum_add I (KL_P_term q Hq) (KL_T_term q) idx).
Qed.

(* 第 4 步：尾项逐点 == (−log Z_P)·q（keep 支经 log_mult+log_inv_neg；
   drop 支 q 归零两侧归零，照抄根 kl_tail_eval 骨架） *)
Lemma proj_kl_tail_pt : forall (q : I -> Real)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero) (i : I),
  real_eq (KL_T_term q i)
          (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                     (q i)).
Proof.
  intros q Hq_fail i. unfold KL_T_term. destruct (P i) eqn:Hb.
  - assert (HL : real_eq (real_log (keepK i) (keepK_pos i))
                         (real_plus (real_log (f i) (f_pos i))
                                    (real_opp (real_log ZK
                                                (ZP_pos I f P idx f_pos P_witness))))).
    { apply (real_eq_trans _
               (real_log (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                         (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                             (f_pos i)
                                             (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
      - apply (real_log_wd (keepK i)
                 (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (keepK_pos i)
                 (real_mult_positive (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                     (f_pos i)
                                     (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_eq_refl (real_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))))).
      - apply (real_eq_trans _
                 (real_plus (real_log (f i) (f_pos i))
                            (real_log (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                                      (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness)))) _).
        + apply (real_log_mult (f i) (real_inv_pos ZK (ZP_pos I f P idx f_pos P_witness))
                   (f_pos i) (real_inv_pos_pos ZK (ZP_pos I f P idx f_pos P_witness))).
        + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
                   (projp_log_inv_neg ZK (ZP_pos I f P idx f_pos P_witness))). }
    assert (Hmid : real_eq (real_plus (real_log (keepK i) (keepK_pos i))
                                      (real_opp (real_log (f i) (f_pos i))))
                           (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
    { apply (real_eq_trans _
               (real_plus (real_plus (real_log (f i) (f_pos i))
                                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))))
                          (real_opp (real_log (f i) (f_pos i)))) _).
      - apply (RealSetoid.real_eq_plus_compat _ _ _ _ HL (real_eq_refl _)).
      - apply projp_minus_plus_opp. }
    apply (real_eq_trans _
             (real_mult (q i)
                (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))) _).
    + apply (RealSetoid.real_eq_mult_compat (q i)
               (real_plus (real_log (keepK i) (keepK_pos i))
                          (real_opp (real_log (f i) (f_pos i))))
               (q i)
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (real_eq_refl _) Hmid).
    + apply real_mult_comm.
  - assert (Hid : Id (P i) false). { rewrite Hb. apply id_refl. }
    pose proof (Hq_fail i Hid) as Hq0.
    apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply (RealSetoid.real_eq_mult_compat
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               real_zero
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
               (q i) (real_eq_refl _) (real_eq_sym (q i) real_zero Hq0)).
Qed.

(* 第 5 步：尾项求值 Σ 尾 == −log Z_P（ext + linear + 归一化消去） *)
Lemma proj_kl_tail_eval : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
  real_eq (KLqt q) (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))).
Proof.
  intros q Hq_norm Hq_fail.
  apply (real_eq_trans _
           (real_list_sum I
              (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                      (q i)) idx) _).
  - apply (real_list_sum_ext I (KL_T_term q)
             (fun i : I => real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                                     (q i)) idx).
    intro w. exact (proj_kl_tail_pt q Hq_fail w).
  - apply (real_eq_trans _
             (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                        (real_list_sum I q idx)) _).
    + apply (real_list_sum_linear I
               (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness))) q idx).
    + apply (real_eq_trans _
               (real_mult (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                          real_one) _).
      * apply (RealSetoid.real_eq_mult_compat
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 (real_list_sum I q idx)
                 (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))
                 real_one (real_eq_refl _) Hq_norm).
      * apply real_mult_one.
Qed.

(* 件 4（主件·代价恒等）：KL(q‖f) == KL(q‖Proj) + (−log Z_P)。
   审计/截断/逐出的信息代价 = 保留质量亏损对数，一次证明三象通用。 *)
Theorem proj_kl_cost : forall (q : I -> Real)
  (Hq_norm : real_eq (real_list_sum I q idx) real_one)
  (Hq_pos : forall i : I, real_lt real_zero (q i))
  (Hq_fail : forall i : I, Id (P i) false -> real_eq (q i) real_zero),
   real_eq (KLqf q Hq_pos)
          (real_plus (KLqp q Hq_pos)
                     (real_opp (real_log ZK (ZP_pos I f P idx f_pos P_witness)))).
Proof.
  intros q Hq_norm Hq_pos Hq_fail.
  apply (real_eq_trans _ (real_plus (KLqp q Hq_pos) (KLqt q)) _).
  - apply (real_eq_trans _ (KLfm q Hq_pos) _).
    + exact (proj_kl_bridge q Hq_pos Hq_fail).
    + exact (proj_kl_split_sum q Hq_pos).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
             (proj_kl_tail_eval q Hq_norm Hq_fail)).
Qed.

End AbstractKL.

(* ============================================================ *)
(* 实例接入（三象回收）。判据：实例引理证明体短于原证明体。          *)
(* 接缝注记见各 Section 头注释。                                   *)
(* ============================================================ *)

(* ---------- 实例 A：KV 逐出（UpKVEv 的行归一化/件 0/2/2b/3 回收） ----------
   接缝：母签名与 UpKVEv 世界逐参对齐（I:=Tok，f:=K s 固定行，P:=keep）。
   f_norm:=Krow s、f_pos:=Kpos s、P_witness:=keep_nonempty 直通；           *)
Section InstKV.

Variables (Tok : Set) (states : list Tok) (K : Tok -> Tok -> Real)
          (keep : Tok -> bool).
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep_nonempty : sigT (fun s0 : Tok => And (Id (keep s0) true) (InT s0 states)).

Definition Zkv (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.
Definition Kev (s s' : Tok) : Real :=
  if keep s' then
    real_mult (K s s') (real_inv_pos (Zkv s) (ZP_pos Tok (K s) keep states (Kpos s) keep_nonempty))
  else real_zero.

Theorem kev_Zkv_le_one_via_proj : forall s : Tok, real_le (Zkv s) real_one.
Proof.
  intro s. exact (ZP_le_one Tok (K s) keep states (Krow s) (Kpos s)).
Qed.

Theorem kev_row_normalized_via_proj : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => Kev s s') states) real_one.
Proof.
  intro s. exact (proj_normalized Tok (K s) keep states (Kpos s) keep_nonempty).
Qed.

Theorem kev_drop_zero_via_proj : forall s s' : Tok,
  Id (keep s') false -> real_eq (Kev s s') real_zero.
Proof.
  intros s s' H. exact (proj_drop_zero Tok (K s) keep states (Kpos s) keep_nonempty s' H).
Qed.

Theorem kev_keep_ge_via_proj : forall s s' : Tok,
  Id (keep s') true -> real_le (K s s') (Kev s s').
Proof.
  intros s s' H. exact (proj_keep_ge Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty s' H).
Qed.

Variables (Ukv : Tok -> Real) (deltakv : Real).
Variable delta_minor_kv : forall s s' : Tok,
  real_le (real_mult deltakv (Ukv s')) (K s s').

Theorem kev_minor_uncond_via_proj : forall s s' : Tok,
  real_le (if keep s' then real_mult deltakv (Ukv s') else real_zero) (Kev s s').
Proof.
  intros s s'.
  exact (proj_minor_uncond Tok (K s) keep states (Krow s) (Kpos s) keep_nonempty
                           Ukv deltakv (delta_minor_kv s) s').
Qed.

End InstKV.

(* ---------- 实例 B：安全过滤（根 KLProjection 的 Real 层重述） ----------
   接缝：根 projected_normalized 在接口 R 层（sum_over_S/StateSpace），
   本实例按母定理在 Real-list 层同形重述（Z_aud/投影分布/归一化三件
   同构）；根侧接缝留接口实例化，不在此桥。                             *)
Section InstAudit.

Variables (St : Set) (states : list St) (p : St -> Real) (post_aud : St -> bool).
Variable p_norm : real_eq (real_list_sum St p states) real_one.
Variable p_pos : forall s : St, real_lt real_zero (p s).
Variable aud_witness : sigT (fun s : St => And (Id (post_aud s) true) (InT s states)).

Definition ZaudP : Real :=
  real_list_sum St (fun s : St => if post_aud s then p s else real_zero) states.
Definition proj_dist (s : St) : Real :=
  if post_aud s then
    real_mult (p s) (real_inv_pos ZaudP (ZP_pos St p post_aud states p_pos aud_witness))
  else real_zero.

Theorem Zaud_le_one_via_proj : real_le ZaudP real_one.
Proof.
  exact (ZP_le_one St p post_aud states p_norm p_pos).
Qed.

Theorem projected_normalized_via_proj :
  real_eq (real_list_sum St (fun s : St => proj_dist s) states) real_one.
Proof.
  exact (proj_normalized St p post_aud states p_pos aud_witness).
Qed.

Theorem projected_drop_zero_via_proj : forall s : St,
  Id (post_aud s) false -> real_eq (proj_dist s) real_zero.
Proof.
  intros s H. exact (proj_drop_zero St p post_aud states p_pos aud_witness s H).
Qed.

Theorem projected_keep_ge_via_proj : forall s : St,
  Id (post_aud s) true -> real_le (p s) (proj_dist s).
Proof.
  intros s H. exact (proj_keep_ge St p post_aud states p_norm p_pos aud_witness s H).
Qed.

End InstAudit.

(* ---------- 实例 C：Min-P（Set 载体重述 real_minp_markov_kernel） ----------
   接缝：根 RealMinPMain 的保留谓词是 Set 层命题+Or 判定器（非 bool）。
   本实例经 minp_bool（判定器的 bool 载体，构造性合法）接入母定理，
   再以 ext + inv_ext 双桥回收 match 形核的归一化；root Token:Type 与
   本席 Set 载体的差异为纯载体泛化（内容逐字同构）。                     *)
Section InstMinP.

Variables (W : Set) (vocab : list W).
Variable tf : W -> Real.
Variable tf_norm : real_eq (real_list_sum W tf vocab) real_one.
Variable tf_pos : forall w : W, real_lt real_zero (tf w).
(* 忠实镜像根 RealMinPMain 的判定接口（Set 谓词 + Or 判定器，非 bool） *)
Variable Kw : W -> Set.
Variable keep_dec : forall w : W, Or (Kw w) (Not (Kw w)).

Definition minp_bool (w : W) : bool :=
  match keep_dec w with inl _ => true | inr _ => false end.
Definition temp_sum : Real :=
  real_list_sum W
    (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end) vocab.
Variable temp_sum_pos : real_lt real_zero temp_sum.
(* 母形态见证（对应 root pick_max witness + in-vocab；root 侧非平凡部分
   已由 pick_max_token_minp_keep/pick_best_in_vocab' 证毕，此处为诚实接口） *)
Variable kept_witness : sigT (fun w : W => And (Id (minp_bool w) true) (InT w vocab)).

Definition minp_kernel (w : W) : Real :=
  match keep_dec w with
  | inl _ => real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
  | inr _ => real_zero
  end.

Theorem minp_normalized_via_proj :
  real_eq (real_list_sum W (fun w : W => minp_kernel w) vocab) real_one.
Proof.
  pose proof (proj_normalized W tf minp_bool vocab tf_pos kept_witness) as HP.
  assert (HZeq : real_eq (Z_P W tf minp_bool vocab) temp_sum).
  { apply (real_list_sum_ext W (fun w : W => if minp_bool w then tf w else real_zero)
             (fun w : W => match keep_dec w with inl _ => tf w | inr _ => real_zero end)
             vocab).
    intro w. unfold minp_bool. destruct (keep_dec w) as [Hk | Hd].
    - apply real_eq_refl.
    - apply real_eq_refl. }
  apply (real_eq_trans _
           (real_list_sum W
              (fun w : W => if minp_bool w then
                              real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                            else real_zero) vocab) _).
  - apply (real_list_sum_ext W (fun w : W => minp_kernel w) _ vocab).
    intro w. unfold minp_kernel, minp_bool. destruct (keep_dec w) as [Hk | Hd].
    + apply real_eq_refl.
    + apply real_eq_refl.
  - apply (real_eq_trans _
             (real_list_sum W
                (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab) _).
    + apply (real_list_sum_ext W
               (fun w : W => if minp_bool w then
                               real_mult (tf w) (real_inv_pos temp_sum temp_sum_pos)
                             else real_zero)
               (fun w : W => Proj W tf minp_bool vocab tf_pos kept_witness w) vocab).
      intro w. unfold minp_bool, Proj. destruct (keep_dec w) as [Hk | Hd].
      * apply (RealSetoid.real_eq_mult_compat (tf w)
                 (real_inv_pos temp_sum temp_sum_pos)
                 (tf w)
                 (real_inv_pos (Z_P W tf minp_bool vocab)
                               (ZP_pos W tf minp_bool vocab tf_pos kept_witness))).
      -- apply real_eq_refl.
      -- apply (real_inv_pos_ext temp_sum (Z_P W tf minp_bool vocab)
                   temp_sum_pos (ZP_pos W tf minp_bool vocab tf_pos kept_witness)
                   (real_eq_sym (Z_P W tf minp_bool vocab) temp_sum HZeq)).
      * apply real_eq_refl.
    + exact HP.
Qed.

End InstMinP.
