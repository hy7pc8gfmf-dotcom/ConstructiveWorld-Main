(* ============================================================
   EngineCeilingK.v — UpReqEngineCeiling 一般 k 参数化件。
   使命：兑现 UpReqEngineCeiling.v 双留记（:42 头注诚实边界段 +
     :351 G2b 主件注）「cec_kernel_coef 一般 k 形以参数化恒等式
     s == k·v + k(k+1)/2·v^2 + v^3·w 为显式假设」——本件对一般 k
     给出显式见证 w = eck_Wk k v 的无条件参数化恒等式，并据此把
     二阶反演主件升格为一般 k 无条件形（k=1 退化为已闭件
     cec_kernel_coef_k1）。
   路线（几何和 + 逐幂二阶 + 求和三归纳）：
     ① 几何和小引擎：eck_gsum + eck_geom_sum_closed（q_pow Q 层版
       闭式；库内 q_pow Q 层版缺，本件首节自建）；
     ② 逐幂面：eck_pow_minus_one / eck_q_pow_inv，合成 R6 核几何
       表象 eck_r6s_geom；步递推 eck_r6s_step；
     ③ 求和归纳：二阶系数递推引擎 eck_Wk（W_1 = 1/(1-v)，
       W_{k+1} = (W_k + b_{k+2})/(1-v)，b_k = k(k+1)/2）；主归纳
       eck_r6_param_k 一跳闭合；
     ④ 主定理 eck_kernel_coef_k：cec_kernel_coef 的一般 k 无条件实例。
   数学内核（fractions 数值抽检 k=1,2,3 与 1/(1-v)^k 幂展开逐系数
     一致）：s_k(v) = 1/(1-v)^k - 1；s_k = k·v + b_k·v^2 + v^3·W_k(v)；
     b_k = k(k+1)/2 = cec_r6_bcoef k；步恒等 b_{k+2} = b_{k+1} + (k+2)。
   构造性：纯构造性；Set 面 Qeq + sigT 见证装载（proj1 可计算提取）；
     非平凡真实现；全部 Qed 闭合零承认语句；文尾 Print Assumptions
     审计。每主件配四要素注明（对象/语句强度/边界/去向），见前注。
   编译配方：coqc -native-compiler no -q -Q . ""。
   对标：UpReqEngineCeiling.v:42/:351 留记语句面；cec_r6_bcoef。
   依赖：S01_BaseRing / S02_CauchyComplete（库内既有件）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqEngineCeiling.

(* ---- 0. Z 移位与非零性小引擎 ---- *)

(* Z 移位：z_{n+1} == z_n + 1（Qmake 原子统一；lia 走 Nat2Z 零名漂移） *)
Lemma eck_z_shift : forall n : nat,
  (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + (1 # 1).
Proof. intro n. unfold Qeq, Qplus. simpl. lia. Qed.

(* 正幂非零（Qeq 面；步乘积分裂使用 Qmult_integral_l） *)
Lemma eck_q_pow_neq0 : forall (x : Q) (n : nat),
  ~ (x == 0) -> ~ (q_pow x n == 0).
Proof.
  intros x n Hx. induction n as [| m IH].
  - intro H. unfold Qeq in H. simpl in H. lia.
  - simpl. intro H. apply IH.
    exact (Qmult_integral_l x (q_pow x m) Hx H).
Qed.

(* ---- 1. 几何和小引擎（q_pow Q 层版，库内缺自建） ---- *)

(* Σ_{j=0}^{k-1} x^j（内项取 j 形幂，防 S 错位） *)
Fixpoint eck_gsum (k : nat) (x : Q) : Q :=
  match k with
  | 0%nat => 0%Q
  | Datatypes.S m => eck_gsum m x + q_pow x m
  end.

(* 几何和闭式：(1-x)·Σ_{j<k} x^j == 1 - x^k（两归纳一 ring） *)
Lemma eck_geom_sum_closed : forall (k : nat) (x : Q),
  ((1 # 1) - x) * eck_gsum k x == (1 # 1) - q_pow x k.
Proof.
  intros k x. induction k as [| m IH].
  - cbn [eck_gsum q_pow]. ring.
  - cbn [eck_gsum q_pow].
    (* 分配律桥 + IH 代入 + 闭式合并（IH 模式被和式挡，直 rewrite 不中） *)
    apply (Qeq_trans _ (((1 # 1) - x) * eck_gsum m x
                        + ((1 # 1) - x) * q_pow x m)).
    + ring.
    + rewrite IH. ring.
Qed.

(* 逐幂差一：(x-1)·Σ_{j<k} x^j == x^k - 1（几何和反号直读） *)
Lemma eck_pow_minus_one : forall (k : nat) (x : Q),
  q_pow x k - (1 # 1) == (x - (1 # 1)) * eck_gsum k x.
Proof.
  intros k x.
  assert (E1 : x - (1 # 1) == - ((1 # 1) - x)) by ring.
  assert (E2 : q_pow x k - (1 # 1) == - ((1 # 1) - q_pow x k)) by ring.
  (* 序：E2 反号 → 闭式 RHS 侧代入（rewrite <-）→ E1 反号 → ring *)
  rewrite E2. rewrite <- (eck_geom_sum_closed k x). rewrite E1. ring.
Qed.

(* 倒数幂：t = 1/x 的 k 次幂 == 1/x^k（R6 核 t = 1/(1-v) 表象桥） *)
Lemma eck_q_pow_inv : forall (k : nat) (x : Q), ~ (x == 0) ->
  q_pow ((1 # 1) / x) k == (1 # 1) / q_pow x k.
Proof.
  intros k x Hx. induction k as [| m IH].
  - cbn [q_pow]. reflexivity.
  - assert (Hpm : ~ (q_pow x m == 0)) by (apply eck_q_pow_neq0; exact Hx).
    cbn [q_pow]. rewrite IH. field; cec_nz.
Qed.

(* ---- 2. R6 核的几何表象与步递推（逐幂一跳） ---- *)

(* R6 核几何表象：s_k(v) == (t-1)·Σ_{j<k} t^j，t = 1/(1-v)。
   【四要素】①对象：:42 留记「几何和」第一环；②语句：核的几何和表象
   等式（Qeq）；③强度：一般 k，仅 1-v≠0 域假设；④去向：兑现
   （几何和环节闭，使用本件自建 eck_gsum 引擎）。 *)
Lemma eck_r6s_geom : forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
  cec_r6_s k v ==
  (((1 # 1) / (1 - v)) - (1 # 1)) * eck_gsum k ((1 # 1) / (1 - v)).
Proof.
  intros k v Hv. unfold cec_r6_s.
  rewrite <- (eck_q_pow_inv k (1 - v) Hv).
  apply eck_pow_minus_one.
Qed.

(* 步递推：s_{k+1} == s_k/(1-v) + v/(1-v)（R6 核逐幂一跳；
   k=0 基例即已闭件 cec_r6_param_k1 的恒等式面） *)
Lemma eck_r6s_step : forall (k : nat) (v : Q),
  ~ ((1 # 1) - v == 0) -> ~ (q_pow (1 - v) k == 0) ->
  cec_r6_s (Datatypes.S k) v ==
  cec_r6_s k v / (1 - v) + ((1 # 1) * v) / (1 - v).
Proof.
  intros k v Hv Hk. unfold cec_r6_s. cbn [q_pow]. field; cec_nz.
Qed.

(* ---- 3. 二阶系数递推引擎 eck_Wk 与一般 k 参数化主恒等式 ---- *)

(* bcoef 步恒等：b_{k+2} == b_{k+1} + (k+2)（求和三常数 Σ1/Σj/ΣC(j,2)
   在递推侧的内敛形：二阶系数步增量即 k+2） *)
Lemma eck_bcoef_step : forall m : nat,
  cec_r6_bcoef (Datatypes.S (Datatypes.S m)) ==
  cec_r6_bcoef (Datatypes.S m) + (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1).
Proof.
  intro m. unfold cec_r6_bcoef.
  rewrite (eck_z_shift (Datatypes.S m)). rewrite (eck_z_shift m).
  field; cec_nz.
Qed.

(* W_k(v)：s_k(v) = k·v + b_k·v^2 + v^3·W_k(v) 的显式见证（分式递推，
   W_1 = 1/(1-v)，W_{k+1} = (W_k + b_{k+2})/(1-v)；k=1 与已闭件
   cec_r6_param_k1 的见证 1/(1-v) 恰合） *)
Fixpoint eck_Wk (n : nat) (v : Q) : Q :=
  match n with
  | 0%nat => (1 # 1) / (1 - v)
  | Datatypes.S m =>
      (eck_Wk m v + cec_r6_bcoef (Datatypes.S (Datatypes.S m))) / (1 - v)
  end.

(* 一般 k 参数化主恒等式（交付主件之一）：
   s_{k+1}(v) == (k+1)·v + b_{k+1}·v^2 + v^3·W_k(v)。
   【四要素】①对象：UpReqEngineCeiling.v:42/:351 留记「一般 k 形以
   参数化恒等式为显式假设」；②语句：见证 w = eck_Wk k v 显式给出，
   假设卸载（Qeq 无条件形）；③强度：一般 k 无条件（1-v≠0 为 q_pow/
   分母内禀域假设，非降级非虚报）；④边界：v=0 点两面包络仍闭
   （s=0 与右端同为 0），恒等式域内全域成立；无不可判定墙、无
   Or-encoding 墙，对照 GEOM-B R2.2 诚实边界先例对称登记。 *)
Theorem eck_r6_param_k : forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
  cec_r6_s (Datatypes.S k) v ==
  (Z.of_nat (Datatypes.S k) # 1) * v + cec_r6_bcoef (Datatypes.S k) * v * v
  + v * v * v * eck_Wk k v.
Proof.
  intros k v Hv. induction k as [| m IH].
  - cbn [eck_Wk]. exact (cec_r6_param_k1 v Hv).
  - assert (Hpm : ~ (q_pow (1 - v) (Datatypes.S m) == 0))
      by (apply eck_q_pow_neq0; exact Hv).
    rewrite (eck_r6s_step (Datatypes.S m) v Hv Hpm).
    rewrite IH. cbn [eck_Wk]. rewrite eck_bcoef_step.
    rewrite (eck_z_shift (Datatypes.S m)).
    field; cec_nz.
Qed.

(* sigT 装载件：一般 k 参数化见证包（proj1 = eck_Wk k v 可计算提取，
   Set 面透明设计，沿 UpReqUMixSelect 提取透明先例） *)
Definition eck_param_sig : Type :=
  forall (k : nat) (v : Q), ~ ((1 # 1) - v == 0) ->
    sigT (fun w : Q =>
      cec_r6_s (Datatypes.S k) v ==
      (Z.of_nat (Datatypes.S k) # 1) * v
      + cec_r6_bcoef (Datatypes.S k) * v * v + v * v * v * w).

Definition eck_param_pack : eck_param_sig :=
  fun (k : nat) (v : Q) (Hv : ~ ((1 # 1) - v == 0)) =>
    existT (fun w : Q =>
      cec_r6_s (Datatypes.S k) v ==
      (Z.of_nat (Datatypes.S k) # 1) * v
      + cec_r6_bcoef (Datatypes.S k) * v * v + v * v * v * w)
      (eck_Wk k v) (eck_r6_param_k k v Hv).

(* ---- 4. 主定理：cec_kernel_coef 一般 k 无条件形 ---- *)

(* 二阶反演一般 k 无条件实例：核二阶系数 (k+1)/(2k) = cec_r6_coef k
   对一般 k 承载，无需参数化恒等式假设（k=1 退化为 cec_kernel_coef_k1）。
   【四要素】①对象：UpReqEngineCeiling.v:351 G2b 主件条件形升格；
   ②语句：一般 k 无条件 Qeq 反演形，见证 w = eck_Wk k v；③强度：
   与 cec_kernel_coef_k1 同构且 k 自由（cec_kernel_coef 泛化形的最强
   可证形）；④边界：域假设 1-v≠0 与 s≠0（反演非零性）为内禀域假设，
   对照 GEOM-B R2.2 先例对称登记，无不可判定墙无 Or-encoding 墙。 *)
Theorem eck_kernel_coef_k : forall (k : nat) (v : Q),
  ~ ((1 # 1) - v == 0) -> ~ (cec_r6_s (Datatypes.S k) v == 0) ->
  Qeq ((Z.of_nat (Datatypes.S k) # 1) * v)
      (cec_r6_s (Datatypes.S k) v
       - cec_r6_coef (Datatypes.S k)
         * (cec_r6_s (Datatypes.S k) v * cec_r6_s (Datatypes.S k) v)
       + cec_r6_s (Datatypes.S k) v * cec_r6_s (Datatypes.S k) v
         * cec_r6_s (Datatypes.S k) v
         * cec_rho (Z.of_nat (Datatypes.S k) # 1) (cec_r6_bcoef (Datatypes.S k))
             (eck_Wk k v) v).
Proof.
  intros k v Hv Hs.
  apply (cec_kernel_coef (Datatypes.S k) v (eck_Wk k v)).
  - lia.
  - exact Hs.
  - apply eck_r6_param_k. exact Hv.
Qed.

(* ---- 5. 公理面审计 ---- *)

Print Assumptions eck_geom_sum_closed.
Print Assumptions eck_r6s_geom.
Print Assumptions eck_r6s_step.
Print Assumptions eck_r6_param_k.
Print Assumptions eck_param_pack.
Print Assumptions eck_kernel_coef_k.
