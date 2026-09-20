(* ============================================================ *)
(* UpAblP7_WallEps_CSM.v —— 逐 eps 三角不等式的实例化与行加权和形式重建 *)
(*                                                              *)
(* 数学使命：本件形式化 Bishop 逐 eps 三角不等式 |Σ f(s)| ≤ Σ|f(s)| + eps       *)
(*   （对一切 eps>0；csm_abs_sum_le_eps 为其库内直供形）的两类实例化：          *)
(*   其一，二元变号载体（uabp7we_mixed_f：true ↦ a、false ↦ −b）上的           *)
(*   uabp7we_csm_eps_twopt 与符号合取 uabp7we_twopt_mixed_sign；其二，          *)
(*   逐点非负核 K 的加权和行不等式 uabp7we_abs_row_eps（|Σ f(s)·K s s'| ≤       *)
(*   Σ|f s|·K s s' + eps），先以抽象核 uabp7we_abs_row_eps_absK 证明，          *)
(*   再以 rsq 核（rsq_u_r_kernel）全参实例化。                                  *)
(*                                                              *)
(* 数学背景：不带余量三角不等式 |Σf| ≤ Σ|f| 在变号系数下不可由接口字段导出       *)
(*   （UpReqConcSoftmax 对此有注记）；本件不给该形本身，只供其逐 eps 形的        *)
(*   重建件——rsq_u_abs_row 等下游结论的逐 eps 对应物由本件在链根补齐。          *)
(*                                                              *)
(* 依赖清单：CW_ConstructiveWorld_219、UpReqAlgebra、UpReqSumD、                 *)
(*   UpReqConcSoftmax（提供 csm_abs_sum_le_eps：逐 eps 三角不等式）、             *)
(*   UpReqSampling（提供 rsq_u_r_kernel/rsq_u_r_nonneg/rsq_u_abs_row 同形参照）； *)
(*   实例面 = RealEnhancedReal 具体层实例（导入后类型类解析，与源模块同源同解析）。*)
(*                                                              *)
(* 证明要点：二元约简 uabp7we_sumd_twopt 由 sumd_list_sum 的折叠定义经           *)
(*   plus_zero 归约；抽象核 uabp7we_abs_row_eps_absK 由 abs_mult、非负定位       *)
(*   前提 abs_ge_zero_req 与逐 eps 三角前提 abs_sum_le_eps_h 经 sum_ext 与        *)
(*   req_plus_compat、le_id_r 装配；rsq 核逐点非负由 rsq_u_r_nonneg 出节形直连。 *)
(*                                                              *)
(* Section 前提的地位：sum_ext、abs_sum_le_eps_h、abs_ge_zero_req、K_nonneg      *)
(*   均为 Section 内假设（出节后量化为定理前提），非全局公理；其中                *)
(*   abs_sum_le_eps_h 即逐 eps 三角不等式本身，作为本件重建的目标前提引入。       *)
(*                                                              *)
(* 构造性注记：全件语句集合值面；零承认、零经典逻辑捷径、零排中律；              *)
(*   见证以依存对承载；文尾对逐件 Print Assumptions 审计封闭。                   *)
(*                                                              *)
(* 编译配方：Rocq 9.1 直调、cpu_guard 节流、-o 临时目录输出（树内零写入）。      *)
(*                                                              *)
(* 标识符约定：本件实例层命名以前缀 uabp7we_ 区分于库内 rsq_/csm_ 系列。         *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Import RealInterfaceEnhancedMod.

(* ============ 二元变号载体上的逐 eps 实例面 ============ *)

(* 变号载体族：两点 bool 载体，系数 a 与 −b（a,b>0 的证明另附），
   正负两支各占一点——使三角不等式在变号系数下取实质形。 *)
Definition uabp7we_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 二元约简：折叠在二点清单上定义性归约为逐点加法（req 链两段：
   折叠的内部自归约 + 右端零消去） *)
Lemma uabp7we_sumd_twopt : forall g : bool -> Real,
  req (sumd_list_sum bool g (true :: false :: nil))
      (plus (g true) (g false)).
Proof.
  intro g.
  exact (req_trans
           (sumd_list_sum bool g (true :: false :: nil))
           (plus (g true) (plus (g false) zero))
           (plus (g true) (g false))
           (req_refl (plus (g true) (plus (g false) zero)))
           (req_plus_compat (g true) (g true)
              (plus (g false) zero) (g false)
              (req_refl (g true))
              (plus_zero (g false)))).
Qed.

(* 主例：二元变号载体上 |Σf| ≤ Σ|f| + eps（逐 eps 形）。
   由库件 csm_abs_sum_le_eps（UpReqConcSoftmax）直接实例化，
   二元载体为其具体实例。 *)
Lemma uabp7we_csm_eps_twopt : forall a b eps : Real,
  lt zero a -> lt zero b -> lt zero eps ->
  le (abs (csm_sumf bool (true :: false :: nil) (uabp7we_mixed_f a b)))
     (plus (csm_sumf bool (true :: false :: nil)
              (fun s : bool => abs (uabp7we_mixed_f a b s)))
           eps).
Proof.
  intros a b eps Ha Hb Heps.
  exact (csm_abs_sum_le_eps bool (true :: false :: nil)
           (uabp7we_mixed_f a b) eps Heps).
Qed.

(* 符号合取：正支在 true 点定义性等于 a（正），负支在 false 点定义性
   等于 −b，由 b>0 经 opp_lt_compat 反号保序得负——变号载体上
   两支符号在此逐点确定。两个见证以 sigT 依存对承载
   （Set 值面的合取不走 Prop 连接子，配对走依存对） *)
Lemma uabp7we_twopt_mixed_sign : forall a b : Real,
  lt zero a -> lt zero b ->
  sigT (fun _ : lt zero (uabp7we_mixed_f a b true) =>
        lt (uabp7we_mixed_f a b false) zero).
Proof.
  intros a b Ha Hb.
  exact (existT _
           Ha
           (req_lt_id_r_loc (opp b) (opp zero) zero
              (req_trans (opp zero) (plus zero (opp zero)) zero
                 (req_sym (plus zero (opp zero)) (opp zero)
                    (req_plus_zero_l (opp zero)))
                 (plus_opp zero))
              (opp_lt_compat zero b Hb))).
Qed.

(* ============ 行加权和不等式的逐 eps 形重建 ============ *)

(* 抽象核：任意逐点非负核 K 上，行不等式（与 rsq_u_abs_row 同形）
   的逐 eps 形——求和三角前提取逐 eps 形（以 abs_sum_le_eps_h
   替代不带余量形 abs_sum_le_h），结论右端加 eps 余量。 *)
Section WallEpsRowAbs.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* 求和外延前提（与 rsq 同位） *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).

(* 逐 eps 三角前提：abs_sum_le_h 的 Bishop 逐 eps 形同位替换 *)
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).

(* 逐点非负核 K（与 rsq 核非负前提同形） *)
Variable K : S -> S -> R.
Hypothesis K_nonneg : forall s s' : S, le zero (K s s').

(* 绝对值非负定位前提（le zero a ⟹ abs a = a，与 rsq 同位） *)
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* 行不等式的逐 eps 重建（与 rsq_u_abs_row 同形）：
   右端多 eps 余量；证明链 = 乘积绝对值分解（abs_mult 与非负定位）经
   sum_ext 加法外延换元与 req_plus_compat，末端由逐 eps 三角前提给出。 *)
Theorem uabp7we_abs_row_eps_absK : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (K s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (le_id_r
           (abs (sumf (fun s : S => mult (f s) (K s s'))))
           (plus (sumf (fun s : S => abs (mult (f s) (K s s')))) eps)
           (plus (sumf (fun s : S => mult (abs (f s)) (K s s'))) eps)
           (req_plus_compat
              (sumf (fun s : S => abs (mult (f s) (K s s'))))
              (sumf (fun s : S => mult (abs (f s)) (K s s')))
              eps eps
              (sum_ext
                 (fun s : S => abs (mult (f s) (K s s')))
                 (fun s : S => mult (abs (f s)) (K s s'))
                 (fun s : S =>
                    req_trans
                      (abs (mult (f s) (K s s')))
                      (mult (abs (f s)) (abs (K s s')))
                      (mult (abs (f s)) (K s s'))
                      (abs_mult (f s) (K s s'))
                      (req_mult_compat (abs (f s)) (abs (f s))
                         (abs (K s s')) (K s s')
                         (req_refl (abs (f s)))
                         (abs_ge_zero_req (K s s') (K_nonneg s s')))))
              (req_refl eps))
           (abs_sum_le_eps_h (fun s : S => mult (f s) (K s s')) eps Heps)).
Qed.

End WallEpsRowAbs.

(* rsq 核实例节：以库件 rsq_u_r_kernel 的最小前提集实例化抽象核
   （rsq_u_r_nonneg 的出节签名即所需全部前提） *)
Section WallEpsRowRsq.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable u : S -> R.
Variable delta : R.
Variable delta_lt_one : lt delta one.
Variable transition : S -> S -> R.
Variable minorization : forall s s' : S, le (mult delta (u s')) (transition s s').
Variable lpc : forall a b c d : R,
  lt a b -> le c d -> lt (plus a c) (plus b d).

Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* rsq 核同形定义（库件直连，无需重证） *)
Definition uabp7we_rkern (s s' : S) : R :=
  rsq_u_r_kernel S u delta delta_lt_one transition lpc s s'.

(* 核逐点非负：直接应用库件出节形（实参 R RIS S u delta
   delta_lt_one transition minorization lpc s s' 全显给出） *)
Lemma uabp7we_rkern_nonneg : forall s s' : S, le zero (uabp7we_rkern s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg R RIS S u delta delta_lt_one transition
           minorization lpc s s').
Qed.

(* 主定理：行不等式（rsq_u_abs_row）的逐 eps 形重建——
   抽象核以 K:=rsq 核全参实例化；rsq_u_abs_row 正是
   cmk_attention_mixing_time 链中该行不等式的库内原型（经 rsq 链继承） *)
Theorem uabp7we_abs_row_eps : forall (f : S -> R) (s' : S) (eps : R),
  lt zero eps ->
  le (abs (sumf (fun s : S => mult (f s) (uabp7we_rkern s s'))))
     (plus (sumf (fun s : S => mult (abs (f s)) (uabp7we_rkern s s'))) eps).
Proof.
  intros f s' eps Heps.
  exact (@uabp7we_abs_row_eps_absK R RIS S sumf sum_ext abs_sum_le_eps_h
           uabp7we_rkern uabp7we_rkern_nonneg abs_ge_zero_req f s' eps Heps).
Qed.

End WallEpsRowRsq.

(* ============ 假设审计（对逐件 Print Assumptions） ============ *)
Print Assumptions uabp7we_sumd_twopt.
Print Assumptions uabp7we_csm_eps_twopt.
Print Assumptions uabp7we_twopt_mixed_sign.
Print Assumptions uabp7we_abs_row_eps_absK.
Print Assumptions uabp7we_rkern_nonneg.
Print Assumptions uabp7we_abs_row_eps.
