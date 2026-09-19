(* ============================================================ *)
(* UpAblP7_WallEps_CSM.v —— 论文7 专项消融战役 席 PA7-11（墙件 eps 甲腿 W1） *)
(*                                                              *)
(* 假设任务：目标⑤ 墙件 eps/B 形消费件战役——abs_sum_le 墙槽侧。        *)
(*   墙：abs_sum_le plain 形（|Σf|≤Σ|f|，Or 编码 le）对混合号 f 等价    *)
(*   真墙（UpReqConcSoftmax.v L11-16 定谳注记；real_le = Or real_lt     *)
(*   real_eq，S02 L469，混合号下两支均不可达）。本席不施工墙本体，       *)
(*   供墙槽的 Bishop 逐 eps 形消费件。                                  *)
(*                                                              *)
(* 母本坐标（文件:行号）→ 放电件 → 消费位：                            *)
(*   UpReqConcSoftmax.v:248 csm_abs_sum_le_eps（逐 eps 三角直供）       *)
(*     → uabp7we_csm_eps_twopt（二元混合号载体实例消费）                *)
(*   UpReqSampling.v:116/488 abs_sum_le_h 槽与唯一深消费位 rsq_u_abs_row *)
(*     → uabp7we_abs_row_eps_absK / uabp7we_abs_row_eps（eps 形重建）   *)
(*   UpReqSampling.v:1166 经 rsq_bounded_softmax_tv_iter 向上；         *)
(*   UpReqConcMixSel.v:880/911 cmk_attention_mixing_time/_le 为墙槽     *)
(*   消费末端（经 rsq 链继承，本件在链根重建 eps 形）。                 *)
(*                                                              *)
(* 分级申报：                                                          *)
(*   N1 库内放电件直连：csm_abs_sum_le_eps（指定消费路线）、            *)
(*     rsq_u_r_kernel / rsq_u_r_nonneg（出节签名实测不含 plain 墙槽——  *)
(*     墙槽未被其证明消费、未泛化，消费诚实）、abs_mult、le_id_r、      *)
(*     req_plus_compat、req_mult_compat、opp_lt_compat、reqd_opp_zero、 *)
(*     req_lt_id_r_loc、plus_zero。                                    *)
(*   N2 已证导出：uabp7we_abs_row_eps 由抽象核 uabp7we_abs_row_eps_absK *)
(*     全参实例化（K:=rsq 核），链路零 plain 形冒充。                   *)
(*   N3 实例供给：二元 bool 载体（enum:=true::false::nil 清单供给），   *)
(*     系数 a、−b 带正性证书（有界系数面），混合号锚逐点定谳。         *)
(*                                                              *)
(* 依赖清单（只读消费，原树零改）：CW_ConstructiveWorld_219、           *)
(*   UpReqAlgebra、UpReqSumD、UpReqConcSoftmax、UpReqSampling；         *)
(*   实例面 = S07 具体实例（模块导入后类型类解析，与母件同源同解析）。  *)
(*                                                              *)
(* 红线自审：全件语句集合值面；全件真证收口；无承认件、无未证断言、     *)
(*   无经典逻辑捷径、无选择公理、无排中律；文尾逐件假设审计全封闭。     *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Import RealInterfaceEnhancedMod.

(* ============ 甲件：二元混合号载体的逐 eps 实例面 ============ *)

(* 混合号载体族：两点 bool 载体，系数 a 与 −b（a,b>0 证书另附），
   正负两支各占一点——plain 墙的典型混合号形状。 *)
Definition uabp7we_mixed_f (a b : Real) : bool -> Real :=
  fun s : bool => if s then a else opp b.

(* 二元约简：折叠处方在二点清单上定义性归约为逐点加法（req 链两段：
   折叠自归约中段 + 右零消去） *)
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

(* 甲件主例：二元混合号载体上 |Σf| ≤ Σ|f| + eps（逐 eps 形）。
   消费路线申报：直接消费 csm_abs_sum_le_eps（UpReqConcSoftmax.v:248，
   指定免费档），二元载体为其实例化。 *)
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

(* 混合号锚：正支在 true 点定义性等于 a（正），负支在 false 点定义性
   等于 −b，由 b>0 经反号保序得负——plain 墙注记中的混合号形状在此
   载体上逐点定谳（req 反号右定位换形）。语句集合值，两证以 sigT 打包
   （宇宙坑先例：合取连接子仅 Prop 层，Set 值证配对走依存对） *)
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

(* ============ 乙件：墙槽消费定理的逐 eps 形重建 ============ *)

(* 抽象核：任意逐点非负核 K 上，墙槽消费定理（rsq_u_abs_row 同形）
   的逐 eps 形——求和三角槽取逐 eps 形（替代 plain 墙槽 abs_sum_le_h，
   零 plain 形冒充），结论右端加 eps 余量。 *)
Section WallEpsRowAbs.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

Variable S : Set.
Variable sumf : (S -> R) -> R.

(* 求和外延槽（rsq 同位） *)
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).

(* 逐 eps 三角槽：plain 墙槽 abs_sum_le_h 的 Bishop 逐 eps 形同位替换 *)
Hypothesis abs_sum_le_eps_h :
  forall (f : S -> R) (eps : R), lt zero eps ->
    le (abs (sumf f)) (plus (sumf (fun s : S => abs (f s))) eps).

(* 逐点非负核（rsq 核非负位同形） *)
Variable K : S -> S -> R.
Hypothesis K_nonneg : forall s s' : S, le zero (K s s').

(* 绝对值非负定位证书（rsq 同位诚实假设面） *)
Hypothesis abs_ge_zero_req : forall a : R, le zero a -> req (abs a) a.

(* 墙槽消费定理逐 eps 重建（rsq_u_abs_row 同形，UpReqSampling.v:483-489）：
   右端多 eps 余量；证明链 = 乘积绝对值分解链（abs_mult+非负定位）经
   加法同余抬升 + 逐 eps 三角槽直喂。 *)
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

(* rsq 核证书面：镜像 ReqUContraction 核最小证书集（出节签名实测——
   rsq_u_r_nonneg 出口不含 plain 墙槽，消费诚实） *)
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

(* rsq 核同形定义（库件直连，零重证） *)
Definition uabp7we_rkern (s s' : S) : R :=
  rsq_u_r_kernel S u delta delta_lt_one transition lpc s s'.

(* 核逐点非负：消费库件出节形（签名探针实测：R RIS S u delta
   delta_lt_one transition minorization lpc s s' 十一位全显） *)
Lemma uabp7we_rkern_nonneg : forall s s' : S, le zero (uabp7we_rkern s s').
Proof.
  intros s s'.
  exact (@rsq_u_r_nonneg R RIS S u delta delta_lt_one transition
           minorization lpc s s').
Qed.

(* 乙件主定理：墙槽消费定理（rsq_u_abs_row）的逐 eps 形重建——
   消费抽象核全参实例化（K:=rsq 核），链根即 cmk_attention_mixing_time
   链的墙槽唯一深消费位（UpReqConcMixSel.v:880/911 经 rsq 链继承） *)
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

(* ============ 审计收尾段（逐件封闭判读，节外全显） ============ *)
Print Assumptions uabp7we_sumd_twopt.
Print Assumptions uabp7we_csm_eps_twopt.
Print Assumptions uabp7we_twopt_mixed_sign.
Print Assumptions uabp7we_abs_row_eps_absK.
Print Assumptions uabp7we_rkern_nonneg.
Print Assumptions uabp7we_abs_row_eps.
