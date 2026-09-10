(* ============================================================ *)
(* UpReqBoltzDirect.v —— 定理级签名迁移首批执行席：               *)
(*   boltzmann_factor_pos 的【具体构造重证】                      *)
(*                                                              *)
(* 使命：接口转发版 PropositionConvergenceCore.boltzmann_factor_pos *)
(*   （出口形 forall {RI : RealInterfaceEnhanced} {SS : StateSpace RI} *)
(*   (D : R) (HD : lt zero D) (L : S -> R) (s : S), lt zero (...)，  *)
(*   证明体 3 步 unfold+intros+apply exp_neg_pos）是接口转发，非     *)
(*   独立证明。本件不经接口参数，直接在 Cauchy Real 构造层          *)
(*   （real_eq 逐 eps 层）重证 Boltzmann 因子正性，引擎直落 CW219   *)
(*   B3 具体构造 cauchy_real_exp_pos（Real 层无条件、零假设）。      *)
(*   本件 Closed 无接口参数 = 定理级签名迁移首批完成的机器证据。    *)
(*                                                              *)
(* 语句面对齐（sed/Check 实证，20260910）：                        *)
(*   @PropositionConvergenceCore.boltzmann_factor_pos              *)
(*    : forall (RI : RealInterfaceEnhanced) (SS : StateSpace RI)   *)
(*        (D : @R RI), lt zero D -> (S -> R) -> S -> R -> lt zero … *)
(*   节参 {RI}{SS} 剪除 + 载体落 nat（S := nat 具体化）+ 字段替换    *)
(*   （lt:=real_lt, zero:=real_zero, exp_neg:=real_exp_neg,         *)
(*     mult:=real_mult, inv_pos:=real_inv_pos）后即本件主件语句。    *)
(*                                                              *)
(* 逐件分级表：                                                    *)
(*  主件 A  bzdir_boltzmann_factor_pos      —— 引擎 real_exp_neg_pos *)
(*           （Real 层包裹，D/HD/L/s 全参，零其余前件）             *)
(*  主件 B  bzdir_boltzmann_factor_pos_cauchy —— 直落 cauchy_real_  *)
(*           exp_pos（CW219 B3 最终步引擎，unfold 到柯西构造层）    *)
(*  主件 C  bzdir_boltzmann_factor_one_pos  —— D := real_one 全具体 *)
(*           零前件版（real_lt_zero_one 直喂）                     *)
(*  辅件 1  bzdir_boltz_pos_of_engine / bzdir_engine_of_boltz_pos   *)
(*           —— Cauchy 正性→Boltzmann 正性双向直插桥（exact 恒等，  *)
(*           透明定义层 conversion 实证=零翻译直插机器证据）        *)
(*  辅件 2  bzdir_iface_conclusion_shape + bzdir_iface_shape_agree  *)
(*           —— 接口槽位结论形字段替换后的语句面对齐证书（refl）    *)
(*  辅件 3  bzdir_boltzmann_factor_pos_le —— lt→le 升格（inl 直喂） *)
(*  附加   bzdir_softmax_pos —— softmax_pos 同法重证（语句面分离： *)
(*           p := mult (inv Z HZ) (factor)，mult_positive×         *)
(*           inv_pos_pos×主件，对应 StochasticLanguageModel.softmax_pos *)
(*           与 boltzmann_prob_pos 的具体构造面）                  *)
(*                                                              *)
(* 勘误（对侦察预判，以 sed/Check 现值为准）：                      *)
(*  1. 侦察稿「current 陈述 forall {RI}」的精确形态实为节限定名：    *)
(*     Rocq 9 节保留命名空间，短名 boltzmann_factor_pos 不在顶层，  *)
(*     须写 PropositionConvergenceCore.boltzmann_factor_pos         *)
(*     （Locate 实证）；同库三处 boltzmann_factor 重名互掩，顶层     *)
(*     短名解析到 logits 版（StochasticLanguageModel 系）。          *)
(*  2. 接口层全实例落点（@PCC.boltzmann_factor_pos 具体实例喂定）    *)
(*     需 plain RealInterfaceEnhanced 实例；CW219 仅出              *)
(*     RealInterfaceEnhancedSetoid 实例 RealEnhancedReal（L41115）， *)
(*     故接口↔具体对齐以【字段替换语句面证书】（辅件 2）呈现，      *)
(*     不放大为全实例喂定。                                        *)
(*  3. 柯西正性引擎在 Real 层无条件（cauchy_real_exp_pos :          *)
(*     forall x, real_lt real_zero (cauchy_real_exp x)，Check 实证）， *)
(*     主件对 L 不加任何正性/有界前件——正性与损失函数符号无关，    *)
(*     为 e^{-x} 结构性正；此为重证相对接口版的诚实强度注记。       *)
(*                                                              *)
(* 红线：Set 层语句（real_lt/real_le 均 Set 值谓词，零 Prop 泄露）；  *)
(*   纯项式组装（exact/apply 供给项，零重写战术）；零外部未证假设，  *)
(*   尾部 Print Assumptions 全件 Closed（无 RI 泛化前件）；既有文件  *)
(*   零改；零 git。前缀台账：bzdir_ 全库 grep 零重名，文件名         *)
(*   UpReqBoltzDirect.v 全库零同名（双形并存，零既有文件改动）。     *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ============ 主定义：Boltzmann 因子的 Cauchy Real 具体构造 ============ *)
(* 字段替换：exp_neg := real_exp_neg，mult := real_mult，
   inv_pos := real_inv_pos（柯西倒数，正下界 eps0 保护）。载体 S := nat。 *)
Definition bzdir_boltzmann_factor (D : Real) (HD : real_lt real_zero D)
           (L : nat -> Real) (s : nat) : Real :=
  real_exp_neg (real_mult (real_inv_pos D HD) (L s)).

(* ============ 主件 A：正性（Real 层包裹引擎 real_exp_neg_pos） ============ *)
Theorem bzdir_boltzmann_factor_pos :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  unfold bzdir_boltzmann_factor.
  apply real_exp_neg_pos.
Qed.

(* ============ 主件 B：直落 CW219 B3 具体构造引擎 ============ *)
(* real_exp_neg x := cauchy_real_exp (real_opp x)（透明定义），
   引擎 cauchy_real_exp_pos 于 Real 层无条件（零假设）——
   重证深达柯西逐 eps 构造层，非接口字段转发。 *)
Theorem bzdir_boltzmann_factor_pos_cauchy :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  unfold bzdir_boltzmann_factor, real_exp_neg.
  apply cauchy_real_exp_pos.
Qed.

(* ============ 主件 C：全具体零前件版（D := real_one） ============ *)
Definition bzdir_boltzmann_factor_one (L : nat -> Real) (s : nat) : Real :=
  real_exp_neg (real_mult (real_inv_pos real_one real_lt_zero_one) (L s)).

Theorem bzdir_boltzmann_factor_one_pos :
  forall (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor_one L s).
Proof.
  intros L s.
  exact (bzdir_boltzmann_factor_pos real_one real_lt_zero_one L s).
Qed.

(* ============ 辅件 1：Cauchy Real 正性→Boltzmann 正性双向直插桥 ============ *)
(* 目标形与引擎形在透明定义层判定等价（bzdir_boltzmann_factor delta
   → real_exp_neg … delta → cauchy_real_exp (real_opp …)），
   故桥即恒等项：引擎结论【零翻译】直插 Boltzmann 槽位。 *)
Theorem bzdir_boltz_pos_of_engine :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (cauchy_real_exp (real_opp (real_mult (real_inv_pos D HD) (L s)))) ->
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s H.
  exact H.
Qed.

Theorem bzdir_engine_of_boltz_pos :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_boltzmann_factor D HD L s) ->
  real_lt real_zero (cauchy_real_exp (real_opp (real_mult (real_inv_pos D HD) (L s)))).
Proof.
  intros D HD L s H.
  exact H.
Qed.

(* ============ 辅件 2：接口槽位语句面对齐证书 ============ *)
(* 接口 PCC L1628 结论形 lt zero (exp_neg (mult (inv_pos D HD) (L s)))
   经字段替换（lt:=real_lt, zero:=real_zero, exp_neg:=real_exp_neg,
   mult:=real_mult, inv_pos:=real_inv_pos）后与本件主件语句
   判定等价（Set 层 eq，reflexivity 实证）。 *)
Definition bzdir_iface_conclusion_shape (D : Real) (HD : real_lt real_zero D)
           (L : nat -> Real) (s : nat) : Set :=
  real_lt real_zero (real_exp_neg (real_mult (real_inv_pos D HD) (L s))).

Lemma bzdir_iface_shape_agree :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  bzdir_iface_conclusion_shape D HD L s =
  real_lt real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  reflexivity.
Qed.

(* ============ 辅件 3：lt→le 升格（le 腿消费面直喂形） ============ *)
Theorem bzdir_boltzmann_factor_pos_le :
  forall (D : Real) (HD : real_lt real_zero D) (L : nat -> Real) (s : nat),
  real_le real_zero (bzdir_boltzmann_factor D HD L s).
Proof.
  intros D HD L s.
  exact (inl (bzdir_boltzmann_factor_pos D HD L s)).
Qed.

(* ============ 附加：softmax_pos 同法重证（语句面分离形） ============ *)
(* softmax 因子形：p := mult (inv Z HZ) (boltzmann 因子)。
   对应 StochasticLanguageModel.softmax_pos（exp_neg_pos × inv_pos_pos）
   与 PropositionConvergenceCore.boltzmann_prob_pos 的具体构造面。
   Z（配分和）以正性前提 HZ 携带（诚实边界：和的正性归 sum 引擎线）。 *)
Definition bzdir_softmax (D : Real) (HD : real_lt real_zero D)
           (Z : Real) (HZ : real_lt real_zero Z)
           (L : nat -> Real) (s : nat) : Real :=
  real_mult (real_inv_pos Z HZ) (bzdir_boltzmann_factor D HD L s).

Theorem bzdir_softmax_pos :
  forall (D : Real) (HD : real_lt real_zero D) (Z : Real) (HZ : real_lt real_zero Z)
         (L : nat -> Real) (s : nat),
  real_lt real_zero (bzdir_softmax D HD Z HZ L s).
Proof.
  intros D HD Z HZ L s.
  unfold bzdir_softmax.
  apply real_mult_positive.
  - apply real_inv_pos_pos.
  - apply bzdir_boltzmann_factor_pos.
Qed.

(* ============ 尾部四关之一：Print Assumptions（全件须 Closed） ============ *)
Print Assumptions bzdir_boltzmann_factor_pos.
Print Assumptions bzdir_boltzmann_factor_pos_cauchy.
Print Assumptions bzdir_boltzmann_factor_one_pos.
Print Assumptions bzdir_boltz_pos_of_engine.
Print Assumptions bzdir_engine_of_boltz_pos.
Print Assumptions bzdir_iface_shape_agree.
Print Assumptions bzdir_boltzmann_factor_pos_le.
Print Assumptions bzdir_softmax_pos.
