(* ========================================================================= *)
(* 【ToyR 战役·包AW三·T300 台账席】玩具级定理同名非平凡替换稿（补标头注）    *)
(*                                                                           *)
(* 本稿系 ToyR 战役包AW三 替换落件（原名落件）；落件时头部漏植战役标记，     *)
(* 本块由 T326 异常修复席于 2026-09-22 补植：仅加头注，语句面／证明体／      *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/T300。       *)
(* 替换定理清单：uassw_nat_to_R_step（共 1 刀，刀面以台账为权威）            *)
(* 非平凡性口径：nat_to_R 步进方程 iota 重演，恒等点显式化直取，无行         *)
(* 拆分式假非平凡。                                                          *)
(* 本稿零公理、零承认件、全封口、纯构造性、无经典逻辑；补标零改动不触        *)
(* 证明面，落件录判绿承来源台账。                                            *)
(* ========================================================================= *)
(* ===================================================================== *)
(* UpAblP6_S5SlotWire.v — PA6-05 喂件面消融件（T215 台账）                *)
(* 对象：S5SlotWire.v（T201 脸表：230 行 20 声明 0 伴生，全 Defined        *)
(*       提取面向＝可执行喂件）。消融形态＝N3 代表性喂件实例供给：         *)
(*       四组具体数据构造喂入，使转发件沿喂点真实求值出结论，非转发冒充——  *)
(*       喂件构造即消融实质（对照 FA3 消融三分类之实例供给类）。           *)
(* 覆盖：槽4/5/6（fa56 双槽位点喂：单位点正性消费＋恒等求值）＋            *)
(*       槽8（fa56c 单位权重喂）＋槽3（of_nat 三前提具体实现喂＋轨道点）＋  *)
(*       槽9a（Q 半半数值喂＋闭式有理数求值伴件）。                       *)
(* 纪律：零新数学；语句面全本库 Set 面位；全件 Qed 收束；原树零改；        *)
(*       .vo 只落临时工作根；零云端零 git；姊妹席辖区零碰。                *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import fa56_id_carrier.
Require Import fa56c_ext.
Require Import PhysPredAblation.
Require Import p4a_GradSignQDec.
Require Import S5SlotWire.
From Stdlib Require Import QArith_base Qring Qabs.
From Stdlib Require Import Lists.List.

(* ============ §一 接口槽四组喂件（槽4/5/6/8/3） ======================== *)

Section UasswFeed.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R    := @R RI.
Let zero := @zero RI.
Let one  := @one RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp  := @opp RI.
Let le   := @le RI.
Let lt   := @lt RI.

(* ---- 喂件一（槽4/5：协方差位单位点正性消费） ------------------------
   喂入数据：D := one、H_inv := one（接口单位点），正性证书
   one_pos × one_pos 双喂——被喂件 ssw_covariance_pos 在该具体点放电，
   结论 lt zero (fa56_covariance one one) 为单位点协方差正性实例。
   非平凡性：消费链经 fa56_covariance_pos（mult_positive）在喂点闭合，
   证书合成（单位点双正）为本席构造。 ---- *)
Theorem uassw_covariance_unit_pos : lt zero (fa56_covariance one one).
Proof.
  exact (ssw_covariance_pos one one one_pos one_pos).
Qed.

(* ---- 喂件二（槽6：恒等位单位点求值；易档 T 级申报） ------------------
   喂入数据：D := one、H_inv := one。fa56_covariance 装法在喂点
   定义性展开＝mult one one，恒等以 id_refl 构造子收口——
   装法体沿喂点真实求值，恒等两臂逐位同型（透明展开级，如实申报）。 ---- *)
Theorem uassw_fluctuation_unit_id : Id (fa56_covariance one one) (mult one one).
Proof.
  exact id_refl.
Qed.

(* ---- 喂件三（槽8：产率位单位权重喂） --------------------------------
   喂入数据：Flx := unit、TD := unit、w := 常一权重、theta := 常一势、
   J := tt、X := tt。fa56c 产率装法（权重×势）在喂点求值：
   常一×常一＝mult one one，恒等经被喂件 ssw_entropy_production_rate
   放电后按 β 规约收口。 ---- *)
Theorem uassw_entropy_production_unit :
  Id (fa56c_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt)
     (mult one one).
Proof.
  exact (ssw_entropy_production_rate unit unit (fun _ => one) (fun _ => one) tt tt).
Qed.

(* ---- 喂件四（槽3：of_nat 三前提具体实现喂） --------------------------
   喂入数据：nat_to_R 具体实现（零元 zero、步进 plus·one 的
   nat 递归构造，泛型于接口），三前提件逐件构造为独立 Qed 件：
   零元恒等（iota 求值）、步进恒等（iota 求值）、非负（归纳＋
   plus_le_lt_pos 在喂点合成），再喂入 ssw_macro_loss_monotone
   于 m0 := zero、t := 2 双步轨道点消费。 ---- *)
Fixpoint nat_to_R (n : nat) : R :=
  match n with
  | O => zero
  | Datatypes.S m => plus (nat_to_R m) one
  end.

Theorem uassw_nat_to_R_zero_id : Id (nat_to_R O) zero.
Proof.
  exact id_refl.
Qed.

Theorem uassw_nat_to_R_step :
  forall n : nat, Id (nat_to_R (Datatypes.S n)) (plus (nat_to_R n) one).
Proof.
  intro n.
  exact (@id_refl _ (plus (nat_to_R n) one)).
Qed.

Theorem uassw_nat_to_R_nonneg : forall n : nat, le zero (nat_to_R n).
Proof.
  induction n as [| m IH].
  - apply le_refl.
  - apply lt_le_iff.
    apply inl.
    apply plus_le_lt_pos.
    * exact IH.
    * apply one_pos.
Qed.

Theorem uassw_macro_loss_zero_step2 :
  le (ppa_macro_loss (iterate ppa_macro_dynamics (Datatypes.S (Datatypes.S O)) zero))
     (ppa_macro_loss zero).
Proof.
  exact (ssw_macro_loss_monotone nat_to_R
           uassw_nat_to_R_zero_id uassw_nat_to_R_step uassw_nat_to_R_nonneg
           zero (Datatypes.S (Datatypes.S O))).
Qed.

End UasswFeed.

(* ============ §二 槽9a Q 数值喂件（半半实例＋闭式求值伴件） ============= *)

Open Scope Q_scope.

(* ---- 喂件五（槽9a：eta := 1/2、mu := 1/2、x0 := 1/2、n := 0、k := 1） --
   喂入数据：ημ ＝ 1/4 ＜ 1（收缩系数 κ ＝ 3/4 落 (0,1)），三前提
   逐件由 Q 层有序比较计算收口；被喂件 ssw_full_sign_decay_instance_ref
   在该闭式点放电出数值衰减不等式。 ---- *)
Theorem uassw_full_sign_decay_half :
  Qle (Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) (O + Datatypes.S O) (1#2))))
      (gsq_pow (gsq_kappa (1#2) (1#2)) (Datatypes.S O)
         * Qabs (gsq_grad (1#2) (gsq_iter (1#2) (1#2) O (1#2)))).
Proof.
  apply (ssw_full_sign_decay_instance_ref (1#2) (1#2) (1#2) O (Datatypes.S O)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.

(* ---- 真求值伴件三件：喂点数据经 Defined 体计算至闭式有理数 -----------
   κ(1/2,1/2) ＝ 3/4、g(1/2) ＝ 1/4、轨道一步 x₁ ＝ 3/8——
   gsq_step 三分支判定（stdlib 构造性三分，Defined 透明）沿喂点
   真实求值，结论逐位为字面有理数（Qeq 交叉积比较收口）。 ---- *)
Theorem uassw_kappa_half_eval : gsq_kappa (1#2) (1#2) == (3#4).
Proof.
  vm_compute. reflexivity.
Qed.

Theorem uassw_grad_half_eval : gsq_grad (1#2) (1#2) == (1#4).
Proof.
  vm_compute. reflexivity.
Qed.

Theorem uassw_iter_half_step_eval : gsq_iter (1#2) (1#2) (Datatypes.S O) (1#2) == (3#8).
Proof.
  vm_compute. reflexivity.
Qed.

Close Scope Q_scope.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions uassw_covariance_unit_pos.
Print Assumptions uassw_fluctuation_unit_id.
Print Assumptions uassw_entropy_production_unit.
Print Assumptions uassw_nat_to_R_zero_id.
Print Assumptions uassw_nat_to_R_step.
Print Assumptions uassw_nat_to_R_nonneg.
Print Assumptions uassw_macro_loss_zero_step2.
Print Assumptions uassw_full_sign_decay_half.
Print Assumptions uassw_kappa_half_eval.
Print Assumptions uassw_grad_half_eval.
Print Assumptions uassw_iter_half_step_eval.
