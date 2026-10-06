(* ==========================================================================
   uabda_up01_discharge.v — Arch_Up_01 接口假设面的消解形对拍件
   数学使命：对 Arch_Up_01.v AlignIdWorld 节三处接口假设（:478 Z_align_pos、
   :481-482 与 :786-787 sum_over_S_pos）给出消解形——逐口使用在库供给定理
   abl_tail_supply_70（tsp_up01_* 四件）机械对拍，验证供给-槽逐字对位；
   UpDpoSensMain 节 :1867-1868 为不透明自由参数的裸正性前提，无闭式可展开，
   保持接口前提身份（abl_tail_supply_70.v 头注同判）。
   依赖清单：S01_BaseRing、S05_AlignmentGRPO、G13 配套库件、
   abl_tail_supply_70（全部只读；既有件零字节不动）。
   对标行：Arch_Up_01.v:478／:481-482／:786-787／:1867-1868；
   供给定理＝tsp_up01_Z_align_pos_slot（abl_tail_supply_70.v:115）／
   tsp_up01_align_sum_over_S_pos（:145）／tsp_up01_fwloop_sum_over_S_pos（:155）／
   tsp_up01_Z_align_pos_unit_world（:167）。
   构造性注记：全件 Qed 闭合、零承认式声明、零经典逻辑；语句面全 Set 层
   （lt 为 Set 值序谓词、Id 型为 S01:73 恒等型，零 Prop 泄露）；逐件
   Print Assumptions 取 Closed 判据。
   编译配方：coqc -q -native-compiler no -Q <主vo树> "" -Q . "" 本件
   （cpu_guard -TempLimit 98 包裹；COQLIB/ROCQLIB 全字面导出）。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S05_AlignmentGRPO.
Require Import UpAblT13c_G13.
Require Import abl_tail_supply_70.

(* ---- 一、AlignIdWorld 节环境（Arch_Up_01.v:455-482 同序同形） ----
   消解判读：Z_align 正性由同节 sum_over_S_pos 前提与在库条件形
   tsp_up01_Z_align_pos_slot 闭合——接口假设面由两前提减为一份。 *)

Section UabdaUp01Align.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.
Local Existing Instance RI_base.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @zero RI.
Let plus := @plus RI.
Let mult := @mult RI.
Let opp := @opp RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable reward : S -> R.          (* 奖励函数 r(s) *)
Variable beta : R.                 (* KL 正则化温度 β > 0 *)
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.          (* 参考策略 *)
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable sum_over_S_pos : forall (f : S -> R),
  (forall s : S, lt zero (f s)) -> lt zero (sum_over_S f).

(* :478 的消解形——前提面不再含 Z_align_pos 本假设 *)
Theorem uabda_up01_zalign_pos :
  lt zero (Z_align reward beta beta_pos pi_ref).
Proof.
  exact (tsp_up01_Z_align_pos_slot reward beta beta_pos pi_ref pi_ref_pos
           sum_over_S_pos).
Qed.

End UabdaUp01Align.

(* ---- 二、:481-482 槽实例面闭形对拍（单点状态空间世界） ----
   抽象 SumOver 类无严格正字段，一般层保持假设身份；单点世界读法
   （SS := uab_ssUnit、SO := uab_soUnit）下闭形在库，本件逐字对拍。 *)

Theorem uabda_up01_align_sum_pos :
  forall {RI : RealInterfaceEnhanced} (f : @S RI uab_ssUnit -> @R RI),
    (forall s : @S RI uab_ssUnit, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (@sum_over_S RI uab_ssUnit uab_soUnit f).
Proof.
  intros RI f H.
  exact (@tsp_up01_align_sum_over_S_pos RI f H).
Qed.

(* ---- 三、:786-787 槽同形对拍（单点世界读法） ---- *)

Theorem uabda_up01_fwloop_sum_pos :
  forall {RI : RealInterfaceEnhanced} (f : @S RI uab_ssUnit -> @R RI),
    (forall s : @S RI uab_ssUnit, @lt RI (@zero RI) (f s)) ->
    @lt RI (@zero RI) (@sum_over_S RI uab_ssUnit uab_soUnit f).
Proof.
  intros RI f H.
  exact (@tsp_up01_fwloop_sum_over_S_pos RI f H).
Qed.

(* ---- 四、:478 出节全参闭形（单点世界读法，无条件） ---- *)

Theorem uabda_up01_zalign_unit_world :
  forall {RI : RealInterfaceEnhanced}
         (reward : @S RI uab_ssUnit -> @R RI) (beta : @R RI)
         (beta_pos : @lt RI (@zero RI) beta)
         (pi_ref : @S RI uab_ssUnit -> @R RI)
         (pi_ref_pos : forall s : @S RI uab_ssUnit,
                         @lt RI (@zero RI) (pi_ref s)),
    @lt RI (@zero RI)
      (@Z_align RI uab_ssUnit uab_soUnit reward beta beta_pos pi_ref).
Proof.
  intros RI reward beta beta_pos pi_ref pi_ref_pos.
  exact (@tsp_up01_Z_align_pos_unit_world RI reward beta beta_pos pi_ref
           pi_ref_pos).
Qed.

(* ---- 逐件前提面审计（Closed 判据） ---- *)

Print Assumptions uabda_up01_zalign_pos.
Print Assumptions uabda_up01_align_sum_pos.
Print Assumptions uabda_up01_fwloop_sum_pos.
Print Assumptions uabda_up01_zalign_unit_world.
