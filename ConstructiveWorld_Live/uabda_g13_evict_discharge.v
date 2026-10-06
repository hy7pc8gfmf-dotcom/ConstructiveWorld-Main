(* ==========================================================================
   uabda_g13_evict_discharge.v — G13_EvictFam 逐出族接口假设面的消解形对拍件
   数学使命：对 G13_EvictFam.v 四处接口假设（Id 层 :57 Z_thermo_pos、
   :83 evicted_partition_pos；req 层 :474 Z_thermo_pos、:503
   evicted_partition_pos）给出实例世界消解形——Id 层单点世界使用
   供给库件 :130/:141 行二件，req 层两点世界使用其 :285 行件；req 层
   逐出配分正性为无条件闭合新构造（在库仅有需求和保正前提的条件形
   的条件形一件与 Id 层 :141 行件，本件世界形缺位）。
   依赖清单：S01_BaseRing、G13_EvictFam、G13 配套库件（全部只读）。
   对标行：G13_EvictFam.v:57/:83/:474/:503；供给库件消解三件
   （:130／:141／:285）；S06_DiffSamplingGibbs.v:3826 Z_thermo_pos 同构样板
   （逐点 exp_neg_pos ＋ 求和保正接口实例化）。
   构造性注记：全件 Qed 闭合、零承认式声明、零经典逻辑；语句面全 Set 层
   零 Prop 泄露；uabda_g13_evpart_req 证明体为两点正和显式构造
   （plus_positive ＋ exp_neg_pos×2），非转发件。
   编译配方：coqc -q -native-compiler no -Q <主vo树> "" -Q . "" 本件
   （cpu_guard -TempLimit 98 包裹；COQLIB/ROCQLIB 全字面导出）。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import G13_EvictFam.
Require Import UpAblT13c_G13.

(* ---- 一、Id 层：:57 消解形（单点世界，求和退化为因子行） ---- *)

Theorem uabda_g13_zpos_id :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : @lt RI (@zero RI) D)
         (energy : @S RI uab_ssUnit -> @R RI),
    @lt RI (@zero RI)
      (@evict_Z_thermo RI uab_ssUnit uab_soUnit D D_pos energy).
Proof.
  intros RI D D_pos energy.
  exact (uabT13c_evict61 D D_pos energy).
Qed.

(* ---- 二、Id 层：:83 消解形（单点世界，全保留判定供入） ---- *)

Theorem uabda_g13_evpart_id :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : @lt RI (@zero RI) D)
         (energy : @S RI uab_ssUnit -> @R RI),
    @lt RI (@zero RI)
      (@evict_evicted_partition RI uab_ssUnit uab_soUnit D D_pos energy
         (fun _ : @S RI uab_ssUnit => unit)
         (fun _ : @S RI uab_ssUnit => inl tt : Or unit (Not unit))).
Proof.
  intros RI D D_pos energy.
  exact (uabT13c_evict87 D D_pos energy).
Qed.

Import RealInterfaceEnhancedMod.

(* ---- 三、req 层：两点世界（{R}{RIS} 全参） ---- *)

Section UabdaG13Req.

Context {R : Set}.
Context {RIS : RealInterfaceEnhancedSetoid R}.

Let zero := @zero R RIS.
Let one := @one R RIS.
Let plus := @plus R RIS.
Let mult := @mult R RIS.
Let lt := @lt R RIS.
Let inv_pos := @inv_pos R RIS.
Let exp_neg := @exp_neg R RIS.

(* :474 消解形——两点世界（uab_t2sum），使用在库配套件（:285 行） *)
Theorem uabda_g13_zpos_req (D : R) (D_pos : lt zero D) (energy : bool -> R) :
  lt zero (@evq_Z_thermo R RIS bool uab_t2sum D D_pos energy).
Proof.
  exact (uabT13c_evq_Zpos2 D D_pos energy).
Qed.

(* :503 消解形——两点世界全保留判定，无条件闭合（显式两点正和构造）：
   保留判定恒取左支后逐项正性由 exp_neg_pos 给出，两项和的正性由
   plus_positive 合成；与 S06 Z_thermo_pos 同构（逐点正＋求和保正
   实例化，实例化在本世界由两点载体承载）。 *)
Theorem uabda_g13_evpart_req (D : R) (D_pos : lt zero D) (energy : bool -> R) :
  lt zero (@evq_evicted_partition R RIS bool uab_t2sum D D_pos energy
             (fun _ : bool => unit)
             (fun _ : bool => inl tt : Or unit (Not unit))).
Proof.
  unfold evq_evicted_partition, uab_t2sum, evq_boltzmann_factor.
  exact (plus_positive
           (exp_neg (mult (inv_pos D D_pos) (energy true)))
           (exp_neg (mult (inv_pos D D_pos) (energy false)))
           (exp_neg_pos (mult (inv_pos D D_pos) (energy true)))
           (exp_neg_pos (mult (inv_pos D D_pos) (energy false)))).
Qed.

End UabdaG13Req.

(* ---- 逐件前提面审计（Closed 判据） ---- *)

Print Assumptions uabda_g13_zpos_id.
Print Assumptions uabda_g13_evpart_id.
Print Assumptions uabda_g13_zpos_req.
Print Assumptions uabda_g13_evpart_req.
