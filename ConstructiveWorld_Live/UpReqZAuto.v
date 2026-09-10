(* ============================================================ *)
(* UpReqZAuto.v —— Z_auto 引理席：配分相等前提「Z == partition」     *)
(*   的定义性消去（评审08 §3.3.1 点名弱点清偿）。                  *)
(*                                                                *)
(* 目标：把「Z_thermo == partition_function」从配分函数定理的前提    *)
(*   降为可自动消去的引理（Z_auto）：两分布在                       *)
(*   「energy == -z 逐点 + inv D == 1/T」下由定义性相等直接可导，    *)
(*   无需把它单列为前提。                                          *)
(*                                                                *)
(* 原件定位（sed 实读）：                                          *)
(*   · 原件 1：CW219 attention_is_gibbs_setoid（L66294），前提形：    *)
(*       req (inv_pos D D_pos) one ->                              *)
(*       (forall s, req (energy s) (opp (z s))) ->                  *)
(*       req (Z_thermo_setoid …) (partition_function_setoid z) ->   *)
(*       forall s, req (softmax_setoid z s) (boltzmann_dist_attn … s) *)
(*   · 原件 2：CW220 SigMigrate.req_attention_is_gibbs_temp          *)
(*       （L1954），前提 3 = req Z_thermo partition_function_temp。  *)
(*   两处求和载体均无 req 外延可消费（原件 1 的 sum_req_over_S_ext    *)
(*   Variable 未被定理消费故出节即弃；原件 2 节内只有 sum_pos）——     *)
(*   「前提可消而未消」的机制根因。本席把外延引擎显式接入，           *)
(*   Z_auto 即成立。                                               *)
(*                                                                *)
(* 外延引擎（实测签名）：                                          *)
(*   · Id 形：CW219 SumOver 字段                                    *)
(*       sum_over_S_ext : forall f g, (forall s, Id (f s) (g s)) -> *)
(*         Id (sum_over_S f) (sum_over_S g)                         *)
(*   · req 形：本文件各 Z_auto 件以显式参数 sum_req_ext / sumf_req_ext *)
(*     接入（诚实接口：对任何具体求和载体构造性满足，非分布层假设）。 *)
(*                                                                *)
(* exp 关系（实测）：exp_pos 即 exp_neg ∘ opp——两处上游均为透明       *)
(*   Definition（CW220 SigMigrate.exp_pos_fn / CW219 exp_pos_fn_setoid）， *)
(*   delta 换形后逐点镜像件直接以 exp_neg 收口；exp 的 req 兼容由     *)
(*   CW219 已证件 exp_neg_req_compat_setoid（L66223）免费供给，        *)
(*   不再立新假设（CW220 原件 2 节内同形 Hypothesis 桥由此被证明件替代）。 *)
(*                                                                *)
(* 交付清单（8 件，双形并存）：                                     *)
(*  形 A（req 形·CW219 AttentionGibbsBridgeSetoid 载体，S : Type）：  *)
(*   A1 zauto_mirror_point_setoid      保底·逐点镜像件               *)
(*       （inv D == one + energy == -z 逐点                          *)
(*         ⟹ exp_neg(inv D·energy s) == exp_pos(z s) 逐点）          *)
(*   A2 zauto_Z_eq_setoid              主件·Z_auto 引理              *)
(*       （partition_function_setoid == Z_thermo_setoid）            *)
(*   A3 zauto_attention_is_gibbs_noZ_setoid  主件2·前提消去示范件     *)
(*       （原件 1 同结论、少前提 3——配分相等前提由 A2 供替）          *)
(*  形 B（req 形·CW220 SigMigrate 温度参数载体，S : Set）：           *)
(*   B1 zauto_mirror_point_temp        保底·逐点镜像件（温度参数形）  *)
(*   B2 zauto_Z_eq_temp                主件·Z_auto 引理（温度参数形） *)
(*   B3 zauto_attention_is_gibbs_temp_noZ   主件2·前提消去示范件      *)
(*       （原件 2 同结论、少前提 3——配分相等前提由 B2 供替）          *)
(*  形 C（Id 形·Set 层零 Prop，CW219 RealInterfaceEnhanced+SumOver）： *)
(*   C1 zauto_id_mirror                保底·逐点镜像件（Id 形）       *)
(*   C2 zauto_id_Z_eq                  主件·Z_auto 引理（Id 形）      *)
(*                                                                *)
(* 诚实账目：A3/B3 相对原件少一实质前提（配分相等），多一求和载体      *)
(*   外延参数（sum_req_ext / sumf_req_ext）——该参数是载体接口性质，    *)
(*   任何具体求和（有限和/列表和）构造性满足，非对分布的新增假设；     *)
(*   A2/B2/C2 的 Z_auto 本体即「premise 可由（镜像前提+外延）自动供替」  *)
(*   的定理形态。                                                   *)
(*                                                                *)
(* 红线：Set 层语句零 Prop（req/lt/Id 均 Set 值谓词）；全 Qed 闭合；    *)
(*   尾部 Print Assumptions 新件全 Closed；既有文件零改；零 git。      *)
(* 前缀台账：zauto_ 前缀全库 grep 零重名（本席首用）。                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import CW220_Extensions.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 形 A（req 形）：CW219 AttentionGibbsBridgeSetoid 载体             *)
(*   出口签名实测：Z_thermo_setoid R RI S sum D D_pos energy；       *)
(*   partition_function_setoid R RI S sum z；                       *)
(*   attention_is_gibbs_setoid 前提序 = HD、Henergy、HZ。             *)
(* ============================================================ *)

(* A1 保底·逐点镜像件：inv D == one + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_pos(z s)（即 exp_neg(opp(z s))）逐点。 *)
Lemma zauto_mirror_point_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (D : R) (D_pos : lt zero D) (energy z : S -> R),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@boltzmann_factor_setoid R RIS S D D_pos energy s)
      (@exp_pos_fn_setoid R RIS (z s)).
Proof.
  intros R RIS S D D_pos energy z HD Henergy s.
  exact (@exp_neg_req_compat_setoid R RIS
           (mult (inv_pos D D_pos) (energy s)) (opp (z s))
           (@req_trans R RIS (mult (inv_pos D D_pos) (energy s)) (energy s) (opp (z s))
              (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                             (mult one (energy s)) (energy s)
                 (@req_mult_compat R RIS (inv_pos D D_pos) one (energy s) (energy s)
                    HD (@req_refl R RIS (energy s)))
                 (@req_trans R RIS (mult one (energy s)) (mult (energy s) one) (energy s)
                    (@mult_comm R RIS one (energy s))
                    (@mult_one R RIS (energy s))))
              (Henergy s))).
Qed.

(* A2 主件·Z_auto 引理：partition_function_setoid == Z_thermo_setoid。
   逐点镜像（A1）+ 求和外延（sum_req_ext）组装；配分相等前提不出现。 *)
Lemma zauto_Z_eq_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (sum_req_over_S : (S -> R) -> R)
         (sum_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sum_req_over_S f) (sum_req_over_S g))
         (D : R) (D_pos : lt zero D) (energy z : S -> R),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req (@partition_function_setoid R RIS S sum_req_over_S z)
      (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy).
Proof.
  intros R RIS S sum_req_over_S sum_req_ext D D_pos energy z HD Henergy.
  exact (sum_req_ext (fun s : S => exp_neg (opp (z s)))
                     (fun s : S => exp_neg (mult (inv_pos D D_pos) (energy s)))
                     (fun s : S =>
                        @req_sym R RIS (exp_neg (mult (inv_pos D D_pos) (energy s)))
                          (exp_neg (opp (z s)))
                          (zauto_mirror_point_setoid R RIS S D D_pos energy z
                                                     HD Henergy s))).
Qed.

(* A3 主件2·前提消去示范件：原件 1 attention_is_gibbs_setoid 同结论，
   配分相等前提（req Z_thermo_setoid (partition_function_setoid z)）
   不再出现——由 A2 供替（req_sym 换向后喂入）。 *)
Lemma zauto_attention_is_gibbs_noZ_setoid :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Type)
         (sum_req_over_S : (S -> R) -> R)
         (sum_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sum_req_over_S f) (sum_req_over_S g))
         (sum_pos_preserved_req : forall f : S -> R,
            (forall s : S, lt zero (f s)) -> lt zero (sum_req_over_S f))
         (D : R) (D_pos : lt zero D) (energy z : S -> R)
         (Z_thermo_pos : lt zero (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy)),
  req (inv_pos D D_pos) one ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@softmax_setoid R RIS S sum_req_over_S sum_pos_preserved_req z s)
      (@boltzmann_dist_attn_setoid R RIS S sum_req_over_S D D_pos energy
                                   Z_thermo_pos s).
Proof.
  intros R RIS S sum_req_over_S sum_req_ext sum_pos_preserved_req
         D D_pos energy z Z_thermo_pos HD Henergy s.
  exact (@attention_is_gibbs_setoid R RIS S sum_req_over_S sum_pos_preserved_req
           D D_pos energy z Z_thermo_pos HD Henergy
           (@req_sym R RIS (@partition_function_setoid R RIS S sum_req_over_S z)
                     (@Z_thermo_setoid R RIS S sum_req_over_S D D_pos energy)
                     (zauto_Z_eq_setoid R RIS S sum_req_over_S sum_req_ext
                                        D D_pos energy z HD Henergy)) s).
Qed.

(* ============================================================ *)
(* 形 B（req 形）：CW220 SigMigrate.ReqGibbsPilot 温度参数载体        *)
(*   出口签名实测（@ 全参形）：                                      *)
(*   Z_thermo R RIS S sumf D D_pos energy；                          *)
(*   partition_function_temp R RIS S sumf T T_pos z；                *)
(*   req_attention_is_gibbs_temp 前提序 = HD（inv T == inv D）、       *)
(*   Henergy、HZ（req Z_thermo partition_function_temp）。            *)
(* ============================================================ *)

(* B1 保底·逐点镜像件（温度参数形）：inv T == inv D + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_neg(opp(inv T·z s)) 逐点
   （RHS 即 partition_function_temp 第 s 项，exp_pos_fn delta 换形后）。 *)
Lemma zauto_mirror_point_temp :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@SigMigrate.boltzmann_factor R RIS S D D_pos energy s)
      (exp_neg (opp (mult (inv_pos T T_pos) (z s)))).
Proof.
  intros R RIS S T T_pos D D_pos energy z HD Henergy s.
  exact (@exp_neg_req_compat_setoid R RIS
           (mult (inv_pos D D_pos) (energy s)) (opp (mult (inv_pos T T_pos) (z s)))
           (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                       (opp (mult (inv_pos D D_pos) (z s)))
                       (opp (mult (inv_pos T T_pos) (z s)))
              (@req_trans R RIS (mult (inv_pos D D_pos) (energy s))
                          (mult (inv_pos D D_pos) (opp (z s)))
                          (opp (mult (inv_pos D D_pos) (z s)))
                 (@req_mult_compat R RIS (inv_pos D D_pos) (inv_pos D D_pos)
                                   (energy s) (opp (z s))
                    (@req_refl R RIS (inv_pos D D_pos)) (Henergy s))
                 (@SigMigrate.req_mult_opp_l R RIS (inv_pos D D_pos) (z s)))
              (@req_opp_compat R RIS (mult (inv_pos D D_pos) (z s))
                               (mult (inv_pos T T_pos) (z s))
                 (@req_mult_compat R RIS (inv_pos D D_pos) (inv_pos T T_pos)
                                   (z s) (z s)
                    (@req_sym R RIS (inv_pos T T_pos) (inv_pos D D_pos) HD)
                    (@req_refl R RIS (z s)))))).
Qed.

(* B2 主件·Z_auto 引理（温度参数形）：partition_function_temp == Z_thermo。
   逐点镜像（B1）+ 求和外延（sumf_req_ext，诚实接口：任何具体求和
   构造性满足）组装；配分相等前提不出现。 *)
Lemma zauto_Z_eq_temp :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (sumf : (S -> R) -> R)
         (sumf_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  req (@SigMigrate.partition_function_temp R RIS S sumf T T_pos z)
      (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy).
Proof.
  intros R RIS S sumf sumf_req_ext T T_pos D D_pos energy z HD Henergy.
  exact (sumf_req_ext (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                      (fun s : S => exp_neg (mult (inv_pos D D_pos) (energy s)))
                      (fun s : S =>
                         @req_sym R RIS (exp_neg (mult (inv_pos D D_pos) (energy s)))
                           (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                           (zauto_mirror_point_temp R RIS S T T_pos D D_pos energy z
                                                    HD Henergy s))).
Qed.

(* B3 主件2·前提消去示范件（温度参数形）：原件 2 req_attention_is_gibbs_temp
   同结论，前提 3（req Z_thermo partition_function_temp）不再出现——
   由 B2 供替；原节内 exp 兼容 Hypothesis 桥位由已证件
   exp_neg_req_compat_setoid 填充（该假设也被消去）。 *)
Lemma zauto_attention_is_gibbs_temp_noZ :
  forall (R : Set) (RIS : RealInterfaceEnhancedSetoid R) (S : Set)
         (sumf : (S -> R) -> R)
         (sumf_req_ext : forall f g : S -> R,
            (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g))
         (T : R) (T_pos : lt zero T) (D : R) (D_pos : lt zero D)
         (energy z : S -> R)
         (partition_function_temp_pos :
            lt zero (@SigMigrate.partition_function_temp R RIS S sumf T T_pos z))
         (Z_thermo_pos : lt zero (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy)),
  req (inv_pos T T_pos) (inv_pos D D_pos) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  forall s : S,
  req (@SigMigrate.softmax_temp R RIS S sumf T T_pos z
                                partition_function_temp_pos s)
      (@SigMigrate.boltzmann_dist_attn R RIS S sumf D D_pos energy Z_thermo_pos s).
Proof.
  intros R RIS S sumf sumf_req_ext T T_pos D D_pos energy z
         partition_function_temp_pos Z_thermo_pos HD Henergy s.
  exact (@SigMigrate.req_attention_is_gibbs_temp R RIS S sumf
           (@exp_neg_req_compat_setoid R RIS)
           T T_pos D D_pos energy z partition_function_temp_pos Z_thermo_pos
           HD Henergy
           (@req_sym R RIS (@SigMigrate.partition_function_temp R RIS S sumf T T_pos z)
                     (@SigMigrate.Z_thermo R RIS S sumf D D_pos energy)
                     (zauto_Z_eq_temp R RIS S sumf sumf_req_ext T T_pos D D_pos
                                      energy z HD Henergy)) s).
Qed.

(* ============================================================ *)
(* 形 C（Id 形·Set 层零 Prop）：CW219 RealInterfaceEnhanced + SumOver。 *)
(*   外延引擎 = SumOver 字段 sum_over_S_ext（Id 形，实测 L1411）。      *)
(* ============================================================ *)

Section ZAutoId.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Context {SO : SumOver RI SS}.

Let R := @R RI.
Let S := @S RI SS.
Let zero := @CW_ConstructiveWorld_219.zero RI.
Let one := @CW_ConstructiveWorld_219.one RI.
Let mult := @CW_ConstructiveWorld_219.mult RI.
Let opp := @CW_ConstructiveWorld_219.opp RI.
Let lt := @CW_ConstructiveWorld_219.lt RI.
Let inv_pos := @CW_ConstructiveWorld_219.inv_pos RI.
Let exp_neg := @CW_ConstructiveWorld_219.exp_neg RI.
Let sum_over_S := @sum_over_S RI SS SO.

Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition zauto_id_boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).

Definition zauto_id_Z_thermo : R :=
  sum_over_S zauto_id_boltzmann_factor.

Definition zauto_id_exp_pos (x : R) : R := exp_neg (opp x).

Definition zauto_id_partition : R :=
  sum_over_S (fun s : S => zauto_id_exp_pos (z s)).

(* C1 保底·逐点镜像件（Id 形）：inv D == one + energy == -z 逐点
   ⟹ exp_neg(inv D·energy s) == exp_pos(z s) 逐点（Id 收口，零 Prop）。 *)
Lemma zauto_id_mirror :
  Id (inv_pos D D_pos) one ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  forall s : S,
  Id (zauto_id_boltzmann_factor s) (zauto_id_exp_pos (z s)).
Proof.
  intros HD Henergy s.
  exact (id_cong (fun x : R => exp_neg x)
           (id_trans
              (id_trans (id_cong (fun x : R => mult x (energy s)) HD)
                        (id_trans (@CW_ConstructiveWorld_219.mult_comm RI one (energy s))
                                  (@CW_ConstructiveWorld_219.mult_one RI (energy s))))
              (Henergy s))).
Qed.

(* C2 主件·Z_auto 引理（Id 形）：zauto_id_partition == zauto_id_Z_thermo。
   逐点镜像（C1）+ SumOver 外延字段组装；Id 层语句，零 Prop。 *)
Lemma zauto_id_Z_eq :
  Id (inv_pos D D_pos) one ->
  (forall s : S, Id (energy s) (opp (z s))) ->
  Id zauto_id_partition zauto_id_Z_thermo.
Proof.
  intros HD Henergy.
  exact (@sum_over_S_ext RI SS SO (fun s : S => zauto_id_exp_pos (z s))
                         zauto_id_boltzmann_factor
                         (fun s : S => id_sym (zauto_id_mirror HD Henergy s))).
Qed.

End ZAutoId.

(* ============================================================ *)
(* 尾验：新件零假设（Closed）——8 件全数打表                          *)
(* ============================================================ *)
Print Assumptions zauto_mirror_point_setoid.
Print Assumptions zauto_Z_eq_setoid.
Print Assumptions zauto_attention_is_gibbs_noZ_setoid.
Print Assumptions zauto_mirror_point_temp.
Print Assumptions zauto_Z_eq_temp.
Print Assumptions zauto_attention_is_gibbs_temp_noZ.
Print Assumptions zauto_id_mirror.
Print Assumptions zauto_id_Z_eq.
