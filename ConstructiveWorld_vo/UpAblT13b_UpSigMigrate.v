(* ============================================================ *)
(* ToyR 玩具证替换件 —— T263 台账席 战役包X（tier2 十四批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabT13b_sigm_partition_cond（原 L72，1 句玩具证）                    *)
(*   uabT13b_sigm_Zthermo_pos（原 L57，5 句玩具证）                       *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T337 恒等守恒更正注记】2026-09-22 包AW十三 台账席（恒等头注更正第三批） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* T277（包AL）全量恒等核查定谳、T317（包AV六）试点定谳：本件实测为 *)
(* 恒等守恒——清单所列 2 槽证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* 零变化），头注「替换」声称与实物不符，特此更正。 *)
(* 更正口径：真替换 0 槽＋恒等守恒 2 槽；本注记为追加块，上方原头注一字 *)
(* 未改（历史证据保全）；证明体、声明面、语句面、Require 面零改动；台账 *)
(* 承载见 T277 附录／T284 修正块／T317 评估册／T321／T329／T330／T337 台账。 *)
(* 附记：T277 判级全文恒等；M-Z 域未及件（V 收尾＋X 整包＋Y 起步）第四批直推（T317 六·1 方案①）。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblT13b_UpSigMigrate.v —— 假设消融战役 T13b 承接席（批6 配分正性族三位）  *)
(* 辖区：UpSigMigrate.v 三位（T13a 移交单 §6 批6 行点名加「等」位认列）：        *)
(*   位1 UpSigMigrate.v:49   Z_pos（ReqFreeEnergyPilot 配分正性位）             *)
(*   位2 UpSigMigrate.v:50   partition_condition（配分条件槽；T13a 点名 11 位    *)
(*       外「等」2 待勘位之一，本席对普查 17 位家族逐位清点认列）                *)
(*   位3 UpSigMigrate.v:549  Z_thermo_pos（ReqGibbsPilot 配分正性位）           *)
(* 被消融位语句（现档逐字）：                                                   *)
(*   :48-50  Variable Z : R. Variable Z_pos : lt zero Z.                        *)
(*           假设申报 partition_condition :                                   *)
(*             req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos)            *)
(*                                     (base_loss s)))).                        *)
(*   :548-549 Definition sigm_Z_thermo : R := sumf sigm_boltzmann_factor.       *)
(*           Variable Z_thermo_pos : lt zero sigm_Z_thermo.                     *)
(* 放电母本：                                                                   *)
(*   位1 ←req_Z_temp_pos@UpReqDist:2808 同机制（前提=配分条件+正和槽；           *)
(*         迁移经 lt_id_r/req_sym 接口字段，T13a 桥形 req=Id 同口径）；           *)
(*   位2 ←c_partition@UpSigMigrate2:1589 两状态实例判例直喂（exp_neg_zero/       *)
(*         req_plus_compat 实例代数已在其证明体）；                              *)
(*   位3 ←sumd_sum_pos@UpReqSumD:233 正和族（节内 sum_pos 槽显式参）加           *)
(*         exp_neg_pos 逐点正。                                                 *)
(* 消融形（诚实登记）：位1/位3 正和数据槽显式参（抽象载体上不放电，典范载体      *)
(*   加装配桥 tsi_rie_setoid 上成立）；位2 具体实例供给（两状态世界）。           *)
(* 分级：位1 N1（机制件材料化）；位2 N3（实例供给直喂）；位3 N1（正和族直喂）。   *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、UpSigMigrate、          *)
(*   UpSigMigrate2、TempSoftmaxInstantiation。                                  *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                          *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Require Import TempSoftmaxInstantiation.
Import RealInterfaceEnhancedMod.

Section UabT13bSigm.

Context {RI0 : RealInterfaceEnhanced}.
Let R0 : Set := @S01_BaseRing.R RI0.

(* 位1 ←:49（配分条件迁移正和正性；正和槽与配分槽显式参） *)
Theorem uabT13b_sigm_Zpos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (base_loss : S -> R0) (D : R0) (D_pos : lt zero D) (Z : R0),
    req Z (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) ->
    lt zero Z.
Proof.
  intros S sumf Hpos base_loss D D_pos Z Hpc.
  apply (@lt_id_r R0 (tsi_rie_setoid RI0) zero
           (sumf (fun s : S => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
  - apply req_sym. exact Hpc.
  - apply Hpos. intros s.
    exact (exp_neg_pos (mult (inv_pos D D_pos) (base_loss s))).
Qed.

(* 位3 ←:549（正和面加逐点正；正和槽显式参） *)
Theorem uabT13b_sigm_Zthermo_pos :
  forall (S : Set) (sumf : (S -> R0) -> R0)
         (Hpos : forall f : S -> R0, (forall s : S, lt zero (f s)) -> lt zero (sumf f))
         (D : R0) (D_pos : lt zero D) (energy : S -> R0),
    lt zero (@sigm_Z_thermo R0 (tsi_rie_setoid RI0) S sumf D D_pos energy).
Proof.
  intros S sumf Hpos D D_pos energy.
  unfold sigm_Z_thermo, sigm_boltzmann_factor.
  apply Hpos.
  intros s.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy s))).
Qed.

End UabT13bSigm.

(* 位2 ←:50（两状态具体实例供给；实载体 Real 载体面，全局实例消解） *)
Theorem uabT13b_sigm_partition_cond :
  req two_state_Z
      (bsum (fun s : bool =>
               exp_neg (mult (inv_pos real_one real_lt_zero_one)
                             (two_state_loss s)))).
Proof.
  exact c_partition.
Qed.

(* ---- 收尾段 ---- *)
Print Assumptions uabT13b_sigm_Zpos.
Print Assumptions uabT13b_sigm_Zthermo_pos.
Print Assumptions uabT13b_sigm_partition_cond.
