(* ============================================================ *)
(* UpAblT5_S04_RealExpLogConv.v —— 假设消融战役 T5a 席（FA1 第⑦⑧批：inv/log 桥 + r_arch_pow） *)
(* 母本：S04_RealExpLogConv.v（原树零改，只读消费；Live_X 根与 Main 行号齐）        *)
(*                                                              *)
(* 辖区三槽（普查表 _tfa1_ §④ 批7/批8 + §① 行号锚）：                *)
(*   ① L3341 inv_pos_lt_compat —— 抽象 RI 层直喂（N1）               *)
(*      放电件：ipl_inv_pos_lt_compat@InvPosLtCompat.v:62（同层同形） *)
(*      消费位：S04:3752 / S04:4252                                  *)
(*   ② L778  log_lt_mono_cc —— Real 层实例供给（N3）                 *)
(*      放电件：logd_log_lt_mono_real@G05_LogSmall.v:966（Part C1 判词：  *)
(*      log_lt_mono_cc 槽族由 real_log_lt_mono@S07:6510 供给）        *)
(*      消费位：S04:822                                              *)
(*   ③ L303  r_arch_pow —— Real 层实例供给（N3）                     *)
(*      放电件：r_arch_pow_real@CW220_Extensions.v:1032              *)
(*      （节参 kappa/kappa_pos/kappa_lt_one@S04:277-279 出节全参形；    *)
(*        G07_KLWall:924 同构先例：镜像幂 Fixpoint 定义级实例化桥）      *)
(*      消费位：S04:763 / S04:819                                    *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 公理面零新增 / 原树零改 /          *)
(*       独立伴生件不并入原模块 / 前缀 abl_ 本件内防撞。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import InvPosLtCompat.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
Require Import G05_LogSmall.

(* ################ ① inv_pos_lt_compat（母本 L3341-3342 逐字槽形） ################ *)
(* 母本节：Section FreeEnergyMinimization（L1981-4943），Context {RI}{SS}{SO}；  *)
(* 语句仅依赖 RI，故镜像节只带 RI（与 InvPosLtCompat.v 同款解包前导）。          *)
Section AblS04FreeEnergy.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

Theorem abl_S04_inv_pos_lt_compat : forall a b : R, forall Ha : lt zero a, forall Hb : lt zero b,
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblS04FreeEnergy.

(* ################ ② log_lt_mono_cc（母本 L778 逐字槽形；Real 层实例供给形） ######### *)
(* 母本语句为抽象 RI 层 total-log 形（Section ConvergenceCauchy:238-1457）；        *)
(* 实例供给取 G05 Part C1 同款 Real 层 real_log 见证形（G05:966 判词原文点名        *)
(* log_lt_mono_cc 槽族）。                                                        *)
Theorem abl_S04_log_lt_mono_cc : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  exact logd_log_lt_mono_real.
Qed.

(* ################ ③ r_arch_pow（母本 L303-305 逐字槽形；Real 层实例供给形） ######### *)
(* 镜像幂：母本节内 Fixpoint r_pow（L293-296，O↦one，S m↦mult x (r_pow x m)）        *)
(* 逐形复刻于具体层；与 real_pow@CW220:777 定义级同构（G07:924 先例同桥）。          *)
Fixpoint abl_r_pow (x : Real) (n : nat) : Real :=
  match n with
  | 0%nat => real_one
  | Datatypes.S m => real_mult x (abl_r_pow x m)
  end.

(* 母本节参出节全参形：kappa/kappa_pos/kappa_lt_one（L277-279）+ 槽位四参。 *)
Theorem abl_S04_r_arch_pow :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun n : nat => real_lt (real_mult a (abl_r_pow kappa n)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  exact (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps).
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_S04_inv_pos_lt_compat.
Print Assumptions abl_S04_log_lt_mono_cc.
Print Assumptions abl_S04_r_arch_pow.
