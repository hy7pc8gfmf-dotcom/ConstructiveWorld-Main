(* ============================================================ *)
(* UpAblT5_S05_AlignmentGRPO.v —— 假设消融战役 T5a 席（FA1 第⑦批 inv/log 桥）      *)
(* 母本：S05_AlignmentGRPO.v（原树零改，只读消费）                                *)
(*                                                              *)
(* 辖区两槽（普查表 _tfa1_ §④ 批7 + §① 行号锚）：                    *)
(*   ① L2303 inv_pos_lt_contra —— 抽象 RI 层直喂（N1）                *)
(*      放电件：ipl_inv_pos_lt_compat@InvPosLtCompat.v:62（同层同形；      *)
(*      母本仅名异形同：参分组 (a b) 括号形，语句逐字同）                  *)
(*      消费位：S05:2330（sigmoid_strict_inc 构造体）                    *)
(*   ② L2314 log_lt_mono —— Real 层实例供给（N3）                     *)
(*      放电件：logd_log_lt_mono_real@G05_LogSmall.v:966                *)
(*      （与 abl_S04_log_lt_mono_cc 同喂形；镜像件注记禁双计数）           *)
(*      消费位：S05:2373（sigmoid_strict_inc 第三步）                    *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 公理面零新增 / 原树零改 /          *)
(*       独立伴生件不并入原模块 / 前缀 abl_ 本件内防撞。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import InvPosLtCompat.
Require Import G05_LogSmall.

(* ################ ① inv_pos_lt_contra（母本 L2303-2305 逐字槽形） ################ *)
(* 母本节：Section Alignment（L24 起），抽象 RI 层；镜像节与 InvPosLtCompat 同款。 *)
Section AblS05Alignment.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let R := @R RI.
Let zero := @zero RI.
Let one := @one RI.
Let mult := @mult RI.
Let inv_pos := @inv_pos RI.
Let lt := @lt RI.

Theorem abl_S05_inv_pos_lt_contra :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  exact (ipl_inv_pos_lt_compat a b Ha Hb Hab).
Qed.

End AblS05Alignment.

(* ################ ② log_lt_mono（母本 L2314-2315 逐字槽形；Real 层实例供给形） ####### *)
(* 母本语句为抽象 RI 层 total-log 形（Section Alignment）；实例供给取 G05 Part C1    *)
(* Real 层 real_log 见证形（同 abl_S04_log_lt_mono_cc 喂形；镜像件按 T1b 口径      *)
(* 计件注记：N1/N3 同源直喂，两件并列申报不注水）。                                *)
Theorem abl_S05_log_lt_mono : forall (a b : Real) (Ha : real_lt real_zero a)
    (Hb : real_lt real_zero b),
  real_lt a b -> real_lt (real_log a Ha) (real_log b Hb).
Proof.
  exact logd_log_lt_mono_real.
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_S05_inv_pos_lt_contra.
Print Assumptions abl_S05_log_lt_mono.
