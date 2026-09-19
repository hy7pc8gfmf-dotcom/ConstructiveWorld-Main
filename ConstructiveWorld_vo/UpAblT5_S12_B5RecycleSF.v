(* ============================================================ *)
(* UpAblT5_S12_B5RecycleSF.v —— 假设消融战役 T5a 席（FA1 第⑦批 log 桥）           *)
(* 母本：S12_B5RecycleSF.v（原树零改，只读消费）                                *)
(*                                                              *)
(* 辖区一槽（普查表 _tfa1_ §④ 批7 + §① 行号锚）：                     *)
(*   L12061 sf_log_antitone_le —— 具体层逐字直喂（N1）                 *)
(*      母本语句为具体 Real 层形（Section SFSoftmaxInfoNCE:11944；              *)
(*      母本 L12056-12060 原注：陈述已按单调形修正，保留名 sf_log_antitone_le）   *)
(*      放电件：real_log_le_mono（壳内 S14:14236 直供；E403 B1 mono 链同族）      *)
(*      消费位：S12:12085（sf_infonce_nonneg 构造体）                     *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 公理面零新增 / 原树零改 /          *)
(*       独立伴生件不并入原模块 / 前缀 abl_ 本件内防撞。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.

(* ################ sf_log_antitone_le（母本 L12061-12064 逐字槽形） ################ *)
Theorem abl_S12_sf_log_antitone_le :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b ->
    real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (real_log_le_mono a b Ha Hb Hab).
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_S12_sf_log_antitone_le.
