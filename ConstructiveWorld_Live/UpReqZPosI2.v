(* ============================================================ *)
(* UpReqZPosI2.v —— G3 Definition-Z 面直装席：Z_pos 族余量逐槽实例化  *)
(*   消费席60 通用键 UpReqZPosD（zposd_Z_pos 主键）+ G1 钥匙          *)
(*   UpReqSumD（sumd_sum_pos 根引擎）+ CW219 exp/mult 正性引擎，      *)
(*   为普查 §G3 Definition-Z 余量面产出 T2 模板② 形态逐槽放电件：    *)
(*   槽类型在 E354 填位（sumf := sumd_sumf 喂参）的实例语句，非空     *)
(*   前提 Not (enum = nil) 显式携带（诚实降级）。                    *)
(*                                                                *)
(* 前缀台账：前缀 zpi2_ 在席64 UpReqZPosI.v 面2 已有 4 名             *)
(*   （zpi2_partition_condition / zpi2_Z_pos / zpi2_boltzmann_dist_m2 / *)
(*   zpi2_req_boltzmann_positive）；本席逐名 grep 全库零重名，文件名    *)
(*   UpReqZPosI2.v 与 UpReqZPosI.v 无冲突（双形并存，零既有文件改动）。 *)
(*                                                                *)
(* 逐槽清偿表（sed 实读行号；键填充/根引擎/阻塞三分级）：             *)
(*  保底 4：                                                      *)
(*   ① UpReqAlign.v:94   Z_align_pos : lt zero Z_align_req          *)
(*      （Z_align_req@92 := sumf 逐项 mult (pi_ref s) 乘 exp_neg     *)
(*      （opp 翻转指数）——见勘误 1）                               *)
(*   ② UpReqAlign2.v:104  Z_align_pos : lt zero req2_Z_align         *)
(*      （req2_Z_align@102 同形体）                                *)
(*   ③ UpReqAlignRestA.v:75 Z_align_pos : lt zero (Z_align_req …)    *)
(*   ④ UpReqDpoLoss.v:58  Z_align_pos : lt zero (Z_align_req …)      *)
(*  主件 11：                                                     *)
(*   ⑤ UpReqAlign3.v:114  ZAL_pos : lt zero ZAL（ZAL := req2_Z_align） *)
(*   ⑥ UpReqU2.v:343      ZAL_pos 同形                             *)
(*   ⑦ UpAlignIdReq.v:163 ZAL_pos 同形                             *)
(*   ⑧ UpReqPPOPlain.v:115 Zap : lt zero (Z_align_req S sumf …)      *)
(*   ⑨ UpReqPPO.v:95      Zap 同形（节载体名 Real，语句同型）        *)
(*   ⑩ UpSigMigrate.v:540 Z_thermo_pos : lt zero Z_thermo           *)
(*      （键填充：zposd_Z_pos 直供，base_loss := energy，β := D）    *)
(*   ⑪ UpEvictIdReq.v:88  Z_thermo_pos 同形（键填充）               *)
(*   ⑫ UpReqAttnIter.v:129 Z_thermo_i_pos（键填充）                 *)
(*   ⑬ UpReqAttnGibbs.v:543 Z_thermo_r_pos（键填充）                *)
(*   ⑭ UpSigMigrate2.v:891 Z_align_a_pos : lt zero Z_align_a_sum     *)
(*   ⑮ UpSigMigrate.v:533 partition_function_temp_pos                *)
(*      （exp_pos_fn := exp_neg∘opp 换形，根引擎逐项 exp 正性）      *)
(*                                                                *)
(* 阻塞裁决（兜底，逐槽如实报；本席零越权）：                         *)
(*   B1 UpReqAlign.v:709 HZ : lt zero Z_aud_req——Z_aud_req :=        *)
(*      sumf (fun s => if post_aud s then p s else zero)：零腿分支和  *)
(*      （非 posting 态项为 zero），非全正项和；sumd_sum_pos 全正前提 *)
(*      在零腿不可满足，posting 非空信息缺失，阻塞归 N。             *)
(*   B2 UpEvictIdReq.v:117 evicted_partition_pos——evicted_partition  *)
(*      := sumf (fun s => if keep_dec s then boltzmann_factor s      *)
(*      else zero)：同零腿分支和（keep 分支），kept 非空信息缺失，    *)
(*      阻塞归 N。                                                  *)
(*   B3 UpReqAttnGibbs.v:697 evicted_partition_r_pos——同 B2 零腿形，  *)
(*      阻塞归 N。                                                  *)
(*   B4 UpReqAlignRestB.v:1755 req_evicted_partition_pos——求和载体为  *)
(*      sum_over_S 且节载体 S : Type（Check 实证），与 enum 列表键     *)
(*      载体不匹配 + 零腿 match keep_dec 分支，双重不适配，阻塞归 N。  *)
(*                                                                *)
(* 勘误（对表所出，以 sed/Check 现值为准）：                          *)
(*   1. 键形失配类：zposd 四键的指数形为 exp_neg (mult (inv_pos β β⁻¹) *)
(*      (base_loss s))；Align 族（①②③④⑤⑥⑦⑧⑨⑭）逐项实为          *)
(*      mult (pi_ref s) (exp_neg (opp (mult (inv_pos beta beta_pos)   *)
(*      (reward s))))——pi_ref 外乘 + 指数 opp 翻转，键形不可对接      *)
(*      （ convertible 实证否），改沿 G1 根引擎 sumd_sum_pos +         *)
(*      mult_positive/exp_neg_pos 纯项式直装（即席60 zposd_Z_pos      *)
(*      内部同链），台账记「键形失配→根引擎直装」，不放大主张；        *)
(*   2. ⑮ exp_pos_fn 为透明 Definition（exp_neg∘opp），delta 换形后    *)
(*      根引擎逐项 exp_neg_pos 直供，同上登记；                       *)
(*   3. ⑨ UpReqPPO 节载体绑定名 Real（语句与 R 实例同型，绑定名差异    *)
(*      不改语句）；                                                 *)
(*   4. 面常数 R/RIS 为非极大隐式位，直装喂定一律 @ 全参形（席64       *)
(*      勘误3 同法）；feed 形 sumf := @sumd_sumf R RIS S enum（部分    *)
(*      应用即 (S->R)->R 载体，E354 装法）。                          *)
(*                                                                *)
(* 红线：Set 层语句（lt/req 均 Set 值谓词，零泄露）；纯项式组装        *)
(*   （exact 供给项，零重写战术）；零外部未证假设，尾部 Print          *)
(*   Assumptions 新件全 Closed；既有文件零改；零 git。                *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqZPosD.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpSigMigrate.
Require Import UpSigMigrate2.
Require Import UpEvictIdReq.
Require Import UpReqAttnIter.
Require Import UpReqAttnGibbs.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* 保底 ①：UpReqAlign.v:94 槽实例（Z_align_req@92 E354 填位）        *)
(* ============================================================ *)
Lemma zpi2_align1_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ②：UpReqAlign2.v:104 槽实例（req2_Z_align@102 E354 填位）     *)
(* ============================================================ *)
Lemma zpi2_align2_req2_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ③：UpReqAlignRestA.v:75 槽实例（全局 Z_align_req E354 填位）  *)
(* ============================================================ *)
Lemma zpi2_resta_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 保底 ④：UpReqDpoLoss.v:58 槽实例（全局 Z_align_req E354 填位）     *)
(* ============================================================ *)
Lemma zpi2_dpo_Z_align_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑤：UpReqAlign3.v:114 ZAL_pos 槽实例（ZAL := req2_Z_align）    *)
(* ============================================================ *)
Lemma zpi2_align3_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑥：UpReqU2.v:343 ZAL_pos 槽实例（同形）                      *)
(* ============================================================ *)
Lemma zpi2_u2_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑦：UpAlignIdReq.v:163 ZAL_pos 槽实例（同形）                  *)
(* ============================================================ *)
Lemma zpi2_alignidreq_ZAL_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign2.req2_Z_align R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑧：UpReqPPOPlain.v:115 Zap 槽实例（全局 Z_align_req 填位）    *)
(* ============================================================ *)
Lemma zpi2_ppoplain_Zap
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑨：UpReqPPO.v:95 Zap 槽实例（节载体绑定名 Real，语句同型；    *)
(*         勘误 3）                                                  *)
(* ============================================================ *)
Lemma zpi2_ppo_Zap
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAlign.Z_align_req R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑩：UpSigMigrate.v:540 Z_thermo_pos 槽实例——键填充：           *)
(*   Z_thermo@539 := sumf boltzmann_factor，boltzmann_factor@536 :=   *)
(*   exp_neg (mult (inv_pos D D_pos) (energy s))，E354 填位后与        *)
(*   zposd_Z（base_loss := energy，β := D）定义性重合，zposd_Z_pos    *)
(*   一次喂定。                                                      *)
(* ============================================================ *)
Lemma zpi2_sigmig_Z_thermo_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate.Z_thermo R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑪：UpEvictIdReq.v:88 Z_thermo_pos 槽实例（键填充，同⑩形）     *)
(* ============================================================ *)
Lemma zpi2_evict_Z_thermo_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpEvictIdReq.Z_thermo R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑫：UpReqAttnIter.v:129 Z_thermo_i_pos 槽实例（键填充）        *)
(* ============================================================ *)
Lemma zpi2_iter_Z_thermo_i_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAttnIter.Z_thermo_i R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑬：UpReqAttnGibbs.v:543 Z_thermo_r_pos 槽实例（键填充）       *)
(* ============================================================ *)
Lemma zpi2_gibbs_Z_thermo_r_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (D : R) (D_pos : lt zero D) (energy : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpReqAttnGibbs.Z_thermo_r R RIS S (@sumd_sumf R RIS S enum)
             D D_pos energy).
Proof.
  exact (@zposd_Z_pos R RIS S enum energy D D_pos Hne).
Qed.

(* ============================================================ *)
(* 主件 ⑭：UpSigMigrate2.v:891 Z_align_a_pos 槽实例                   *)
(*   （Z_align_a_sum@889 Align 同形体；勘误 1 根引擎直装）             *)
(* ============================================================ *)
Lemma zpi2_sigmig2_Z_align_a_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (reward : S -> R) (beta : R) (beta_pos : lt zero beta)
      (pi_ref : S -> R) (pi_ref_pos : forall s : S, lt zero (pi_ref s))
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate2.Z_align_a_sum R RIS S (@sumd_sumf R RIS S enum)
             reward beta beta_pos pi_ref).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => mult (pi_ref s)
                       (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))
           Hne
           (fun s : S =>
              @mult_positive R RIS (pi_ref s)
                (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))
                (pi_ref_pos s)
                (@exp_neg_pos R RIS
                   (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Qed.

(* ============================================================ *)
(* 主件 ⑮：UpSigMigrate.v:533 partition_function_temp_pos 槽实例      *)
(*   （partition_function_temp@531 := sumf (fun s => exp_pos_fn       *)
(*   (mult (inv_pos T T_pos) (z s)))，exp_pos_fn := exp_neg∘opp 透明   *)
(*   换形（勘误 2），根引擎逐项 exp 正性直供）                        *)
(* ============================================================ *)
Lemma zpi2_sigmig_partition_function_temp_pos
      (R : Set) (RIS : RealInterfaceEnhancedSetoid R)
      (S : Set) (enum : list S)
      (T : R) (T_pos : lt zero T) (z : S -> R)
      (Hne : Not (enum = nil)) :
  lt zero (@UpSigMigrate.partition_function_temp R RIS S
             (@sumd_sumf R RIS S enum) T T_pos z).
Proof.
  exact (@sumd_sum_pos R RIS S enum
           (fun s : S => exp_neg (opp (mult (inv_pos T T_pos) (z s))))
           Hne
           (fun s : S =>
              @exp_neg_pos R RIS (opp (mult (inv_pos T T_pos) (z s))))).
Qed.

(* ============ 证据：新件零外部未证假设（全 Closed） ============ *)
Print Assumptions zpi2_align1_Z_align_pos.
Print Assumptions zpi2_align2_req2_Z_align_pos.
Print Assumptions zpi2_resta_Z_align_pos.
Print Assumptions zpi2_dpo_Z_align_pos.
Print Assumptions zpi2_align3_ZAL_pos.
Print Assumptions zpi2_u2_ZAL_pos.
Print Assumptions zpi2_alignidreq_ZAL_pos.
Print Assumptions zpi2_ppoplain_Zap.
Print Assumptions zpi2_ppo_Zap.
Print Assumptions zpi2_sigmig_Z_thermo_pos.
Print Assumptions zpi2_evict_Z_thermo_pos.
Print Assumptions zpi2_iter_Z_thermo_i_pos.
Print Assumptions zpi2_gibbs_Z_thermo_r_pos.
Print Assumptions zpi2_sigmig2_Z_align_a_pos.
Print Assumptions zpi2_sigmig_partition_function_temp_pos.
