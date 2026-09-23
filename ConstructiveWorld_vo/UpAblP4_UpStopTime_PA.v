(* ============================================================ *)
(* UpAblP4_UpStopTime_PA.v —— UpStopTime 证据链姊妹验证件（战役席 P5-M，T197）        *)
(*                                                              *)
(* 母本坐标：ConstructiveWorld_Live/UpStopTime.v（889 行，Live 树只读零改）。          *)
(*   母本尾部 §7 仅有提取探针块（L886-889），无 Print Assumptions 闭合块——              *)
(*   G4 面证据链由本姊妹件以「消费性重述」补全（PA7-36 诊断支援同款：                     *)
(*   Live 只读铁律下的合规路径；母本本体入册候补块另见 T197 台账建议文案）。              *)
(*                                                              *)
(* 母本清点（T197 台账同步）：47 语句 = 38 Lemma + 1 Corollary + 8 Theorem；           *)
(*   封口 45 处 Qed + 2 处 Defined（stsearch_step_0 / stsearch_step_S——可执行            *)
(*   搜索步，提取器须吃其本体，E530 卡口径）；封口面零悬置、零假设位、零 Section；         *)
(*   母本头注「全部 Qed」按「全封口零悬置」口径读取（两件 Defined 为可执行件特例）。       *)
(*                                                              *)
(* 消费权威态：/tmp/czn14_union_full/UpStopTime.vo——源副本与 Live 源 md5 同值             *)
(*   （8089d2de374577e4d305a33e20d33242），.vo 代际（09-19 06:02）新于源（09-15 23:44），    *)
(*   无 .vos/.vok 混装；姊妹件 Require 直连消费，零重编在飞上游。                       *)
(*                                                              *)
(* 抽验口径（母本自称全封口 → 代表旗舰 + 总装 + 反面抽验三件，不逐件爆炸）：              *)
(*   旗舰  minimal_stoptime   件 3 最小停时三联证书（存在性+3a 最小性+3b 上界单调）       *)
(*   总装  st_thresh_dominance 件 4 阈值策略双目标占优的几何衰减实例化                    *)
(*   反面  unguarded_no_stoptime 件 5 无见证恒值链停时不存在（分离件）                   *)
(*   三件语句与母本逐字同形、真 Qed 收口（exact 直连母本同名件），                        *)
(*   文尾逐件 Print Assumptions 出闭合判词。                                           *)
(* 依赖清单：UpStopTime（及其传递面 CW_ConstructiveWorld_219 / UpBudgetReal /              *)
(*   UpConstitution / QArith / Lia / PeanoNat）——只读消费，原树零改，在飞席零接触。        *)
(* 红线自审：全中文表述；全件真证收口（零悬置、零假设位、零经典逻辑依赖）；                 *)
(*   编译产物只落 /tmp（Live 树与消融50 源树除本 .v 外零写入）。                          *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpBudgetReal.
Require Import UpConstitution.
Require Import UpStopTime.

(* ============================================================ *)
(* 一、旗舰消费性重述：件 3 最小停时（语句逐字同形母本 L594-600）                       *)
(* ============================================================ *)

Theorem uastp_minimal_stoptime_pa : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof. exact minimal_stoptime. Qed.

(* ============================================================ *)
(* 二、总装消费性重述：件 4 阈值策略双目标占优（语句逐字同形母本 L744-753）               *)
(* ============================================================ *)

Theorem uastp_st_thresh_dominance_pa : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof. exact st_thresh_dominance. Qed.

(* ============================================================ *)
(* 三、反面抽验消费性重述：件 5 停时不存在（语句逐字同形母本 L819-820）                  *)
(* ============================================================ *)

Theorem uastp_unguarded_no_stoptime_pa : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof. exact unguarded_no_stoptime. Qed.

(* ============================================================ *)
(* 四、文尾逐件闭合审（Print Assumptions 三连）                                    *)
(* ============================================================ *)

Print Assumptions uastp_minimal_stoptime_pa.
Print Assumptions uastp_st_thresh_dominance_pa.
Print Assumptions uastp_unguarded_no_stoptime_pa.
