(* LW3CarrierFull.v                                                   *)
(* 使命：Real 半边全清接载——carrier 双前提（kills 位＋eps 选取位）全消，   *)
(*      产出使用侧零非条件前提的全清件（p(e)=0 为诚实条件前件，(c) 段裁决    *)
(*      条件永久化，不在本件辖内）。                                         *)
(* 路线：398 kills 闭合＋402 支 1 接载序四步——①eps' := projT1               *)
(*      (cauchy_real_exp_pos (real_const X))（S03 L6442 在件直连，显式正     *)
(*      有理）；②Heps' := fst (projT2 ...)（And=A*B 定义面投影，402          *)
(*      PROJ1-ANDDEF 病灶处方：fst/snd 非 proj1/proj2）；③半值化            *)
(*      eps := eps'/2（qltT_div_pos＋qltT_0_2，eslot L160-163 同款，严格     *)
(*      余量）；④tlw398_carrier_discharge X eps Hhalf 产 real_lt 见证。      *)
(* 对接：tlw408_carrier_fulldischarge（X 泛型零前提）供给 399 C4 的 E-槽     *)
(*      gap 前件位（tlw399_c4_full_cond1 第三前件 lw3_qnz(exp_L…) 的供给链   *)
(*      上游）；tlw408_realcarrier_fulldischarge＝原 realcarrier 消 kills    *)
(*      ＋eps 两前提后的单条件形（p(e)=0 逐字保留）。                        *)
(* 构造性：语句面全 Set（QltT Id-bool 形、real_lt/real_eq 数据形、sigT）；   *)
(*      构造性红线四条全守（零公理零假设承载位）；等词面仅证明体内；全装配  *)
(*      走库件引理 exact 级组合（NOEVALIFT：零 eval 级拼接）。终形名位全    *)
(*      tlw408_ 前缀避占名位；^Theorem lw3_ 计 0＝诚实态（GAPASUME          *)
(*      REGEXGATE 口径）。                                                  *)
(* 编译配方：SW2 双 export COQLIB/ROCQLIB 全字面；coqc -q -Q . '""' -Q      *)
(*      ConstructiveWorld_vo '""'；cpu_guard 包裹（398 配方承继）。          *)
(* 依赖：Stdlib QArith/Lia/Arith/ZArith/List＋S01_BaseRing/S02_CauchyComplete/S03_QExp＋LW0QPoly/LW1ZPoly/LW2Hermite/LW2IntegMachine/LW0FactGrowth/LW2UpperBound/LW2NivenInt/LW3ETranscendental/LW3ESlot/LW3Kills。 *)
(* 对标：carrier 全清承载件（p(e)=0 为诚实条件前件，(c) 段裁决条件永久化）。 *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW1ZPoly.
Require Import LW0FactGrowth.
Require Import LW2Hermite.
Require Import LW2IntegMachine.
Require Import LW3ETranscendental.
Require Import LW3ESlot.
Require Import LW3Kills.
(* LW1ZPoly opens Z_scope at file level and the open leaks through the      *)
(* Require chain, so the bare numeral default would land on Z; reopen the   *)
(* rational scope for this file (399/387 prescription).  Every nat and Z    *)
(* occurrence carries an explicit scope annotation, so no reading changes.  *)
Local Open Scope Q_scope.

(* ===== 0. 链上引理可见性勘形（PROBEFIRST：首炮随件留存签名铁据） ===== *)

Check cauchy_real_exp_pos.
Check tlw383_eslot_carrier.
Check tlw383_eslot_realcarrier.
Check tlw398_carrier_discharge.
Check qltT_div_pos.
Check qltT_0_2.
Check (fun x : Real => fst (projT2 (cauchy_real_exp_pos x))).
Check real_lt.

(* ===== 1. eps 选取位显式数据形（402 支 1 第 1-3 步落装） ===== *)

(* eps 选取：e^X 的显式正有理下界之半。projT1 (cauchy_real_exp_pos …) 是    *)
(* real_lt 的 sigT 结构投影（数据形，零公理），半值化留严格余量：下游       *)
(* e − |e − EQ| > eps' − eps'/2 > 0 的转移由该余量支撑（402 §四支 1）。     *)
Definition tlw408_eps_pick (X : Q) : Q :=
  projT1 (cauchy_real_exp_pos (real_const X)) / 2.

Lemma tlw408_eps_pick_pos : forall X : Q, QltT 0 (tlw408_eps_pick X).
Proof.
  intros X. unfold tlw408_eps_pick.
  apply (qltT_div_pos (projT1 (cauchy_real_exp_pos (real_const X))) 2).
  - exact (fst (projT2 (cauchy_real_exp_pos (real_const X)))).
  - exact qltT_0_2.
Qed.

(* ===== 2. carrier 全清件：X 泛型零非条件前提 ===== *)

(* 原 carrier 使用侧（tlw383_eslot_carrier 的 sigT real_lt 结论面）在      *)
(* kills 位（tlw398_kills）与 eps 选取位（tlw408_eps_pick_pos）双前提全消   *)
(* 后的零前提供给形。装配＝单步 exact（tlw398_carrier_discharge 已消        *)
(* kills 位，本件再消 eps 位），零新分析件、零 eval 级拼接。                *)
Theorem tlw408_carrier_fulldischarge : forall X : Q,
  sigT (fun M : nat =>
    real_lt (real_metric (cauchy_real_exp (real_const X))
                          (real_const (tlw383_EQ X M)))
            (real_const (tlw408_eps_pick X))).
Proof.
  intros X.
  exact (tlw398_carrier_discharge X (tlw408_eps_pick X)
           (tlw408_eps_pick_pos X)).
Qed.

(* 见证抽取数据形：M 门槛为 X 的显式可计算函数（G3 提取并集，魔数双零预期   *)
(* 承 398 tlw398_kills_M 同款口径）。                                       *)
Definition tlw408_carrier_M (X : Q) : nat :=
  projT1 (tlw408_carrier_fulldischarge X).

(* ===== 3. 实侧装配：原 realcarrier 消双前提后的单条件形 ===== *)

(* p(e)=0 为诚实条件前件逐字保留（(c) 段裁决条件永久化；本前件在全清件      *)
(* 装配中不被使用——carrier 见证产出与 p(e)=0 无关，该前件供下游            *)
(* apartness/非零转移使用——394 案丙条件面同款口径）。                       *)
Theorem tlw408_realcarrier_fulldischarge : forall (p : zpoly) (Nn : nat),
  real_eq (lw3_evalr p lw3_e) real_zero ->
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (lw3_nodecount p Nn))) M)))
            (real_const (tlw408_eps_pick
               (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))))).
Proof.
  intros p Nn Hpzero.
  exact (tlw408_carrier_fulldischarge
          (- lw2_node (Datatypes.S (lw3_nodecount p Nn)))).
Qed.

(* ===== 4. 锚例钉：X := -node 2 处零前提产出实距 < e^{-2}/2 之界 ===== *)

(* 非空洞性机械钉：全清件在锚例上零前提直接产出 M 见证与实距离被显式正量    *)
(* 压制（eps 选取全自动，与 398 锚例的手选 eps := 1 位对照）。              *)
Theorem tlw408_anchor_fulldischarge :
  sigT (fun M : nat =>
    real_lt (real_metric
               (cauchy_real_exp
                  (real_const (- lw2_node (Datatypes.S (Datatypes.S O)))))
               (real_const (tlw383_EQ
                  (- lw2_node (Datatypes.S (Datatypes.S O))) M)))
            (real_const (tlw408_eps_pick
               (- lw2_node (Datatypes.S (Datatypes.S O)))))).
Proof.
  exact (tlw408_carrier_fulldischarge
          (- lw2_node (Datatypes.S (Datatypes.S O)))).
Qed.

(* ===== 5. 假设面与提取检核（G3 数据名并集） ===== *)

Print Assumptions tlw408_carrier_fulldischarge.
Print Assumptions tlw408_realcarrier_fulldischarge.
Print Assumptions tlw408_anchor_fulldischarge.

From Stdlib Require Import Extraction.
Separate Extraction tlw408_carrier_M.
