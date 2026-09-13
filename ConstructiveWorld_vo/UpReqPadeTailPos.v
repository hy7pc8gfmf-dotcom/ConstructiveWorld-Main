(* ============================================================ *)
(* UpReqPadeTailPos.v —— 席C-T1a：Padé 正尾恒等式主件（C 路闭合     *)
(*                        主轨第一切片，Set 层承重墙）               *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 使命（修正令对表后）：把 S3/S1 数值实锤的「有限 Q 前缀 × 符号因子  *)
(*   (−1)^n × 正系数级数」余项恒等式落成 Set 层 Coq 件。             *)
(*   符号面勘误（C-T1a 修正令 20260914）：尾系数符号 = (−1)^n，      *)
(*   非恒正——本件语句全部显式携带符号因子（n=1 切片为 −(1#2)，      *)
(*   n=2 实例为正号），β_m 本身的全正闭式单独成件（ptp_beta_pos）。  *)
(*                                                                 *)
(* 主件降档（诚实标注，60 分钟预算 + 平台损伤双重止损）：
   ptp_tail_series 全称形（n=1、∀N≥3、∀y）归纳骨架已完备设计——
   归纳步合并恒等式 β_m/m! == 1/(m+2)! − 2/(m+3)!（q_fact 链展开后
   为 q_fact m 的多项式恒等式，ring 可收）；但主步收口需 field 于
   「原子分母」目标，实测本平台 9.0 的 field 对原子分母一律报
   not a valid field equation（最小复现见 E-STAGING-CT1A 卡），
   E268/E293「归一再 field」教义已用尽（目标已纯环项仍炸）。
   交叉相乘 + 乘法消去路线挂账下一席（骨架见交付报告）。            *)
(*                                                                 *)
(* 降档声明（诚实标注）：                                             *)
(*   ① 主件为 n=1 切片的全称 N 形；全称 n 的逐项系数等式（柯西积      *)
(*      重排 + 配对引理）未及落盘，挂账下一席（S1 报告已给配对比值    *)
(*      (n−2j)/((2n−2j)(2j+1)) ≤ 1/2 的正性路线）。                  *)
(*   ② n=2 仅交付截断多项式实例恒等式（S1 定值变体同构），非全称 N。  *)
(*   ③ 平台损伤实锤：field 原子分母全拒（E268/E293 归一教义不适用，  *)
(*      新坑沉淀 E-STAGING-CT1A 卡）；④ 语句面等式用 Qeq（库内        *)
(*      UpReqPadeExp 同款先例）；正性语句面     *)
(*      一律 QltT（Set 层），证内 Prop 仅作桥（Qlt_to_QltT）。        *)
(*                                                                 *)
(* 消费面：S03_QExp（exp_partial/q_pow/q_fact/sum_upto/q_fact_pos/    *)
(*   q_neq_of_lt）、UpReqPadeExp（pade_coeff/pade_num/pade_den）、    *)
(*   S02_CauchyComplete（QltT/Qlt_to_QltT）。                        *)
(*                                                                 *)
(* 公理面自审：本件不新增任何公理依赖，全部结论构造性直证；四关审计    *)
(*   以 Print Assumptions = Closed 与提取产物 Obj.magic 零命中为准。   *)
(*                                                                 *)
(* 编译配方（温控协议，cpu_guard CoreN 1）：                          *)
(*   秒审: coqc -vos -Q . "" UpReqPadeTailPos.v                      *)
(*   全量: coqc -Q . "" UpReqPadeTailPos.v                           *)
(*   G4  : coqchk -Q . "" -o UpReqPadeTailPos                        *)
(* ============================================================ *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== 定义面 ===== *)

(* β_m = n!·(n+m)!/(2n+m+1)!——S3 探针 beta_term 同式，全正闭式 *)
Definition ptp_beta (n m : nat) : Q :=
  q_fact n * q_fact (n + m) / q_fact (2 * n + m + 1).

(* 带符号正尾前缀：Σ_{m=0}^{M} β_m·y^{2n+1+m}/m!（幂次在项内） *)
Definition ptp_beta_prefix (n M : nat) (y : Q) : Q :=
  sum_upto (Datatypes.S M)
    (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)).

(* ===== 小引擎 ===== *)

(* sum_upto 尾部展开：定义性（sum_upto (S K) f = sum_upto K f + f K） *)
Lemma ptp_sum_S : forall (K : nat) (f : nat -> Q),
  sum_upto (Datatypes.S K) f == sum_upto K f + f K.
Proof. intro K. intro f. reflexivity. Qed.

(* 前缀步进：prefix (S M) = prefix M + f (S M) *)
Lemma ptp_prefix_S : forall (n M : nat) (y : Q),
  ptp_beta_prefix n (Datatypes.S M) y ==
  ptp_beta_prefix n M y +
  (ptp_beta n (Datatypes.S M) / q_fact (Datatypes.S M)
     * q_pow y (2 * n + 1 + Datatypes.S M)).
Proof.
  intros n M y. unfold ptp_beta_prefix.
  rewrite (ptp_sum_S (Datatypes.S M)
             (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m))).
  reflexivity.
Qed.

(* Q₁(y) = 1 − y/2、P₁(y) = 1 + y/2（系数闭式展开） *)
Lemma ptp_den1 : forall y : Q, pade_den 1 y == 1 + - (1#2) * y.
Proof.
  intro y. unfold pade_den, pade_coeff. cbn. field.
Qed.

Lemma ptp_num1 : forall y : Q, pade_num 1 y == 1 + (1#2) * y.
Proof.
  intro y. unfold pade_num, pade_coeff. cbn. field.
Qed.

(* ===== 正性件（全称 n,m，Set 层 QltT 出口） ===== *)

Theorem ptp_beta_pos : forall (n m : nat), QltT 0 (ptp_beta n m).
Proof.
  intros n m. apply Qlt_to_QltT.
  unfold ptp_beta. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ===== β 哨兵族（S3 探针 fractions 精确对表） ===== *)

Lemma ptp_beta_n1_0 : ptp_beta 1 0%nat == (1#6).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_1 : ptp_beta 1 1%nat == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_2 : ptp_beta 1 2%nat == (1#20).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_3 : ptp_beta 1 3%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_4 : ptp_beta 1 4%nat == (1#42).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_0 : ptp_beta 2 0%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_1 : ptp_beta 2 1%nat == (1#60).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_2 : ptp_beta 2 2%nat == (1#105).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* 首项闭式实例：(n!)^2/((2n)!(2n+1)!)——n=1 得 1/12（y^3 位首系数
   带 (−1)^1 符号），n=2 得 1/720（y^5 位首系数偶号正），与修正令②对表 *)
Lemma ptp_beta_n1_first : ptp_beta 1 0%nat / q_fact 2 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_first : ptp_beta 2 0%nat / q_fact 4 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 保底件一：n=1 截断多项式恒等式（全称 y） =====
   系数 −1/12, −1/24 与全级数 −β_m/(2!·m!) 精确对表（m=0,1），
   y^5 项 −1/48 为 exp_partial 4 的截断窄条。 *)
Lemma ptp_n1_poly : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12)*q_pow y 3 + (1#24)*q_pow y 4 + (1#48)*q_pow y 5).
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 保底件二：n=2 偶号正尾实例（S1 g2_poly 同款，全称 y） =====
   十个 Padé 匹配条件（y^0..y^4 系数全零）由右端无低次项读出；
   y^7 系数恰零（右端无 y^7 项）；首项 y^5/720 = (2!)^2/(4!·5!)。 *)
Lemma ptp_n2_poly : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == (1#720)*q_pow y 5 + (1#1440)*q_pow y 6 + (1#8640)*q_pow y 8.
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 数值哨兵（y = 1/2 对账；vm_compute + Qeq 交叉乘 lia） ===== *)

Lemma ptp_sentinel_n1_half :
  exp_partial 4 (1#2) * pade_den 1 (1#2) - pade_num 1 (1#2) == - (7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_sentinel_n2_half :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == (1#720)*(1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 审计与提取 ===== *)

Print Assumptions ptp_beta_pos.
Print Assumptions ptp_n1_poly.
Print Assumptions ptp_n2_poly.

From Stdlib Require Import Extraction.
Separate Extraction ptp_beta_pos ptp_beta ptp_beta_prefix
  ptp_n1_poly ptp_n2_poly.
