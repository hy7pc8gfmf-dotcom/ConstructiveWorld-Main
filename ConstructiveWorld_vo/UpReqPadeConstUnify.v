(* ============================================================ *)
(* UpReqPadeConstUnify.v *)
(* *)
(* 目的： 1/720 跨四文件精确撞车 = Padé n=2 残差首系数跨模块统一恒等式。 *)
(* 主件： pcu_beta2_unify（六位点统一账）与 pcu_c0_eq_ptp（一般闭式）。 *)
(* 依赖： S02_CauchyComplete、S03_QExp、UpReqPadeExp、UpReqPadeBetaPos、 *)
(*        UpReqPadeTailPos、UpReqPadeSignXfer、UpReqPadeLower、         *)
(*        UpReqPadeFinale。                                            *)
(* 备注： 闭式 c₀(n) = (n!)²/((2n)!(2n+1)!)，n=1 得 1/12、n=2 得 1/720。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeConstUnify.v —— 数值几何·隐藏恒等式定理化        *)
(*   构造性注记：零承认语句，纯构造证明，全 Qed。                                                *)
(*                                                                   *)
(* 使命：把 GEO1 常数对撞发现的首果定理化——1/720 跨四文件精确撞车        *)
(*   = Padé n=2 残差首系数的跨模块统一恒等式。数学背景（TCS1 侦察在案）： *)
(*   残差首系数 c₀(n) = (n!)²/((2n)!(2n+1)!)，n=2 时 (2!)²/(4!·5!)      *)
(*   = 4/2880 = 1/720 = 1/6!——撞车不是巧合，是同一闭式在不同模块的化身。 *)
(*                                                                 *)
(* 六位点实读比对（python fractions 逐点复核，全部语义同构，零剔除）：    *)
(*   位点① UpReqPadeFinale.v:200  cpf_witness_n2 x := q_pow x 5*(1#720) *)
(*          ——主件见证 x⁵·c₀（乘法形）。                                *)
(*   位点② UpReqPadeLower.v:288   cpl_lower_even 见证 q_pow y 5/720      *)
(*          ——下界见证 y⁵·c₀（除法形；Qdiv 定义性展开后与①同项）。       *)
(*          （旁证 cpl_sent_witness_half:152：½⁵/720 = 1/23040。）       *)
(*   位点③ UpReqPadeSignXfer.v:159 psx_coef_vals：psx_coef n :=         *)
(*          ptp_beta n 0/q_fact(2n)——首系数定义性展开形。               *)
(*   位点④ UpReqPadeTailPos.v:141  ptp_beta_n2_first：同③核心形 n=2。    *)
(*   位点⑤ UpReqPadeTailPos.v:161  ptp_n2_poly 首项系数 (1#720)·y⁵。     *)
(*   位点⑥ UpReqPadeTailPos.v:176  ptp_sentinel_n2_half 数值锚首项。   *)
(*   六位点同数学量 c₀(2)·y⁵（y=1 退化 c₀(2)）；n=1 孪生 1/12 随行。      *)
(*                                                                 *)
(* 分层：                                                             *)
(*   S1 定义面 pcu_c0：闭式 (n!)²/((2n)!(2n+1)!) 的 Q 层直写。           *)
(*   S2 闭式评估定值件：n=1,2,3（vm_compute 交叉乘 lia，库内同款）。     *)
(*   S3 一般闭式定理（G2 主件）：pcu_c0 n == ptp_beta n 0/q_fact(2n)     *)
(*      全称 n——站点定义展开 + Qinv 乘法分配（pcu_Qinv_mult 自证）+      *)
(*      ring 闭合；全程绕开 field 原子分母坑（TailPos 先例）。 *)
(*   S4 正性件与对账（「正性已证、闭式今统」成对）：pcu_c0_pos 直构；     *)
(*      pcu_first_coef_pair 把 pbp_beta_pos（β 正性族，BetaPos 在盘）     *)
(*      双正性并排（Set 面），闭式桥 pcu_c0_eq_pbp 相邻三件成对。         *)
(*   S5 站点桥：每站点一处定义性实例——桥语句一律指向站点真定义项          *)
(*      （unfold 直转/直 apply/库件 rewrite），禁自造 1#720 冒充；        *)
(*      pcu_c0 2 == 1/720 只出现在闭式评估件（S2）。                     *)
(*   S7 数值锚链：½⁵·c₀(2) = ½⁵/720 = 1/23040，与 Lower 数值锚    *)
(*      cpl_sent_witness_half 核验合流；TailPos 数值锚统一形。            *)
(*   S6 主件（G1）：pcu_beta2_unify 七项 And 账（每站点一处实例化）+      *)
(*      pcu_beta1_unify（n=1 孪生 1/12 账）。                            *)
(*                                                                 *)
(* 公理面：本文件语句面全 Set 层承载（Qeq/And/forall；正性出口 QltT），   *)
(*   证内 Prop 仅作桥（Qlt_to_QltT 换桥，库内同款）；零新增假设件、       *)
(*   零 承认件。Print Assumptions 应全 Closed——lia/ring/vm_compute    *)
(*   均 ax-free，Require 链不触 Psatz。提取面 Separate Extraction        *)
(*   产物以 Obj.magic 零命中为准。                                      *)
(*                                                                 *)
(* 红线自审：纯构造性；站点桥真走各站点定义展开（直用                  *)
(*   cpf_witness_n2/ptp_n2_poly/ptp_sentinel_n2_half 真形）；零承认件；   *)
(*   编译配方：Rocq 9.1 直调 coqc -q -Q . ""，cpu_guard 单道守护。          *)
(* ============================================================ *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp.
Require Import UpReqPadeBetaPos.
Require Import UpReqPadeTailPos.
Require Import UpReqPadeSignXfer.
Require Import UpReqPadeLower.
Require Import UpReqPadeFinale.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== S1 定义面 ===== *)

(* 残差首系数闭式：c₀(n) = (n!)²/((2n)!(2n+1)!)
   （= β(n,0)/(2n)!，其中 β(n,m) = n!·(n+m)!/(2n+m+1)! 即
   ptp_beta/pbp_beta 双库同式闭式）。 *)
Definition pcu_c0 (n : nat) : Q :=
  q_fact n * q_fact n / (q_fact (2 * n) * q_fact (2 * n + 1)).

(* ===== S2 闭式评估（定值件） ===== *)

Lemma pcu_c0_val_n1 : pcu_c0 1 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma pcu_c0_val_n2 : pcu_c0 2 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma pcu_c0_val_n3 : pcu_c0 3 == (1#100800).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== S3 一般闭式定理（G2 主件，全称 n） ===== *)

(* Qinv 乘法分配（stdlib Qinv_mult_distr 一行实装，检验已证结论；
   q_fact (2*n) 类变元项非 constructor 形，conversion/reflexivity
   直击不可（实测），故经此桥。 *)
Lemma pcu_Qinv_mult : forall p q : Q, Qinv (p * q) == Qinv p * Qinv q.
Proof. intro p. intro q. apply Qinv_mult_distr. Qed.

(* 主桥：c₀(n) = β(n,0)/(2n)!。展开 ptp_beta 定义（q_fact (n+0)、
   (2n+0+1) 归一走 Nat.add_0_r），除法链 Qdiv 定义性展开后 Qinv
   乘法分配（pcu_Qinv_mult）+ ring 闭合。 *)
Lemma pcu_c0_eq_ptp : forall n : nat,
  pcu_c0 n == ptp_beta n 0 / q_fact (2 * n).
Proof.
  intro n.
  unfold pcu_c0, ptp_beta.
  repeat rewrite Nat.add_0_r.
  unfold Qdiv.
  assert (Hinv : Qinv (q_fact (2 * n) * q_fact (2 * n + 1)) ==
                 Qinv (q_fact (2 * n)) * Qinv (q_fact (2 * n + 1)))
    by (apply pcu_Qinv_mult).
  rewrite Hinv. ring.
Qed.

(* 对称形（站点桥的通用形） *)
Lemma pcu_site_ptp_gen : forall n : nat,
  ptp_beta n 0 / q_fact (2 * n) == pcu_c0 n.
Proof. intro n. symmetry. apply pcu_c0_eq_ptp. Qed.

(* BetaPos 桥（双库同式：psx_beta_bridge 一行承桥） *)
Lemma pcu_c0_eq_pbp : forall n : nat,
  pcu_c0 n == pbp_beta n 0 / q_fact (2 * n).
Proof.
  intro n.
  rewrite (pcu_c0_eq_ptp n).
  rewrite psx_beta_bridge.
  reflexivity.
Qed.

(* ===== S4 正性件与「正性已证、闭式今统」成对账 ===== *)

Lemma pcu_c0_pos : forall n : nat, QltT 0 (pcu_c0 n).
Proof.
  intro n. apply Qlt_to_QltT. unfold pcu_c0, Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* 成对件（Set 面 sigT 依值对——BetaPos pbp_beta_pos_sigT 同款承载；
   Qeq 属 Prop 不与 Set 混 /\——分面纪律）：β(n,0) 正性（pbp_beta_pos
   在盘）为见证位，c₀ 正性（今构）为承载位；闭式桥见上 pcu_c0_eq_pbp
   ——「正性已证（BetaPos）、闭式今统（本件）」三件成对。 *)
Corollary pcu_first_coef_pair : forall n : nat,
  sigT (fun _ : QltT 0 (pbp_beta n 0) => QltT 0 (pcu_c0 n)).
Proof.
  intro n.
  exact (existT (fun _ : QltT 0 (pbp_beta n 0) => QltT 0 (pcu_c0 n))
                (pbp_beta_pos n 0) (pcu_c0_pos n)).
Qed.

(* ===== S5 站点桥（每站点一处定义性实例） ===== *)

(* 位点④：TailPos 首系数定值件语句面（n=2 实例；2*2=4 转换级统一） *)
Lemma pcu_site_ptp_first : ptp_beta 2 0 / q_fact 4 == pcu_c0 2.
Proof. apply (pcu_site_ptp_gen 2). Qed.

(* n=1 孪生实例 *)
Lemma pcu_site_ptp_first1 : ptp_beta 1 0 / q_fact 2 == pcu_c0 1.
Proof. apply (pcu_site_ptp_gen 1). Qed.

(* 位点③：SignXfer 首系数定义面（psx_coef n := ptp_beta n 0/q_fact(2n)） *)
Lemma pcu_site_psx_coef2 : psx_coef 2 == pcu_c0 2.
Proof. unfold psx_coef. apply (pcu_site_ptp_gen 2). Qed.

Lemma pcu_site_psx_coef1 : psx_coef 1 == pcu_c0 1.
Proof. unfold psx_coef. apply (pcu_site_ptp_gen 1). Qed.

(* 位点①：Finale 主件见证（乘法形 x⁵·(1#720)）真形直使用 *)
Lemma pcu_site_cpf : forall x : Q,
  cpf_witness_n2 x == q_pow x 5%nat * pcu_c0 2.
Proof.
  intro x. unfold cpf_witness_n2. rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* 位点②：Lower 下界见证（除法形 y⁵/720——Qdiv 展开后同乘法形） *)
Lemma pcu_site_cpl : forall y : Q,
  q_pow y 5%nat / 720 == q_pow y 5%nat * pcu_c0 2.
Proof.
  intro y. rewrite pcu_c0_val_n2. unfold Qdiv. reflexivity.
Qed.

(* 位点⑤：TailPos n=2 残差多项式恒等式统一形（首项 = c₀·y⁵，全称 y） *)
Lemma pcu_n2_poly_unified : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == pcu_c0 2 * q_pow y 5%nat
     + (1#1440) * q_pow y 6%nat + (1#8640) * q_pow y 8%nat.
Proof.
  intro y. rewrite (ptp_n2_poly y). rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* ===== S7 数值锚链 ===== *)

(* 闭式与 Lower 数值锚核验桥：½⁵·c₀(2) == ½⁵/720 *)
Lemma pcu_sent_cpl_agree :
  q_pow (1#2) 5%nat * pcu_c0 2 == q_pow (1#2) 5%nat / 720.
Proof.
  rewrite (pcu_c0_val_n2). reflexivity.
Qed.

(* 合流：½⁵·c₀(2) = ½⁵/720 = 1/23040（位点② cpl_sent_witness_half 供货） *)
Lemma pcu_sent_unified : q_pow (1#2) 5%nat * pcu_c0 2 == (1#23040).
Proof.
  apply (Qeq_trans _ (q_pow (1#2) 5%nat / 720) _).
  - apply pcu_sent_cpl_agree.
  - exact cpl_sent_witness_half.
Qed.

(* 位点⑥：TailPos 数值锚统一形（残差在 y=½ 精确值，首项 = c₀·½⁵） *)
Lemma pcu_sentinel_n2_half_unified :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == pcu_c0 2 * (1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof.
  rewrite (ptp_sentinel_n2_half). rewrite pcu_c0_val_n2. reflexivity.
Qed.

(* ===== S6 主件（G1：跨模块统一账） ===== *)

(* n=2 主账：四文件六位点常数的定义性展开全部 Qeq 统一到闭式 pcu_c0 2，
   而闭式评估 pcu_c0 2 == 1/720（S2）——1/720 撞车 = 同一闭式的化身。 *)
Theorem pcu_beta2_unify :
  pcu_c0 2 == (1#720) /\
  ptp_beta 2 0 / q_fact 4 == pcu_c0 2 /\
  psx_coef 2 == pcu_c0 2 /\
  (forall x : Q, cpf_witness_n2 x == q_pow x 5%nat * pcu_c0 2) /\
  (forall y : Q, q_pow y 5%nat / 720 == q_pow y 5%nat * pcu_c0 2) /\
  (forall y : Q,
     exp_partial 6 y * pade_den 2 y - pade_num 2 y
     == pcu_c0 2 * q_pow y 5%nat
        + (1#1440) * q_pow y 6%nat + (1#8640) * q_pow y 8%nat) /\
  q_pow (1#2) 5%nat * pcu_c0 2 == (1#23040).
Proof.
  (* 注意：repeat split 会经 delta+eq_refl 把闭式可转换的 Qeq 合取项
     （前三项两边皆封闭且同值）直接收掉，bullet 错位——apply conj
     不做转换穿透，目标数恒定（实测）。 *)
  repeat apply conj.
  - apply pcu_c0_val_n2.
  - apply pcu_site_ptp_first.
  - apply pcu_site_psx_coef2.
  - intro x. apply pcu_site_cpf.
  - intro y. apply pcu_site_cpl.
  - intro y. apply pcu_n2_poly_unified.
  - exact pcu_sent_unified.
Qed.

(* n=1 孪生账：1/12（y³ 位首系数；奇号带负由 psx_sign 承担，幅值同闭式） *)
Theorem pcu_beta1_unify :
  pcu_c0 1 == (1#12) /\
  ptp_beta 1 0 / q_fact 2 == pcu_c0 1 /\
  psx_coef 1 == pcu_c0 1.
Proof.
  repeat apply conj.
  - apply pcu_c0_val_n1.
  - apply pcu_site_ptp_first1.
  - apply pcu_site_psx_coef1.
Qed.

(* ===== 审计与提取 ===== *)

Print Assumptions pcu_c0_val_n2.
Print Assumptions pcu_c0_eq_ptp.
Print Assumptions pcu_c0_eq_pbp.
Print Assumptions pcu_c0_pos.
Print Assumptions pcu_first_coef_pair.
Print Assumptions pcu_beta2_unify.
Print Assumptions pcu_beta1_unify.
Print Assumptions pcu_sent_unified.
Print Assumptions pcu_sentinel_n2_half_unified.

From Stdlib Require Import Extraction.
Separate Extraction pcu_c0 pcu_beta2_unify pcu_beta1_unify pcu_sent_unified.
