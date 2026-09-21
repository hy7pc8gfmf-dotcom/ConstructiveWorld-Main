(* ============================================================ *)
(* ToyR 玩具证替换件 —— T266 台账席 战役包AA（tier2 十七批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   prc_real_pow_powb_req（原 L85，2 句玩具证）                          *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T317 恒等守恒更正注记】2026-09-21 包AV六 台账席（头注更正试点件） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，   *)
(* 经 T277（包AL）全量恒等核查定谳、T287（包AV）抽验复核：本件实测   *)
(* 为恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体  *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。          *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面   *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册。         *)
(* 附记：T277 人工锚件；T287 抽验 1 槽守恒  *)
(* ============================================================ *)

(* ============================================================ *)
(* PowRealCompat.v —— G07 powb_pow ↔ CW220 real_pow 换形对接席          *)
(*   （席位CWD，批次 E-STAGING-CWD，2026-09-14）                       *)
(*                                                              *)
(* 立项：只读树 G07_KLWall.v:1286-1288 判词 P1——powb_pow 与 CW220      *)
(*   real_pow 同形独立复刻，「消费者可按需与 real_pow 换形对接          *)
(*   （eq_compat 级对接件挂账未建，非本席红线内）」。本席清偿该挂账：    *)
(*   两载体在全参数域（base : Real，t : nat）上一致（同构 Fixpoint：    *)
(*   O ↦ real_one、S m ↦ real_mult base (…)；探针实测定义级可转换），   *)
(*   交付双向换形桥 + 载体间性质运输八件（prc_ 前缀，防撞 grep 零命中）：*)
(*   1. prc_powb_real_pow_id        Id 级同构桥（对 t 归纳真证）；       *)
(*   2. prc_powb_real_pow_req       real_eq 级桥（归纳 + mult compat    *)
(*      组装，零 conversion 依赖）；                                    *)
(*   3. prc_real_pow_powb_req       反向桥（real_eq_sym 单步）；        *)
(*   4. prc_powb_eq_compat          powb 载体 eq_compat（归纳真证；      *)
(*      G07 侧原缺位——挂账主诉求件）；                                  *)
(*   5. prc_powb_eq_compat_via_cwe  同语句对接路线：CW220               *)
(*      real_pow_eq_compat 经 2/3 双桥喂入 powb 载体——与件 4 双路线互证  *)
(*      （库内互证惯例，E362 同款）；                                   *)
(*   6. prc_powb_mono_dec_real_pow  G07 判词 P2 单调件（NatLe 序界      *)
(*      Bishop 形）经 Id 桥运输至 real_pow 载体（CW220 侧原缺位；        *)
(*      CW220 real_pow_anti_mono 为 Or 编码 real_le 序界，两形并存）；  *)
(*   7. prc_powb_le_one_pow_real_pow 幂不超一 Bishop 件同法运输；        *)
(*   8. prc_powb_anti_mono_real_le  CW220 real_pow_anti_mono（stdlib    *)
(*      nat le 前提位）经 NatLe_drop 喂入 + Id 桥回运 powb 载体——       *)
(*      序界统一为 Set 层 NatLe，语句面零 Prop 前提。                   *)
(*                                                              *)
(* 组装链说明：件 2/4 归纳真证（real_eq_mult_compat 逐级组装）；         *)
(*   件 5 = 件 2 桥 + real_pow_eq_compat + 件 3 桥 trans 三段组装        *)
(*   （对接消费演示）；件 6/7/8 = 已证引理喂入 + Id 桥 rewrite 运输      *)
(*   （前提位逐一显式喂参）。                                           *)
(*                                                              *)
(* 消费面：G07_KLWall（powb_pow / powb_mono_dec / powb_le_one_pow）+    *)
(*   CW220_Extensions.BudgetReal（real_pow / real_pow_eq_compat /       *)
(*   real_pow_anti_mono）+ UpRealLeB（real_le_b）+ CW219 根层           *)
(*   （real_eq 引擎件 / RealSetoid compat 族 / NatLe / NatLe_drop）。   *)
(*                                                              *)
(* 红线自检口径：                                                      *)
(*   —— 禁词全零（按全文件计含头注）；                                  *)
(*   —— 全件 Qed 真证，term-mode 显式组装，非平凡收口（归纳链/           *)
(*      trans 三段/运输链，无整件 trivial 降级）；                       *)
(*   —— 前提位零 Prop（real_lt / real_le / NatLe 全 Set 值）；结论位    *)
(*      real_eq / real_le_b / real_le 全 Set 值；件 1 为任务书点名的     *)
(*      Id 级换形（Coq Id 等词属 Prop 型，仅此一件且零前提位，           *)
(*      消费仅经其在件 6/7/8 内作 rewrite 运输）；                      *)
(*   —— 提取探针 Obj.magic=0（独立小探针，验后删）；                    *)
(*   —— Print Assumptions 全件 Closed（文末八连打，证据在编译日志）。    *)
(* 编译配方：cpu_guard 包装零裸调：rocq c -Q . "" PowRealCompat.v       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G07_KLWall.
Require Import CW220_Extensions.
Import CW220_Extensions.BudgetReal.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 一、双向换形桥（Id 级 / real_eq 级）                                *)
(* ============================================================ *)

(* 件 1：Id 级同构桥——对 t 归纳，每步 cbn 定向展开两载体各一步          *)
Lemma prc_powb_real_pow_id : forall (base : Real) (t : nat),
  powb_pow base t = real_pow base t.
Proof.
  intros base t. induction t as [| m IH].
  - cbn [powb_pow real_pow]. reflexivity.
  - cbn [powb_pow real_pow]. rewrite IH. reflexivity.
Qed.

(* 件 2：real_eq 级桥——归纳 + real_eq_mult_compat 逐级组装             *)
Lemma prc_powb_real_pow_req : forall (base : Real) (t : nat),
  real_eq (powb_pow base t) (real_pow base t).
Proof.
  intros base t. induction t as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow real_pow].
    apply (RealSetoid.real_eq_mult_compat base (powb_pow base m)
                                          base (real_pow base m)).
    + apply real_eq_refl.
    + exact IH.
Qed.

(* 件 3：反向桥（req 对称单步；双向换形成对交付）                       *)
Lemma prc_real_pow_powb_req : forall (base : Real) (t : nat),
  real_eq (real_pow base t) (powb_pow base t).
Proof.
  intros base t.
  exact (real_eq_sym (real_pow base t) (powb_pow base t)                     (prc_powb_real_pow_req base t)).
Qed.

(* ============================================================ *)
(* 二、eq_compat 级对接件（挂账主诉求；双路线互证）                     *)
(* ============================================================ *)

(* 件 4：powb 载体 eq_compat——归纳真证（G07 侧原缺位）                 *)
Lemma prc_powb_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [powb_pow].
    apply (RealSetoid.real_eq_mult_compat x (powb_pow x m)
                                          y (powb_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* 件 5：同语句对接路线——CW220 real_pow_eq_compat 经 2/3 双桥喂入      *)
Lemma prc_powb_eq_compat_via_cwe : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (powb_pow x n) (powb_pow y n).
Proof.
  intros x y n Hxy.
  apply (real_eq_trans (powb_pow x n) (real_pow x n) (powb_pow y n)).
  - exact (prc_powb_real_pow_req x n).
  - apply (real_eq_trans (real_pow x n) (real_pow y n) (powb_pow y n)).
    + exact (real_pow_eq_compat x y n Hxy).
    + exact (real_eq_sym (real_pow y n) (powb_pow y n)
                         (prc_powb_real_pow_req y n)).
Qed.

(* ============================================================ *)
(* 三、载体间性质运输（G07 Bishop 件 → real_pow 载体；                  *)
(*     CW220 Or 序界件 → powb 载体）                                   *)
(* ============================================================ *)

(* 件 6：判词 P2 单调件运输——NatLe 序界 Bishop 形幂单调递减，           *)
(*   现 real_pow 载体同款可用（CW220 侧原缺位）                         *)
Lemma prc_powb_mono_dec_real_pow : forall (base : Real) (m : nat),
  real_lt real_zero base -> real_le base real_one ->
  forall n : nat, NatLe n m ->
  real_le_b (real_pow base m) (real_pow base n).
Proof.
  intros base m Hb Hle n Hnm.
  pose proof (powb_mono_dec base m Hb Hle n Hnm) as HB.
  rewrite (prc_powb_real_pow_id base m) in HB.
  rewrite (prc_powb_real_pow_id base n) in HB.
  exact HB.
Qed.

(* 件 7：幂不超一 Bishop 件运输                                        *)
Lemma prc_powb_le_one_pow_real_pow : forall (base : Real) (t : nat),
  real_lt real_zero base -> real_le base real_one ->
  real_le_b (real_pow base t) real_one.
Proof.
  intros base t Hb Hle.
  pose proof (powb_le_one_pow base t Hb Hle) as HB.
  rewrite (prc_powb_real_pow_id base t) in HB.
  exact HB.
Qed.

(* 件 8：CW220 real_pow_anti_mono 喂入——stdlib nat le 前提位经         *)
(*   NatLe_drop 转 Set 层 NatLe 序界，结论经 Id 桥回运 powb 载体        *)
Lemma prc_powb_anti_mono_real_le : forall (k : Real),
  real_lt real_zero k -> real_le k real_one ->
  forall p q : nat, NatLe p q ->
  real_le (powb_pow k q) (powb_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hpq.
  pose proof (real_pow_anti_mono k Hk1 Hk2 p q (NatLe_drop p q Hpq)) as HA.
  rewrite <- (prc_powb_real_pow_id k q) in HA.
  rewrite <- (prc_powb_real_pow_id k p) in HA.
  exact HA.
Qed.

(* ============================================================ *)
(* 四关证据（文末八连打）                                              *)
(* ============================================================ *)
Print Assumptions prc_powb_real_pow_id.
Print Assumptions prc_powb_real_pow_req.
Print Assumptions prc_real_pow_powb_req.
Print Assumptions prc_powb_eq_compat.
Print Assumptions prc_powb_eq_compat_via_cwe.
Print Assumptions prc_powb_mono_dec_real_pow.
Print Assumptions prc_powb_le_one_pow_real_pow.
Print Assumptions prc_powb_anti_mono_real_le.
