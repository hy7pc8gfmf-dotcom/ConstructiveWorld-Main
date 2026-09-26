(* ============================================================ *)
(* ToyR 玩具证替换件 —— T266 台账席 战役包AA（tier2 十七批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   p12_param_k1（原 L130，2 句玩具证）                                  *)
(* ============================================================ *)
(* ============================================================ *)
(* 【T330 恒等守恒更正注记】2026-09-22 包AW十 台账席（恒等头注更正全量第三批）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 T277（包AL）全量恒等核查已证结论、T317（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 1 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此更正。                                        *)
(* 更正口径：真替换 0 槽＋恒等守恒 1 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；台账承载见 T277 附录／T284 修正块／T317 评估册／T321／T330 台账。                   *)
(* 附记：T277 判级全文恒等；包AA A-L 包域（AA/AB/AC/AD）第三批整批直推（T317 六·1 方案①）         *)
(* ============================================================ *)

(* ============================================================ *)
(* Paper12345Sample.v —— 席 P67B（E-STAGING-P67B）T56 样例件        *)
(*   论文5 §5.2「诚实边界（遗留登记）」可消融 B 类首步施工件：         *)
(*   定理 5.2（cec_kernel_coef）一般 k 形的参数化恒等式               *)
(*     cec_r6_s k v == k·v + bcoef k·v² + v³·w                       *)
(*   在库内是【显式假设】（仅 k=1 无条件全闭 cec_r6_param_k1）。        *)
(*   本件把它升为【一般 k 无条件存在形】：w 显式给出。                 *)
(*                                                                *)
(*   纪律：前缀 p12_；自足定义（正本对照 ConstructiveWorld_Live/       *)
(*   UpReqEngineCeiling.v 的 cec_r6_s/cec_r6_bcoef/cec_r6_coef）；      *)
(*   零 公理/承认件/参数；普查席禁编译——本件未过四关，          *)
(*   接续席按交接文档 §3.1 模板补跑 G1-G4（-Q vo_901 单根）。           *)
(*                                                                *)
(* 【CZD10 勘误注记 20260918·跳件登记】本件 p12_mul_neq0 证明面为        *)
(*   结构性错稿（语句面 eq / 证明面 Qeq 两面不同构），3 轮跳件。        *)
(* 【CYE12 修证 20260918】p12_mul_neq0 第 4 轮按 Z 层注入级重构闭合；    *)
(*   p12_div_cancel 已证结论为语句面语义假（见该引理注记），跳件。          *)
(* 【CZD13 修证定稿 20260918】:85 真错件手修完成——                    *)
(*   ① p12_div_cancel 语句面维修：原 Leibniz 面 `a <> 0` 语义为假      *)
(*     （反例 a := Qmake 0 2：Leibniz 非 0 但 Qeq 为 0，此时 /a == 0，  *)
(*     左端 == 0 ≠ x），重述为 Qeq 面 `~ a == 0` 真前提（非改弱）；      *)
(*   ② :85 双因已证结论：Qmult_assoc 方向（LHS 右结合 vs 目标左结合）        *)
(*     + Qmult_inv_r 9.1 实形为单参 `x * / x == 1`（双参形不存在）；     *)
(*   ③ 主件证体重构：Qeq_dec 双分支——Qeq 零支 w := 0（p12_s == 0），    *)
(*     非零支除法消去真支 + ring 闭合；定理语句面零改动；               *)
(*   ④ 检验件 /tmp/czd13_side/probe0-2.v 全构件官编实测先行已证结论。       *)
(* ============================================================ *)

From Stdlib Require Import QArith_base Qring.

(* ---- 自足定义（与 UpReqEngineCeiling.v 逐位对照） ---- *)

Fixpoint p12_qpow (x : Q) (n : nat) : Q :=
  match n with
  | O => 1%Q
  | S m => p12_qpow x m * x
  end.

(* R6 族核：s = 1/(1-v)^k - 1 *)
Definition p12_s (k : nat) (v : Q) : Q := (1 # 1) / p12_qpow (1 - v) k - (1 # 1).

(* 族参数 b = k(k+1)/2 *)
Definition p12_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).

(* 指纹系数 (k+1)/(2k) *)
Definition p12_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

(* ---- 支撑引理（Q 层除法消去，自足） ---- *)

Lemma p12_mul_neq0 : forall a b : Q, a <> 0 -> b <> 0 -> a * b <> 0.
Proof.
  (* CYE12 重构 20260918（第4轮，终）：按 CZD10 头注「Z 层注入级重构」路线。
     语句面 <> 是表示级 eq（记录 Leibniz），证明体弃 Qeq(==) 面 tactic，
     改纯 Z 层：destruct 拆 Qmake → injection 分量等式 → positive 单位
     9 情形 discriminate 收敛 ad=bd=1 → Z.mul_eq_0 闭合。 *)
  intros a b Ha Hb Hab.
  destruct a as [an ad]; destruct b as [bn bd]; simpl in *.
  injection Hab as H1 H2.
  destruct ad; destruct bd; simpl in *; try discriminate.
  assert (Han : an <> 0%Z) by (intro Hz; apply Ha; rewrite Hz; reflexivity).
  assert (Hbn : bn <> 0%Z) by (intro Hz; apply Hb; rewrite Hz; reflexivity).
  apply Z.mul_eq_0 in H1.
  destruct H1 as [H1 | H1].
  - apply Ha. rewrite H1. reflexivity.
  - apply Hb. rewrite H1. reflexivity.
Qed.

(* 【CZD13 语句面维修登记 20260918】原语句面 `a <> 0`（Leibniz/表示级）
   为【假命题】：反例 a := Qmake 0 2 满足 Leibniz 非 0，但 Qeq 面为零，
   此时 /a == 0，左端 a * (x / a) == 0 ≠ x。故本引理原形不可证非 tactic
   之过，最小维修 = 前提重述 Qeq 面 `~ a == 0`（真前提，语义恰所需，
   非改弱）。另 :85 原报错（T63 定格：Found no subterm matching
   "(Qnum (?M * (?M * ?M)) * QDen (?M * ?M * ?M))%Z"）双因：
   ① Qmult_assoc 实形 `n * (m * p) == n * m * p` LHS 右结合，
     目标 (x*a)*/a 左结合无匹配（即该 Z 展开模式）；
   ② Qmult_inv_r 9.1 实形为单参 `forall x, ~ x == 0 -> x * / x == 1`，
     原双参引用形 + Leibniz 前提 `exact Ha` 两处皆不匹配。 *)
Lemma p12_div_cancel : forall a x : Q, ~ a == 0 -> a * (x / a) == x.
Proof.
  intros a x Ha. unfold Qdiv.
  transitivity (x * (a * / a)).
  - ring.
  - rewrite Qmult_inv_r by exact Ha. apply Qmult_1_r.
Qed.

(* CZD13 新增支撑：v == 0（Qeq 面）时 (1-v)^k == 1——主件零支用。
   证面全在 Proper 参数位 setoid rewrite（Qmult/Qminus 位实测可用）。 *)
Lemma p12_qpow_zero_r : forall (k : nat) (v : Q),
  v == 0 -> p12_qpow (1 - v) k == 1.
Proof.
  intros k. induction k as [| k IH]; intros v Hv.
  - reflexivity.
  - simpl. rewrite (IH v Hv). rewrite Hv. reflexivity.
Qed.

(* ---- 主件：一般 k 无条件参数化（销论文5 §9 边界 3 的第一格） ---- *)

Theorem p12_param_general_k : forall (k : nat) (v : Q),
  (1 <= k)%nat -> v <> 0 ->
  exists w : Q,
    p12_s k v == (Z.of_nat k # 1) * v + p12_bcoef k * v * v + v * v * v * w.
Proof.
  (* CZD13 证体重构 20260918：原稿除法消去支依赖「v³ Qeq 非 0」，
     而 Leibniz 前提 v <> 0 推不出它（Qmake 0 2 反例同源）——非 tactic
     缺陷而是覆盖面缺口。按 Qeq_dec v 0 双分支闭合：
     零支（Qeq 为 0，含非正规形）p12_s == 0，取 w := 0；
     非零支走除法消去真支 + ring。定理语句面零改动；Hk 在本证面
     天然冗余（两支均不用），保留以维持语句面原貌。 *)
  intros k v Hk Hv.
  destruct (Qeq_dec v 0) as [Hv0 | Hvn].
  - exists 0%Q.
    assert (Hs : p12_s k v == 0).
    { unfold p12_s. rewrite (p12_qpow_zero_r k v Hv0). reflexivity. }
    rewrite Hs. rewrite Hv0. ring.
  - exists ((p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v)
            / (v * v * v)).
    assert (Hv3 : ~ v * v * v == 0).
    { intros Hz. apply Hvn.
      apply Qmult_integral in Hz. destruct Hz as [H1 | H1].
      - apply Qmult_integral in H1. destruct H1 as [H2 | H2]; exact H2.
      - exact H1. }
    rewrite (p12_div_cancel (v * v * v)
              (p12_s k v - (Z.of_nat k # 1) * v - p12_bcoef k * v * v) Hv3).
    ring.
Qed.

(* k=1 特化：与库内无条件件 cec_r6_param_k1 同位对照 *)
Corollary p12_param_k1 : forall v : Q,
  v <> 0 ->
  exists w : Q,
    p12_s 1%nat v == (Z.of_nat 1 # 1) * v + p12_bcoef 1%nat * v * v
            + v * v * v * w.
Proof.
  intros v Hv.
  apply (p12_param_general_k 1%nat v); [ apply le_n | exact Hv ].
Qed.

(* 角点指纹（k=1 系数 > 1/2，无条件；cec_coef_fingerprint 的 k=1 角点） *)
Lemma p12_coef_fingerprint_one : Qlt (1 # 2) (p12_coef 1%nat).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions p12_param_general_k.
