(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uap_abs_diff_triangle_le_B（原 L143，2 句玩具证）                    *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经全量恒等核查与试点复核：本件实测                                                           *)
(* 为恒等守恒——清单所列 1 处证明体与 Main 现版原件逐字同文（刀体                                *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；核验记录见对应批次核验文书存档。                                                     *)
(* 附记：判级全文恒等；同批同域各件同款处理整批直推。                                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblAbsTwoPtAbs.v —— 两点核差形的接口级抽象供给件                    *)
(*   （具体 Real 层两点核差形结果的接口级抽象对应）                      *)
(*                                                                *)
(* 零承认件：无承认词面、无经典逻辑、无假设参数声明、全件 Qed 闭合。      *)
(*   语句面全 Set 层：lt/le 为接口 Set 值关系（R -> R -> Set），          *)
(*   Id 为 S01 Set 层等同类型，Or 为 S01 Set 层别名（sum 型），           *)
(*   uap_le_b 返回型显式 Set——语句面无裸「命题层」泄露。                *)
(*   证明全构造：id_trans/id_cong/id_cong2 逐项运输，Or 仅 inl 单支。     *)
(*                                                                *)
(* 目标：把两点核差形（UpAblAbsSumLeB 的 A.1/A.2，目前位于具体 Real 层）  *)
(*   抽象化为接口级供给——在 RealInterfaceEnhanced Context（abs 族字段    *)
(*   可用系：abs/abs_triangle/abs_nonneg/abs_opp）内供给                 *)
(*   |a−c| ≤ (|a−b|+|b−c|)+eps。                                        *)
(*   本件为接口级抽象 B 形供给的独立互补材料（不 Require、不改写          *)
(*   UpAblAbsSumLeB 系任何文件；无逐 eps 加法字段缺失问题——              *)
(*   接口 le/lt 本身即 Set 值关系，逐 eps 形直接可述）。                  *)
(*                                                                *)
(* 四件供给（全部非平凡构造）：                                          *)
(*   M1 uap_le_add_r：正余量右吸收（接口级）——                           *)
(*      le a b ＋ 0 < c ⟹ le a (b+c)；纯 le 通道构造                     *)
(*      （le_plus_compat ×2＋le_trans；0<c 经 lt_le_iff inl 注入升 le；  *)
(*        接口 le 无 Or 解开字段，UpAblAbsSumLeB 的 Or 分拆路线不可迁移）。*)
(*   M2 uap_diff_stitch：差恒等链 (a−b)+(b−c) ≡ a−c——                    *)
(*      plus_assoc ×2 ＋ plus_comm/plus_opp ＋ plus_zero，               *)
(*      id_cong2 逐项运输（五步恒等链路线的接口级复现）。                *)
(*   M3 uap_abs_diff_triangle_le_eps（主件）：两点核差形逐 eps 形          *)
(*      接口级供给——应用接口 abs_triangle 字段（具体层                    *)
(*      real_abs_triangle 两点核的抽象化），id_cong abs 把两点核左端      *)
(*      经 M2 恒等链换到 |a−c|，右端经 M1 正余量右吸收承担 eps。          *)
(*   M4 uap_le_b＋uap_abs_diff_triangle_le_B：接口级 Bishop 形——           *)
(*      uap_le_b x y := ∀eps>0, x ≤ y+eps（plain-eps 逐 eps 语义，        *)
(*      显式 Set 值；对应 UpRealLeB 的 real_le_closure_b_one 前提位——     *)
(*      具体层该前提经完成引理单步升 real_le_b，故本语义为接口级          *)
(*      可达最强形的诚实对应物；接口 le 无 Or 解开字段，strict            *)
(*      完成形在接口级不可证，如实供给 plain-eps 语义并在此显式说明）。    *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（仅此一件）。                           *)
(* 编译配方：Rocq 9.1 直调 coqc（coqc 无 -Q），cpu_guard 包裹限载；   *)
(*   输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。        *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.

(* ============================================================ *)
(* 接口 Context：RealInterfaceEnhanced（abs 族字段可用系）               *)
(* ============================================================ *)

Section TwoPtAbsInterface.

Context {RI : RealInterfaceEnhanced}.

Local Existing Instance RI_base.

Let zero := @zero RI.
Let one := @one RI.
Let plus := @plus RI.
Let opp := @opp RI.
Let abs := @abs RI.
Let lt := @lt RI.
Let le := @le RI.

(* ---------------------------------------------------------- *)
(* M1 · 正余量右吸收（接口级）                                      *)
(*   le a b ＋ 0 < c ⟹ le a (b+c)。                                  *)
(*   构造（接口 le 无 Or 解开字段，Or 分拆路线不可迁移——              *)
(*   纯 le 通道构造）：a ≤ a+0 ≤ a+c（0 < c 经 lt_le_iff inl 注入      *)
(*   升 le，le_plus_compat 承载）≤ b+c（le_plus_compat），le_trans 收束。 *)
(* ---------------------------------------------------------- *)

Lemma uap_le_add_r : forall a b c : R,
  le a b -> lt zero c -> le a (plus b c).
Proof.
  intros a b c Hab Hc.
  apply (le_trans a (plus a c) (plus b c)).
  - apply (le_id_l a (plus a zero) (plus a c)).
    + exact (id_sym (plus_zero a)).
    + apply (le_plus_compat a a zero c).
      * apply le_refl.
      * apply (lt_le_iff zero c). apply inl. exact Hc.
  - apply (le_plus_compat a b c c).
    + exact Hab.
    + apply le_refl.
Qed.

(* ---------------------------------------------------------- *)
(* M2 · 差恒等链（uap_diff_stitch）：(a−b)+(b−c) ≡ a−c              *)
(*   构造（五步恒等链路线的接口级复现，全部 id_trans/id_cong 逐项）：      *)
(*   ① plus_assoc (a−b) b (b−c) 反向展开；                            *)
(*   ② id_cong（plus a）收拢到内层 opp b+(b+(opp c))；                 *)
(*   ③ plus_assoc (opp b) b (opp c) 反向展开；                        *)
(*   ④ id_cong2 plus：opp b+b ≡ 0（plus_comm＋plus_opp）逐项运输；     *)
(*   ⑤ 0+(opp c) ≡ opp c（plus_comm＋plus_zero）。                    *)
(* ---------------------------------------------------------- *)

Lemma uap_diff_stitch : forall a b c : R,
  Id (plus (plus a (opp b)) (plus b (opp c))) (plus a (opp c)).
Proof.
  intros a b c.
  apply (id_trans (id_sym (plus_assoc a (opp b) (plus b (opp c))))).
  apply (id_cong (fun t : R => plus a t)).
  apply (id_trans (plus_assoc (opp b) b (opp c))).
  apply (id_trans (id_cong2 plus
           (id_trans (plus_comm (opp b) b) (plus_opp b)) (id_refl))).
  apply (id_trans (plus_comm zero (opp c))).
  apply (plus_zero (opp c)).
Qed.

(* ---------------------------------------------------------- *)
(* M3 · 主件：两点核差形逐 eps 形（接口级供给）                        *)
(*   |a−c| ≤ (|a−b|+|b−c|)+eps（0 < eps）。                            *)
(*   构造：应用接口 abs_triangle 字段（real_abs_triangle 两点核        *)
(*   的抽象化）于实例 (a−b, b−c)，id_cong abs 把两点核左端           *)
(*   经 M2 恒等链接到 |a−c|，右端经 M1 正余量右吸收承担 eps。        *)
(* ---------------------------------------------------------- *)

Theorem uap_abs_diff_triangle_le_eps :
  forall a b c eps : R,
    lt zero eps ->
    le (abs (plus a (opp c)))
       (plus (plus (abs (plus a (opp b))) (abs (plus b (opp c)))) eps).
Proof.
  intros a b c eps Heps.
  apply (le_id_l (abs (plus a (opp c)))
                 (abs (plus (plus a (opp b)) (plus b (opp c))))).
  - exact (id_sym (id_cong abs (uap_diff_stitch a b c))).
  - apply (uap_le_add_r
             (abs (plus (plus a (opp b)) (plus b (opp c))))
             (plus (abs (plus a (opp b))) (abs (plus b (opp c)))) eps).
    + exact (abs_triangle (plus a (opp b)) (plus b (opp c))).
    + exact Heps.
Qed.

(* ---------------------------------------------------------- *)
(* M4 · 接口级 Bishop 形（plain-eps 逐 eps 语义，显式 Set 值）          *)
(*   uap_le_b x y := ∀eps>0, x ≤ y+eps（对应 real_le_closure_b_one     *)
(*   前提位；接口 le 无 Or 解开字段，strict 完成形接口级不可达，        *)
(*   本语义为可达最强形的诚实对应物——显式说明）。                      *)
(* ---------------------------------------------------------- *)

Definition uap_le_b (x y : R) : Set :=
  forall eps : R, lt zero eps -> le x (plus y eps).

Theorem uap_abs_diff_triangle_le_B :
  forall a b c : R,
    uap_le_b (abs (plus a (opp c)))
             (plus (abs (plus a (opp b))) (abs (plus b (opp c)))).
Proof.
  intros a b c eps Heps.
  exact (uap_abs_diff_triangle_le_eps a b c eps Heps).
Qed.

End TwoPtAbsInterface.

(* ============================================================ *)
(* 审计注记：Print Assumptions 预期全 Closed（零外部未证假设）           *)
(* ============================================================ *)

Print Assumptions uap_le_add_r.
Print Assumptions uap_diff_stitch.
Print Assumptions uap_abs_diff_triangle_le_eps.
Print Assumptions uap_abs_diff_triangle_le_B.
