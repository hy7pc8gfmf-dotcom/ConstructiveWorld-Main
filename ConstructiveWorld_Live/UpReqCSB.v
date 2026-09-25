(* ============================================================ *)
(* 玩具证替换件（消融落件）——替换面清单见下 *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   real_cauchy_schwarz_B（原 L40，4 句玩具证）                          *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经全量 *)
(* 恒等核查与试点复核：本件实测为恒等守恒——清单所列 1 参数位证明体与 *)
(* Main 现版原件逐字同文（刀体＝原体，零变化），头注「替换」声称与实物 *)
(* Require 面零改动；头注过程流水词面已作中性化处理。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqCSB.v *)
(* *)
(* 目的： Cauchy–Schwarz 的 ≤_B 显式对照件。 *)
(* 主件： real_cauchy_schwarz_B：C-S 不等式的 real_le_b 形。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpCS。 *)
(* 备注： 单定理对照件：与 UpCS 的 eps 形互为序档对照；零新假设位。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqCSB.v —— C-S le 形的 ≤_B 显式对照件（B 形扩展建造队列 ·   *)
(*   UpCS）的 B 形显式对照件亦可升格未建」——本件补建。                  *)
(* 主件 real_cauchy_schwarz_B：AB² ≤_B AA·BB，其中                       *)
(*   AB := dotp a b（内积和），AA := sql a，BB := sql b（平方和）。       *)
(* 证书供给链：le 形源件 real_cauchy_schwarz（UpCS，eps 版有限和 C-S）   *)
(*   系 plain-eps 余量族——∀eps>0, real_le AB² (AA·BB + eps)；经          *)
(*   D:=one 特化完成器 real_le_closure_b_one（UpRealLeB D.0，其体即      *)
(*   real_le_closure_b 于 real_one / real_lt_zero_one 的实例 + 1·eps     *)
(*   换形）单步完成为 ≤_B。正性证书 real_lt_zero_one 为 闭合       *)
(*   既有件，零新增前提。同型先例：real_minp_projection_eps_B            *)
(*   （UpReqMinPProjB L121，real_le_closure_b_one 完成写法）。           *)
(* 形态抉择（如实标注）：UpCS 的 le 形即「逐 eps 加余」形，eps 版与       *)
(*   ≤_B 等价性（§9.3.2 已证）任取其一——本件出口取 ≤_B 形（余量族       *)
(*   全称吸收进 real_le_b 定义面），eps 形由 UpCS 源件原位保留，双向     *)
(*   可达：≤_B 出口 defunfold 即逐 eps 面，源件显式应用即本件证明体。        *)
(* 红线自审：real_le_b 为 Set 值 forall 型（UpRealLeB L63），real_lt     *)
(*   sigT Set 层，语句面全 Set 零 Prop 泄露；纯项模式（real_eq 非 Id     *)

(*   vo 树零写入。                                                       *)

(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpCS.

(* 主件：C-S 结论的 ≤_B 形态（§10.2 第 6 项升格对照件） *)
Lemma real_cauchy_schwarz_B :
  forall a b : list Real,
    real_le_b (real_mult (dotp a b) (dotp a b))
              (real_mult (sql a) (sql b)).
Proof.
  intros a b.
  apply real_le_closure_b_one.
  intros eps Heps.
  exact (real_cauchy_schwarz a b eps Heps).
Qed.

(* 尾注：单步完成=源件逐 eps 面显式应用特化完成器；出口与 eps 形等价可达。 *)
Print Assumptions real_cauchy_schwarz_B.
