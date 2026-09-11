(* ============================================================ *)
(* UpReqCSB.v —— C-S le 形的 ≤_B 显式对照件（B 形扩展建造队列 T5 席 ·   *)
(*   20260911）。论文正式版 §10.2 第 6 项（L1228）登记「C-S le 形（模块  *)
(*   UpCS）的 B 形显式对照件亦可升格未建」——本件补建。                  *)
(* 主件 real_cauchy_schwarz_B：AB² ≤_B AA·BB，其中                       *)
(*   AB := dotp a b（内积和），AA := sql a，BB := sql b（平方和）。       *)
(* 证书供给链：le 形源件 real_cauchy_schwarz（UpCS，eps 版有限和 C-S）   *)
(*   系 plain-eps 余量族——∀eps>0, real_le AB² (AA·BB + eps)；经          *)
(*   D:=one 特化收口器 real_le_closure_b_one（UpRealLeB D.0，其体即      *)
(*   real_le_closure_b 于 real_one / real_lt_zero_one 的实例 + 1·eps     *)
(*   换形）单步收口为 ≤_B。正性证书 real_lt_zero_one 为 CW219 闭合       *)
(*   既有件，零新增前提。同型先例：real_minp_projection_eps_B            *)
(*   （UpReqMinPProjB L121，real_le_closure_b_one 收口写法）。           *)
(* 形态抉择（如实标注）：UpCS 的 le 形即「逐 eps 加余」形，eps 版与       *)
(*   ≤_B 等价性（§9.3.2 已证）任取其一——本件出口取 ≤_B 形（余量族       *)
(*   全称吸收进 real_le_b 定义面），eps 形由 UpCS 源件原位保留，双向     *)
(*   可达：≤_B 出口 defunfold 即逐 eps 面，源件直喂即本件证明体。        *)
(* 红线自审：real_le_b 为 Set 值 forall 型（UpRealLeB L63），real_lt     *)
(*   sigT Set 层，语句面全 Set 零 Prop 泄露；纯项模式（real_eq 非 Id     *)
(*   零改写）；单件单 Qed 全封口；前置件 UpRealLeB/UpCS 只读消费，       *)
(*   vo 树零写入。                                                       *)
(* 编译配方：cpu_guard.ps1 包装，coqc -vos 秒审先行后全量，              *)
(*   -Q <vo 树> "" 供前置件（与 Live_X 邻席配方同源）。                  *)
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

(* 尾注：单步收口=源件逐 eps 面直喂特化收口器；出口与 eps 形等价可达。 *)
Print Assumptions real_cauchy_schwarz_B.
