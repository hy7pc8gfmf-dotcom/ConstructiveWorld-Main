(* ============================================================ *)
(* EpiOrFaces.v                                                  *)
(* 模块与使命：经典命题「e·π 与 e+π 至少一个无理」的构造性形态谱——      *)
(*   四种语句形态的 Set 层完整语句面。                                   *)
(*   记 epiIrr(X)＝lic 判据结论面：对每个有理数 q 存在 Q 层正分离常数 c   *)
(*   使 real_const c < |X−q|（定量强无理性，sigT 见证形）；               *)
(*   记 AlgWit(X)＝非零整系数多项式以 X 为根的 real_eq 根证书。           *)
(*   (a强) epi_or_face＝Or (epiIrr(e·π)) (epiIrr(e+π))：析取数据形，      *)
(*         任一支被给出即解出 e·π 或 e+π 之一的无理性（当代开放问题）；   *)
(*   (c强) epi_cond_face＝forall w:AlgWit(e·π), epiIrr(e+π)：             *)
(*         条件见证形，结论经典真，仅缺 Hermite–Mahler 型有效引擎；       *)
(*   (b)=(c弱) 负言形≡条件弱形：epi_curry_forward／backward 与            *)
(*         epi_neg_equiv_weak_cond 给出 currying 纯逻辑互等（零数学内容； *)
(*         负言形属 Prop 脚手架层，不入 Set 语句面）。                    *)
(*   (a强) 与 (c强) 互不可导出：IrrLic 与 AlgWit 相容（强无理可兼代数，   *)
(*         如 √2），而 e·π 的代数见证本身是开放问题——两向均需新数学输入； *)
(*         该论证属元层级，不在本件形式化范围内。                         *)
(*   证书可得性：e 支由 lic_e_irrational_criterion 直接给出（epi_irr_e）； *)
(*   π 支与 e·π、e+π 的证书在数学上尚属开放问题，本件显式留空。           *)
(* 依赖：S01_BaseRing；S02_CauchyComplete；S03_QExp；SumInvFactEscape；   *)
(*   S10_KVQuantTrig；UpReqIrrationalCriterion。                          *)
(* 对标：lic_e_irrational_criterion 结论面；UpReqLpoEquiv 的 rLPO 语句面  *)
(*   （Set 层 Or 编码）；Hermite 1873（e 超越性）；Mahler 1953             *)
(*   （有效无理测度，(c强) 所需引擎的数学原型）。                         *)
(* 构造性：零 Axiom／承认式；语句面全 Set 层（sigT／And／Or 承载，         *)
(*   比较用 QltT／real_lt，无 Prop 泄露位）；AlgWit 带非零位证书          *)
(*   （Z.eqb 判定面），防零多项式平凡化；rpoly_eval 为 Fixpoint 求值器。  *)
(* 编译配方：coqc -native-compiler no -q -Q <本件目录> "" -Q <Live_X> ""。 *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith ZArith.ZArith List.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import SumInvFactEscape.
Require Import S10_KVQuantTrig.
Require Import UpReqIrrationalCriterion.

(* §1 e、π、e·π、e+π 的实数记录（均为库内已有定义的直接引用） *)

Definition eR : Real :=
  existT (fun u : Qseq => cauchy u) (fun n => exp_series n 1)
    (lic_seq_cauchy (fun n => exp_series n 1) (fun n => 1%Q / q_fact n)
       lic_tail_e lic_vanish_e).

Definition piR : Real := cauchy_real_pi_leibniz.

Definition prodR : Real := real_mult eR piR.
Definition sumR  : Real := real_plus eR piR.

(* §2 强无理性语句面（同 lic 判据结论面） *)

Definition epiIrr (X : Real) : Set :=
  forall q : Q, sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c) (real_metric X (real_const q)))).

(* e 支证书：由 lic_e_irrational_criterion 直接转换。 *)
Lemma epi_irr_e : epiIrr eR.
Proof.
  intro q. exact (lic_e_irrational_criterion q).
Qed.

(* §3 (a强) 析取数据形（Set 层 Or，同 rLPO 语句面编码） *)

Definition epi_or_face : Set := Or (epiIrr prodR) (epiIrr sumR).

(* §4 整系数多项式求值器：系数表低位在前，P = a0 + a1·x + a2·x² + … *)

Fixpoint rpoly_eval (cs : list Z) (x : Real) : Real :=
  match cs with
  | nil => real_const 0%Q
  | a :: rest => real_plus (real_const (Qmake a 1))
                           (real_mult x (rpoly_eval rest x))
  end.

(* AlgWit(X)：存在整系数表 cs、非零位 k（Z.eqb 判定面），
   以及 rpoly_eval cs X ＝ 0 的 real_eq 根证书。 *)
Definition AlgWit (X : Real) : Set :=
  sigT (fun cs : list Z =>
    sigT (fun k : nat =>
      And (Id (Z.eqb (nth k cs 0%Z) 0%Z) false)
          (real_eq (rpoly_eval cs X) real_zero))).

(* §5 (c强) 条件见证形 *)

Definition epi_cond_face : Set := forall w : AlgWit prodR, epiIrr sumR.

(* §6 currying 互等桥：¬(A∧B) ≡ A→¬B 纯逻辑互推，零数学内容；
   (b) 负言形不入 Set 语句面，仅存于本 Prop 脚手架层。
   AlgP(X)＝AlgWit(X) 的 inhabitedness 提升（ex 量化于 Set 型，落 Prop）。 *)

Definition AlgP (X : Real) : Prop := exists w : AlgWit X, True.

Lemma epi_curry_forward : forall X Y : Real,
  ~ (AlgP X /\ AlgP Y) -> AlgP X -> ~ AlgP Y.
Proof.
  intros X Y Hconj Hx Hy. apply Hconj. split; assumption.
Qed.

Lemma epi_curry_backward : forall X Y : Real,
  (AlgP X -> ~ AlgP Y) -> ~ (AlgP X /\ AlgP Y).
Proof.
  intros X Y Hcurry [Hx Hy]. exact (Hcurry Hx Hy).
Qed.

Lemma epi_neg_equiv_weak_cond :
  (~ (AlgP prodR /\ AlgP sumR)) <-> (AlgP prodR -> ~ AlgP sumR).
Proof.
  split.
  - apply epi_curry_forward.
  - apply epi_curry_backward.
Qed.

(* §7 提取与公理面 *)

Separate Extraction eR piR prodR sumR epiIrr epi_or_face rpoly_eval
  AlgWit epi_cond_face.

Print Assumptions epi_irr_e.
Print Assumptions epi_or_face.
Print Assumptions epi_cond_face.
Print Assumptions epi_neg_equiv_weak_cond.

(* ============================================================ *)
(* §8 有理面与强无理面的互斥                                     *)
(* ============================================================ *)

(* Qabs（绝对值）与其 Qeq 同余引理 Qabs_wd 的供应面：QArith.QArith
   不含 Qabs 模块，本件续作区显式引入（纯 Q 算术，零公理增量）。 *)
From Stdlib Require Import QArith.Qabs.

(* RatP(X)：X 等于某有理数（real_eq 有理常量形，Set 层 sigT）。 *)
Definition RatP (X : Real) : Set :=
  sigT (fun q : Q => real_eq X (real_const q)).

(* RatP_h：RatP 的 inhabitedness 提升（Prop 层，同 AlgP 形）。 *)
Definition RatP_h (X : Real) : Prop := exists p : RatP X, True.

Lemma ratp_lift_forward : forall X : Real, RatP X -> RatP_h X.
Proof.
  intros X [q Hq]. exists (existT _ q Hq). exact I.
Qed.

(* 注意：RatP_h 到 RatP 无回取（Prop 消除不出 Set 数据）——提升面严格单向，
   析取形态到提升负言面的弱化在 Prop 目标内直接消去 ex 完成。 *)

(* 互斥核心：强无理（对每个有理数有正分离常数证书）与等于某有理数不可兼得。
   论证：以 c/2 为逼近精度，间隔证书给出 e0 < |u_N − q| − c，
   逼近给出 |u_N − q| < c/2；串接得 c < c·(1/2)，与 c > 0 相抵。 *)
Lemma epi_irr_not_ratface : forall X : Real, epiIrr X -> RatP X -> False.
Proof.
  intros X Hirr [q Hq].
  destruct (Hirr q) as [c [Hc [e0 [He0 [N0 Hsep]]]]].
  assert (Hpos2 : Qlt 0 (1 # 2)%Q) by (unfold Qlt; cbn; reflexivity).
  assert (Hhalf : QltT 0 (c * (1 # 2))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat c (1 # 2)%Q).
    - apply QltT_to_Qlt. exact Hc.
    - exact Hpos2. }
  destruct (Hq (c * (1 # 2))%Q Hhalf) as [N1 H1].
  assert (Hle0 : NatLe N0 (max N0 N1)).
  { apply NatLe_lift. apply Nat.le_max_l. }
  assert (Hle1 : NatLe N1 (max N0 N1)).
  { apply NatLe_lift. apply Nat.le_max_r. }
  pose proof (Hsep _ Hle0) as HsN.
  pose proof (H1 _ Hle1) as H1N.
  (* Qeq 重写不入 QltT 语境（无 Proper 实例；同 lic 源定理本体形）：
     投影换形经 lic_qltt_comp_r 于 Qeq 平面完成。 *)
  assert (HsT : QltT e0 ((Qabs ((projT1 X (max N0 N1) - q)%Q) - c)%Q)).
  { apply (lic_qltt_comp_r
             ((projT1 (real_metric X (real_const q)) (max N0 N1))
              - projT1 (real_const c) (max N0 N1))%Q
             ((Qabs ((projT1 X (max N0 N1) - q)%Q) - c)%Q)
             e0).
    - pose proof (lic_metric_proj X q (max N0 N1)) as HQ.
      rewrite real_const_proj.
      rewrite HQ.
      reflexivity.
    - exact HsN. }
  assert (H1T : QltT (Qabs ((projT1 X (max N0 N1) - q)%Q)) (c * (1 # 2))%Q).
  { pose proof (real_const_proj q (max N0 N1)) as HQ0.
    assert (HabsEq : (Qabs (projT1 X (max N0 N1) - projT1 (real_const q) (max N0 N1)))%Q
                     == (Qabs ((projT1 X (max N0 N1) - q)%Q))%Q).
    { apply Qabs_wd. rewrite HQ0. reflexivity. }
    pose proof (QltT_to_Qlt _ _ H1N) as H1Q.
    setoid_rewrite HabsEq in H1Q.
    apply (Qlt_to_QltT _ _ H1Q). }
  set (A := Qabs ((projT1 X (max N0 N1) - q)%Q)) in *.
  pose proof (QltT_to_Qlt _ _ HsT) as HsN'.
  pose proof (QltT_to_Qlt _ _ H1T) as H1N'.
  pose proof (QltT_to_Qlt _ _ He0) as He0'.
  pose proof (QltT_to_Qlt _ _ Hhalf) as Hpos'.
  (* e0 + c < A：右端经 ((A − c) + c == A) 平移 *)
  assert (Hshift : Qlt (e0 + c)%Q A).
  { apply (lic_qlt_comp_r ((A - c)%Q + c)%Q A (e0 + c)%Q).
    - apply lic_qlt_minus_add_r.
    - apply lic_qlt_add_r. exact HsN'. }
  pose proof (Qlt_trans _ _ _ Hshift H1N') as Hbad.
  (* c < e0 + c：自 0 < e0 加 c 平移 *)
  assert (Hce : Qlt c (e0 + c)%Q).
  { pose proof (lic_qlt_add_r 0%Q e0 c He0') as H0.
    rewrite Qplus_0_l in H0.
    exact H0. }
  pose proof (Qlt_trans _ _ _ Hce Hbad) as Hbad2.
  (* c < c·(1/2) 与 0 < c·(1/2) 相抵 *)
  assert (Hmid : Qlt (c * (1 # 2))%Q 0%Q).
  { pose proof Hbad2 as H0.
    apply (lic_qlt_add_l (- (c * (1 # 2)))%Q c (c * (1 # 2))%Q) in H0.
    assert (Hr2 : ((- (c * (1 # 2)))%Q + c * (1 # 2))%Q == 0%Q) by ring.
    rewrite Hr2 in H0.
    assert (Hr1 : ((- (c * (1 # 2)))%Q + c)%Q == (c * (1 # 2))%Q) by ring.
    rewrite Hr1 in H0.
    exact H0. }
  exact (Qlt_irrefl 0%Q (Qlt_trans _ _ _ Hpos' Hmid)).
Qed.

(* 析取形态到双侧有理性负言的弱化（(a强) 到 (a弱) 降格）。 *)
Lemma epi_or_not_both_rat : epi_or_face -> RatP prodR -> RatP sumR -> False.
Proof.
  intros [f | g] hr hs.
  - exact (epi_irr_not_ratface prodR f hr).
  - exact (epi_irr_not_ratface sumR g hs).
Qed.

Lemma epi_or_face_down_dm : epi_or_face -> ~ (RatP_h prodR /\ RatP_h sumR).
Proof.
  intros hor [hr hs].
  destruct hr as [p Hp]. destruct hs as [p0 Hp0].
  exact (epi_or_not_both_rat hor p p0).
Qed.

(* ============================================================ *)
(* §9 条件见证形的弱化蕴含面与析取出口                           *)
(* ============================================================ *)

(* 应用面：(c强) 在见证给定时即产出 e+π 的强无理证书（良形性注记）。 *)
Lemma epi_cond_face_apply : epi_cond_face -> AlgWit prodR -> epiIrr sumR.
Proof.
  intros ec w. exact (ec w).
Qed.

(* 出口面：(c强) 连同 e·π 的代数见证即给出 (a强) 的右支。 *)
Lemma epi_cond_or_intror : epi_cond_face -> AlgWit prodR -> epi_or_face.
Proof.
  intros ec w. exact (inr (ec w)).
Qed.

(* (c强) 的极大可封合弱化：见证与 e+π 有理证书不可兼得（经互斥核心）。 *)
Lemma epi_cond_down_ratweak : epi_cond_face -> AlgWit prodR -> RatP sumR -> False.
Proof.
  intros ec w hr. exact (epi_irr_not_ratface sumR (ec w) hr).
Qed.

(* 剩余蕴含面的 Set 层语句形。其 inhabitedness 的数学现状（显式记录）：
   两面现皆无成员——(a强) 到 (c强) 需对任一代数见证产出 e+π 强无理证书；
   (c强) 到 (a强) 在 e·π 无代数见证时为空真、不产出分支数据；
   强无理与代数性相容（如 √2 兼二者），见证存在性本身为开放问题。 *)
Definition epi_or_implies_cond : Set := epi_or_face -> epi_cond_face.
Definition epi_cond_implies_or : Set := epi_cond_face -> epi_or_face.

(* (c强) 到 (c弱)（代数性负言形）的蕴含面。其 inhabitedness 需 e 的
   超越性作为数学输入：若 e·π 与 e+π 兼代数，则 e 为有理系数二次方程
   x² − (e+π)x + e·π 之根，故 e 代数，与 Hermite 超越性相抵；库内现有
   e 无理性（lic 判据）不足以封合本面。 *)
Definition epi_cond_implies_weak : Prop :=
  epi_cond_face -> AlgP prodR -> ~ AlgP sumR.

(* ============================================================ *)
(* §10 分支见证的计算形态                                        *)
(* ============================================================ *)

(* 析取见证解出支号与强无理证书：全链可提取的计算面。 *)
Lemma epi_or_branch_extract : forall (P : Real -> Set),
  (forall Z : Real, epiIrr Z -> P Z) -> epi_or_face -> sigT (fun u : Real => P u).
Proof.
  intros P HP [f | g].
  - exists prodR. apply HP. exact f.
  - exists sumR. apply HP. exact g.
Qed.

(* Or 经分支映射的分配面。 *)
Lemma epi_or_face_map : forall (A B : Set),
  (epiIrr prodR -> A) -> (epiIrr sumR -> B) -> epi_or_face -> Or A B.
Proof.
  intros A B f g [h | h].
  - exact (inl (f h)).
  - exact (inr (g h)).
Qed.

(* 布尔支号重编码：与 Or 互相解出（分支即数据）。 *)
Definition epi_or_branch_data : Set :=
  sigT (fun b : bool =>
    match b with
    | true => epiIrr prodR
    | false => epiIrr sumR
    end).

Lemma epi_or_face_to_branch_data : epi_or_face -> epi_or_branch_data.
Proof.
  intros [f | g].
  - exists true. exact f.
  - exists false. exact g.
Qed.

Lemma branch_data_to_epi_or_face : epi_or_branch_data -> epi_or_face.
Proof.
  intros [b h]. destruct b.
  - exact (inl h).
  - exact (inr h).
Qed.

(* 支的判定（无见证时断言何支成立）不在本件范围：epi_or_face 自身的
   inhabitedness 为当代开放问题，两出口引理不引入任何判定机制。 *)

(* ============================================================ *)
(* §11 提取与公理面（续）                                        *)
(* ============================================================ *)

Separate Extraction RatP epi_or_branch_data epi_or_face_map
  epi_or_branch_extract epi_cond_face_apply epi_cond_or_intror.

Print Assumptions epi_irr_not_ratface.
Print Assumptions epi_or_not_both_rat.
Print Assumptions epi_or_face_down_dm.
Print Assumptions ratp_lift_forward.
Print Assumptions epi_cond_face_apply.
Print Assumptions epi_cond_or_intror.
Print Assumptions epi_cond_down_ratweak.
Print Assumptions epi_or_branch_extract.
Print Assumptions epi_or_face_map.
Print Assumptions epi_or_face_to_branch_data.
Print Assumptions branch_data_to_epi_or_face.

(* ============================================================ *)
(* §12 依赖面的显式前提承载（低形引擎入库前的命名前提面）               *)
(* ============================================================ *)

(* 形态谱两形的数学输入尚不在库：(b)=(c弱) 需要 e 的有效超越引擎
   （Hermite 1873 型；(b) 的经典证明只动用 Trans(e)，π 侧超越性
   不需要）；(c强) 另需 Mahler 1953 型有效无理测度。本节把两个
   依赖面铸成命名的 Set 层前提类型：缺什么、以何形承载逐字在案，
   每一 Print Assumptions 行记一项闭合。数学输入入库后以实例替换
   前提即闭合终形，语句面逐字不动。 *)

(* TransWit_weak(X)：L1 接口——「非零整系数多项式 P 且 P(X)=0」
   证书的反驳机，出口取 Set 层空型 Empty_set（反驳数据可消除入
   任意目标，全位无命题）。Niven–Hermite 泛型骨架（核/整/界/
   极限/出口五段）已在库；e 侧实例化分解为五件后续工作：插值核、
   整性、界、出口转换、结式清整。 *)
Definition TransWit_weak (X : Real) : Set :=
  forall cs : list Z,
    sigT (fun k : nat =>
      And (Id (Z.eqb (nth k cs 0%Z) 0%Z) false)
          (real_eq (rpoly_eval cs X) real_zero)) ->
    Empty_set.

(* TransWit_meas(X)：L2 接口——Mahler 型有效无理测度：每个非零
   整系数多项式 P 配显式 δ>0 使 real_const δ < |P(X)|（分离面与
   epiIrr 同形）。此为 (c强) 结论面的引擎级输入，量级较重，
   待 L1 到库后推进。 *)
Definition TransWit_meas (X : Real) : Set :=
  forall cs : list Z,
    sigT (fun k : nat => Id (Z.eqb (nth k cs 0%Z) 0%Z) false) ->
    sigT (fun d : Q => And (QltT 0 d)
      (real_lt (real_const d) (real_metric (rpoly_eval cs X) real_zero))).

(* 泛型前提段（前提位全 Set 型）：前提一＝结式清整层——e·π 与
   e+π 两份根证书到一份 e 侧根证书的代数消元（两根证书之下 e 为
   x² − (e+π)x + e·π 之根，同 §9 注记）；前提二＝TransWit_weak
   在 e 上的实例。 *)
Section EpiTransWitClosure.

Variable res_cl : AlgWit prodR -> AlgWit sumR -> AlgWit eR.
Variable twk_e  : TransWit_weak eR.

(* 主闭合（Set 出口形）：双根证书经清整与引擎即出矛盾数据——
   (b) 的经典形态在两前提下闭合，全程只动用 e 侧输入。 *)
Theorem epi_trans_weak_quad_exit : AlgWit prodR -> AlgWit sumR -> Empty_set.
Proof.
  intros w1 w2.
  destruct (res_cl w1 w2) as [cs cert].
  exact (twk_e cs cert).
Qed.

End EpiTransWitClosure.

(* L2 前提到 (c强) 终形的通道面（显式承载，本面暂无成员）：通道
   本体＝线性多项式证书到 real_metric 分离面的输送
   （lic_e_irrational_criterion 同型内容），随 L2 输入同批闭合；
   终形 epi_cond_face 逐字不动。 *)
Definition epi_cond_from_meas : Set :=
  TransWit_meas sumR -> epi_cond_face.

(* (b) 负言形闭合（Prop 脚手架层，同 §6 应用面）：两前提皆 Set 型，
   合取与存在的消去在 False 目标内完成。 *)
Theorem epi_trans_weak_closure_conj :
  (AlgWit prodR -> AlgWit sumR -> AlgWit eR) ->
  TransWit_weak eR -> ~ (AlgP prodR /\ AlgP sumR).
Proof.
  intros res_cl twk_e Hconj.
  destruct Hconj as [Hx Hy].
  destruct Hx as [w1 _].
  destruct Hy as [w2 _].
  destruct (epi_trans_weak_quad_exit res_cl twk_e w1 w2).
Qed.

(* (c弱) 条件弱形闭合：经 §6 currying 互等引理由 (b) 形单向送达
   （(b)≡(c弱) 纯逻辑互等在库）。 *)
Theorem epi_trans_weak_closure_curry :
  (AlgWit prodR -> AlgWit sumR -> AlgWit eR) ->
  TransWit_weak eR -> AlgP prodR -> ~ AlgP sumR.
Proof.
  intros res_cl twk_e.
  exact (epi_curry_forward prodR sumR
           (epi_trans_weak_closure_conj res_cl twk_e)).
Qed.

(* 分支选择面的反向障碍注记：供给→获解方向全量机器验证闭合——  
   析取见证即一支完全有效无理证明（§10 分支提取直连）。供给面
   自身的构造性成员资格为当代开放问题：e·π、e+π 无理性两支皆
   开放，判定原理族对单实例析取双向不通（单实例不含全称原理的
   代入位，逃逸窗口供给即开放问题）—机器验证不可达系数学现状
   使然，非工程失败。开放状态随三项触发条件重估：（一）e·π 或
   e+π 的无理性获证（经典证明亦可，给出构造化入口）；（二）
   Mahler 型有效测度在库；（三）发现 e·π 有理（与 e 超越性可
   相抵——二次逃逸），此时析取由右支闭合，全局重估。 *)
Theorem epi_or_supply_channel : epi_or_face -> epi_or_branch_data.
Proof. exact epi_or_face_to_branch_data. Qed.

(* 提取与公理面（续二） *)

Separate Extraction TransWit_weak TransWit_meas epi_cond_from_meas
  epi_trans_weak_quad_exit.

Print Assumptions epi_trans_weak_quad_exit.
Print Assumptions epi_trans_weak_closure_conj.
Print Assumptions epi_trans_weak_closure_curry.
Print Assumptions epi_or_supply_channel.
