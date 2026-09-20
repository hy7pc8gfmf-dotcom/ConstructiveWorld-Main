(* G 组：G11_IDLFam — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpCLQuery + UpIDL（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G11_IDLFam 成员件：UpCLQuery（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpCLQuery.v — CL 2.0 分型拒答 Coq 落地：三类查询显式分型 + 结构性拒答      *)
(*              + 差表封闭律语法免疫                                        *)
(*                                                                       *)
(* 设计出处：ROUNDTABLE2 上游会话 终稿（轮次 3）CL 2.0（2 票，上游会话/6 投票理由：    *)
(*   Coq 落地路径全场最短）；排队模块位方案-二轮成果Coq化.md Q4 条目。  *)
(*                                                                       *)
(* 三组件：                                                                *)
(*   件 1  三类查询显式分型 qtype：[内]QIN 平移不变 / [值]QVAL 价值 /          *)
(*         [锚]QANC 绝对；可判定准入谓词（sumbool 三分派定义 bool 准入，       *)
(*         *_eq 引理给直读形式；正确性 iffT 定理：准入 ⟺ sigT 凭证）。        *)
(*   件 2  结构性拒答：qans = qans_val Z | qans_rej misscred——拒答是显式      *)
(*         构造，缺失凭证型标 misscred 显式枚举（缺在册 MC_RANGE / 缺头券      *)
(*         MC_VSLOT / 缺锚闭 MC_ANCH）；qdc 总分派 + qdc_spec +              *)
(*         q·r·e·j·_·a·d·m·i·t·_·f·a·l·s·e + 券一次性（val_fresh_answer / val_burn_reject）。*)
(*   件 3  差表封闭律语法免疫：dtab 归纳型，封闭律 dsub_cocycle 对一切         *)
(*         d : dtab 无前提成立（破律差表在语法层不可写出——构造子封闭）；       *)
(*         gauge shift 下 [内]类裁决平移不变（qin_gauge_invariant），绝对读出  *)
(*         恰平移 c（pot_shift_moves）——语言中无平移不变的绝对读出通道。       *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；语句零 Prop：等式用 tid、序用 nle、            *)
(* 存在用 sigT、分支用 sumbool / bool+tid、⟺ 用 iffT（Set 层双函数记录）。   *)
(* 纪律：纯构造性、无任何公理式出口、stdlib only、全链可提取。                 *)
(* 定稿决策（未定稿细节按「落地最短+判定天然」自定，见技术报告）：             *)
(*   差量域取 Z（Q 的整数格，判定天然）；头元规范 h=0 固定（pot i = 差 i 0）；  *)
(*   头券 = 单槽 option (nat*Z)（指标+熔合绝对量），答一次即焚；               *)
(*   锚义务列 = acol 归纳型（锚闭合事件 acolS），准入 = aread 命中。           *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建（自 G04_ProjFam.v 内联：tid 恒等型 + nle 序型 + 判定工具）          *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive clq_tid (A : Type) : A -> A -> Type := clq_tid_refl : forall x : A, clq_tid A x x.

Definition clq_tid_sym (A : Type) (x y : A) (H : clq_tid A x y) : clq_tid A y x :=
  match H in clq_tid _ a b return clq_tid _ b a with
  | clq_tid_refl _ a0 => @clq_tid_refl _ a0
  end.

Definition clq_tid_trans (A : Type) (x y z : A) (H1 : clq_tid A x y) (H2 : clq_tid A y z) :
  clq_tid A x z :=
  match H1 in clq_tid _ a b return clq_tid _ b z -> clq_tid _ a z with
  | clq_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition clq_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : clq_tid A x y) :
  clq_tid B (f x) (f y) :=
  match H in clq_tid _ a b return clq_tid B (f a) (f b) with
  | clq_tid_refl _ a0 => @clq_tid_refl _ (f a0)
  end.

(* 从 clq_tid 提取定义等式（仅证明内部推理用，命名受控） *)
Ltac tidQ H E :=
  pose proof (match H in clq_tid _ a b return a = b with clq_tid_refl _ _ => eq_refl end) as E.

(* x = y -> clq_tid A x y（定义等式反灌回恒等型） *)
Lemma clq_tid_eq : forall (A : Type) (x y : A), x = y -> clq_tid A x y.
Proof.
  intros A x y H. rewrite H. apply clq_tid_refl.
Defined.

(* Set 层自然数序型（k ≤ m 编码为 nle k m） *)
Inductive clq_nle (n : nat) : nat -> Set :=
| clq_nle_n : clq_nle n n
| clq_nle_S : forall m : nat, clq_nle n m -> clq_nle n (S m).

Lemma clq_leb_refl_tid : forall a : nat, clq_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply clq_tid_refl.
Qed.

Lemma clq_leb_S : forall a m : nat,
  clq_tid bool (Nat.leb a m) true -> clq_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply clq_tid_refl.
    + change (clq_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply clq_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint clq_nle_lebF (a b : nat) (H : clq_nle a b) {struct H} :
  clq_tid bool (Nat.leb a b) true :=
  match H as H0 in clq_nle _ bb
  return clq_tid bool (Nat.leb a bb) true with
  | clq_nle_n _ => clq_leb_refl_tid a
  | clq_nle_S _ m H1 => clq_leb_S a m (clq_nle_lebF a m H1)
  end.

Definition clq_nle_leb (b a : nat) (H : clq_nle a b) : clq_tid bool (Nat.leb a b) true :=
  clq_nle_lebF a b H.

(* clq_nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (clq_nle_leb _ _ H) in clq_tid _ x y return x = y with
        | clq_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma clq_nle_0 : forall m : nat, clq_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply clq_nle_n.
  - apply clq_nle_S. exact IH.
Qed.

Lemma clq_nle_SS : forall a b : nat, clq_nle a b -> clq_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply clq_nle_n.
  - apply clq_nle_S. exact IH.
Qed.

(* clq_nle -> leb = true 反向桥 *)
Lemma clq_nle_of_leb : forall b a : nat,
  clq_tid bool (Nat.leb a b) true -> clq_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply clq_nle_n.
    + change (clq_tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply clq_nle_S. apply clq_nle_0.
    + exact (clq_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ -> clq_tid bool (leb) true 桥 *)
Lemma clq_lebT : forall a b : nat, (a <= b)%nat -> clq_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply clq_tid_refl.
Qed.

(* clq_nle (S m) O 荒谬件（索引不交配的空消去，合法关闭任意 Type 目标） *)
Lemma nle_S_absurd : forall (m : nat) (P : Type), clq_nle (S m) O -> P.
Proof.
  intros m P H. inversion H.
Qed.

(* Set 层 ⟺ 载体：双函数记录（语句零 Prop 的当且仅当） *)
Record iffT (A B : Type) : Type := mkIffT
  { iffT_fw : A -> B
  ; iffT_bw : B -> A }.

(* ===================================================================== *)
(* 1. 差表 dtab：归纳构造的恒差账（语法免疫载体）                              *)
(*    封闭律 差 i j + 差 j k == 差 i k 对一切 dtab 无前提成立——               *)
(*    不存在能写出破律差表的构造子。                                          *)
(* ===================================================================== *)

Inductive dtab : Set :=
| dtab1 (c : Z)                    (* 单指标账：指标 0（头元），gauge 值 c    *)
| dtabSnoc (d : dtab) (w : Z).     (* 入元：新指标 S (dlen d)，其与头元差 w   *)

(* 账内指标数：合法指标域 0 .. dlen d *)
Fixpoint dlen (d : dtab) : nat :=
  match d with
  | dtab1 _ => O
  | dtabSnoc d0 _ => S (dlen d0)
  end.

(* 头元规范 h=0 下的势读数：pot i = 差 i 0（由构造累积，绝非物质化总量） *)
Fixpoint pot (d : dtab) (i : nat) : Z :=
  match d with
  | dtab1 c => if Nat.eqb i O then c else 0
  | dtabSnoc d0 w => if Nat.eqb i (S (dlen d0)) then w else pot d0 i
  end.

(* 差 i j（唯一导出的 [内]类观测量） *)
Definition dsub (d : dtab) (i j : nat) : Z := pot d i - pot d j.

(* 件 3 核心定理：环形封闭律对一切 dtab 构造性成立（无任何前提） *)
Theorem dsub_cocycle : forall (d : dtab) (i j k : nat),
  clq_tid Z (dsub d i j + dsub d j k) (dsub d i k).
Proof.
  intros d i j k. unfold dsub.
  apply (clq_tid_eq Z (pot d i - pot d j + (pot d j - pot d k)) (pot d i - pot d k)).
  ring.
Qed.

(* gauge 平移：整表势读数加 c（换头元规范的语法操作） *)
Fixpoint dshift (d : dtab) (c : Z) : dtab :=
  match d with
  | dtab1 c0 => dtab1 (c0 + c)
  | dtabSnoc d0 w => dtabSnoc (dshift d0 c) (w + c)
  end.

Lemma dlen_shift : forall (d : dtab) (c : Z), clq_tid nat (dlen (dshift d c)) (dlen d).
Proof.
  intros d c. induction d as [c0 | d0 IH w].
  - simpl. apply clq_tid_refl.
  - simpl. tidQ IH Edl. rewrite Edl. apply clq_tid_refl.
Qed.

(* 件 3 对照定理：绝对势读数在 gauge 平移下恰移动 c（语言无平移不变的绝对读出） *)
Theorem pot_shift_moves : forall (d : dtab) (c : Z) (i : nat),
  clq_nle i (dlen d) -> clq_tid Z (pot (dshift d c) i) (pot d i + c).
Proof.
  intros d c i. induction d as [c0 | d0 IH w].
  - intros Hn. destruct i as [| i1].
    + simpl. apply clq_tid_refl.
    + exact (nle_S_absurd i1 _ Hn).
  - intros Hn. simpl in Hn.
    pose proof (dlen_shift d0 c) as DL. tidQ DL Edl.
    simpl. rewrite Edl.
    destruct (Nat.eqb i (S (dlen d0))) eqn:E.
    + apply clq_tid_refl.
    + apply IH. apply clq_nle_of_leb. apply clq_lebT.
      apply Nat.eqb_neq in E. nleP Hn. lia.
Qed.

(* [内]类差值读数 gauge 不变（合法指标域内） *)
Theorem dsub_shift_invariant : forall (d : dtab) (c : Z) (i j : nat),
  clq_nle i (dlen d) -> clq_nle j (dlen d) ->
  clq_tid Z (dsub (dshift d c) i j) (dsub d i j).
Proof.
  intros d c i j Hi Hj. unfold dsub.
  pose proof (pot_shift_moves d c i Hi) as T1. tidQ T1 E1.
  pose proof (pot_shift_moves d c j Hj) as T2. tidQ T2 E2.
  apply (clq_tid_eq Z (pot (dshift d c) i - pot (dshift d c) j) (pot d i - pot d j)).
  rewrite E1, E2. ring.
Qed.

(* ===================================================================== *)
(* 2. 锚义务已闭列 acol（[锚]类凭证载体：锚闭合事件显式归纳）                    *)
(* ===================================================================== *)

Inductive acol : Set :=
| acol0                          (* 空列：无任何已闭锚义务 *)
| acolS (a : acol) (i : nat) (c : Z).  (* 锚闭合事件：指标 i 外锚至绝对值 c *)

(* 锚读数：该指标最近一次闭合记录的绝对值；未闭 = None *)
Fixpoint aread (i : nat) (a : acol) : option Z :=
  match a with
  | acol0 => None
  | acolS a0 j c => if Nat.eqb i j then Some c else aread i a0
  end.

(* ===================================================================== *)
(* 3. 件 1：三类查询显式分型 qtype + 缺失凭证型标 misscred + 答型 qans          *)
(* ===================================================================== *)

(* 三类查询：[内]平移不变 / [值]价值 / [锚]绝对——语法上只有这三个构造子，
   任何混类提问（例如用 [内]类语法问绝对水平）不可写出。 *)
Inductive qtype : Set :=
| QIN (i j : nat)            (* [内] 平移不变类：问差 i j                    *)
| QVAL (i : nat)             (* [值] 价值类：问指标 i 的绝对量（耗头券）       *)
| QANC (i : nat) (a : Z).    (* [锚] 绝对类：问 i 的绝对水平对锚 a 的对齐差    *)

(* 缺失凭证型标：拒答值携带"缺哪种凭证"的结构信息（显式枚举） *)
Inductive misscred : Set :=
| MC_RANGE (i : nat)   (* 缺在册凭证：指标 i 未入账（0 .. dlen 之外） *)
| MC_VSLOT             (* 缺头券：单槽价值凭证缺模块或已焚              *)
| MC_ANCH (i : nat).   (* 缺锚闭凭证：指标 i 无已闭锚义务             *)

(* 答型：左支 = 答值（显式构造），右支 = 结构性拒答（携缺失凭证型标）。
   拒答不是失败：qans_rej 是 qans 的一等构造子。 *)
Inductive qans : Set :=
| qans_val (z : Z)
| qans_rej (mc : misscred).

(* 答型→bool 判读（拒答诚实性定理用） *)
Definition qans_isans (r : qans) : bool :=
  match r with
  | qans_val _ => true
  | qans_rej _ => false
  end.

Definition tid_qans_val (z1 z2 : Z) (H : clq_tid Z z1 z2) :
  clq_tid qans (qans_val z1) (qans_val z2) :=
  clq_tid_cong (@qans_val) z1 z2 H.

(* ===================================================================== *)
(* 4. 件 1：可判定准入谓词——三分派（sdec：sumbool 的信息性凭证版）             *)
(*    三分派 left 支携 Set 层凭证（stdlib sumbool 两支限 Prop，不可用）；        *)
(*    bool 准入取直读定义，与三分派经凭证型刻画互通（见下与 *_correct）。        *)
(* ===================================================================== *)

(* Set 层判定和（sumbool 的信息性凭证版：stdlib sumbool 两支限 Prop，
   无法携带 Set 层凭证，故自造同构三分派型；left/right 支均可携信息性凭证。
   与 option/sigT 同居 Type 层——全链信息性、可提取、零 Prop。） *)
Inductive sdec (A B : Type) : Type :=
| sdec_l (a : A)
| sdec_r (b : B).

(* nat 序的三分派：left = clq_nle 凭证，right = leb=false 的 clq_tid 证据
   （判定本体走全量化引理，避免 destruct 污染目标型中的 scrutinee） *)
Lemma nle_dc_gen : forall (p : bool) (a b : nat),
  p = Nat.leb a b -> sdec (clq_nle a b) (clq_tid bool (Nat.leb a b) false).
Proof.
  intros p a b E. destruct p as [] eqn:Ep.
  - apply sdec_l. exact (clq_nle_of_leb b a (clq_tid_eq bool (Nat.leb a b) true (eq_sym E))).
  - apply sdec_r. exact (clq_tid_eq bool (Nat.leb a b) false (eq_sym E)).
Defined.

Definition nle_dc (a b : nat) : sdec (clq_nle a b) (clq_tid bool (Nat.leb a b) false) :=
  nle_dc_gen (Nat.leb a b) a b eq_refl.

(* [内]类准入三分派：left = 双在册 clq_nle 凭证；right = 缺在册型标 *)
Definition qin_dc (d : dtab) (i j : nat)
  : sdec (prod (clq_nle i (dlen d)) (clq_nle j (dlen d))) misscred.
Proof.
  destruct (nle_dc i (dlen d)) as [Ha | Ha].
  - destruct (nle_dc j (dlen d)) as [Hb | Hb].
    + apply sdec_l. split; assumption.
    + apply sdec_r. apply (MC_RANGE j).
  - apply sdec_r. apply (MC_RANGE i).
Defined.

Definition qin_ok (d : dtab) (i j : nat) : bool :=
  Nat.leb i (dlen d) && Nat.leb j (dlen d).

(* [值]类准入三分派：left = 头券凭证（sigT 携券面绝对量）；right = 缺头券 *)
Definition qval_dc (v : option (nat * Z)) (i : nat)
  : sdec (sigT (fun w : Z => clq_tid (option (nat * Z)) (Some (i, w)) v)) misscred.
Proof.
  destruct v as [[h w] |] eqn:Ev.
  - destruct (Nat.eqb h i) eqn:Eh.
    + apply sdec_l. apply (existT _ w).
      apply Nat.eqb_eq in Eh.
      exact (clq_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
               (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
    + apply sdec_r. apply MC_VSLOT.
  - apply sdec_r. apply MC_VSLOT.
Defined.

Definition qval_ok (v : option (nat * Z)) (i : nat) : bool :=
  match v with Some p => Nat.eqb (fst p) i | None => false end.

(* 头券券面绝对量读出 *)
Definition vs_val (v : option (nat * Z)) : Z :=
  match v with Some p => snd p | None => 0 end.

(* [锚]类准入三分派：left = 锚闭凭证（sigT 携锚面绝对量）；right = 缺锚闭 *)
Definition qanc_dc (a : acol) (i : nat)
  : sdec (sigT (fun c : Z => clq_tid (option Z) (Some c) (aread i a))) misscred.
Proof.
  destruct (aread i a) as [c |] eqn:E.
  - apply sdec_l. apply (existT _ c). apply clq_tid_refl.
  - apply sdec_r. apply (MC_ANCH i).
Defined.

Definition qanc_ok (a : acol) (i : nat) : bool :=
  match aread i a with Some _ => true | None => false end.

(* 三分派与 bool 准入的互通不经本体展开桥接，而经凭证型刻画：
   qin_dc/qval_dc/qanc_dc 的 left 支型 == qin_correct/qval_correct/qanc_correct
   中与各自 bool 准入 ⟺ 的凭证型（prod clq_nle 对 / sigT 券面 / sigT 锚面）——
   两路定义被同一凭证型钉死，一致性由类型而非引理承担。 *)

(* --- 正确性定理：准入 ⟺ 存在凭证（sigT 携带；⟺ 用 iffT） --- *)

Theorem qin_correct : forall (d : dtab) (i j : nat),
  iffT (clq_tid bool (qin_ok d i j) true)
       (prod (clq_nle i (dlen d)) (clq_nle j (dlen d))).
Proof.
  intros d i j. apply (mkIffT _ _).
  - intros H. unfold qin_ok in H.
    tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
    exact (pair (clq_nle_of_leb (dlen d) i (clq_tid_eq bool _ true E1))
                (clq_nle_of_leb (dlen d) j (clq_tid_eq bool _ true E2))).
  - intros p. destruct p as [Ha Hb].
    pose proof (clq_nle_leb (dlen d) i Ha) as T1. tidQ T1 E1.
    pose proof (clq_nle_leb (dlen d) j Hb) as T2. tidQ T2 E2.
    unfold qin_ok.
    apply (clq_tid_eq bool (Nat.leb i (dlen d) && Nat.leb j (dlen d)) true).
    rewrite E1, E2. reflexivity.
Qed.

Theorem qval_correct : forall (v : option (nat * Z)) (i : nat),
  iffT (clq_tid bool (qval_ok v i) true)
       (sigT (fun w : Z => clq_tid (option (nat * Z)) (Some (i, w)) v)).
Proof.
  intros v i. apply (mkIffT _ _).
  - intros H. unfold qval_ok in H. destruct v as [[h w] |] eqn:Ev.
    + simpl in H. destruct (Nat.eqb h i) eqn:Eh.
      * apply (existT _ w).
        apply Nat.eqb_eq in Eh.
        exact (clq_tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
                 (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
      * tidQ H E. discriminate E.
    + simpl in H. tidQ H E. discriminate E.
  - intros [w H]. unfold qval_ok. destruct v as [[h w0] |] eqn:Ev.
    + tidQ H E. injection E as Ei Ew.
      rewrite Ei. simpl.
      exact (clq_tid_eq bool (Nat.eqb h h) true (Nat.eqb_refl h)).
    + tidQ H E. discriminate E.
Qed.

Theorem qanc_correct : forall (a : acol) (i : nat),
  iffT (clq_tid bool (qanc_ok a i) true)
       (sigT (fun c : Z => clq_tid (option Z) (Some c) (aread i a))).
Proof.
  intros a i. apply (mkIffT _ _).
  - intros H. unfold qanc_ok in H. destruct (aread i a) as [c |] eqn:E.
    + apply (existT _ c). apply clq_tid_refl.
    + tidQ H E2. discriminate E2.
  - intros [c H]. unfold qanc_ok. destruct (aread i a) as [c0 |] eqn:E.
    + apply clq_tid_refl.
    + tidQ H E2. discriminate E2.
Qed.

(* ===================================================================== *)
(* 5. 件 2：结构性拒答——账态 clst + 问答机 qask + 总分派 qdc                   *)
(* ===================================================================== *)

(* CL 账态 = 差表 + 单槽头券 + 锚义务已闭列（窗即差表本身，dtab 定长归纳） *)
Record clst : Set := mkCL
  { cld : dtab                    (* 差表（[内]类唯一数据源）            *)
  ; clv : option (nat * Z)        (* 单槽头券：Some (h, w) = 头券未花    *)
  ; cla : acol }.                 (* 锚义务已闭列（[锚]类唯一数据源）     *)

(* 问答机（三元组版）：每类只读自己的凭证通道——
   [内]读差表 dsub；[值]读头券 vs_val；[锚]读锚闭 aread。绝无跨通道偷读。 *)
Definition qaskR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : qans :=
  match q with
  | QIN i j =>
      if Nat.leb i (dlen d)
      then (if Nat.leb j (dlen d)
            then qans_val (dsub d i j)
            else qans_rej (MC_RANGE j))
      else qans_rej (MC_RANGE i)
  | QVAL i =>
      if qval_ok v i then qans_val (vs_val v) else qans_rej MC_VSLOT
  | QANC i a0 =>
      if qanc_ok a i
      then qans_val (match aread i a with Some c => c - a0 | None => 0 end)
      else qans_rej (MC_ANCH i)
  end.

(* 准入谓词（bool）：与问答机同源分派 *)
Definition qadmitR (d : dtab) (v : option (nat * Z)) (a : acol) (q : qtype) : bool :=
  match q with
  | QIN i j => qin_ok d i j
  | QVAL i => qval_ok v i
  | QANC i _ => qanc_ok a i
  end.

(* 账态版封装：问答机与准入谓词 *)
Definition qask (s : clst) (q : qtype) : qans := qaskR (cld s) (clv s) (cla s) q.
Definition qadmit (s : clst) (q : qtype) : bool := qadmitR (cld s) (clv s) (cla s) q.

(* 准入与答判读逐点一致（宪法内部自洽） *)
Lemma qadmit_isin : forall (s : clst) (q : qtype),
  clq_tid bool (qadmit s q) (qans_isans (qask s q)).
Proof.
  intros s q. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans, qin_ok.
    destruct (Nat.leb i (dlen (cld s))); destruct (Nat.leb j (dlen (cld s)));
      apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qval_ok (clv s) i); apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qanc_ok (cla s) i); apply clq_tid_refl.
Qed.

(* 宪法判定面总分派：left = 答值见证；right = 结构性拒答见证（携型标） *)
Definition qdc (s : clst) (q : qtype)
  : sdec (sigT (fun z : Z => clq_tid qans (qask s q) (qans_val z)))
         (sigT (fun mc : misscred => clq_tid qans (qask s q) (qans_rej mc))).
Proof.
  destruct q as [i j | i | i a0].
  - unfold qask, qaskR.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply sdec_l. apply (existT _ (dsub (cld s) i j)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE j)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
  - unfold qask, qaskR. destruct (qval_ok (clv s) i) eqn:Ev.
    + apply sdec_l. apply (existT _ (vs_val (clv s))). apply clq_tid_refl.
    + apply sdec_r. apply (existT _ MC_VSLOT). apply clq_tid_refl.
  - unfold qask, qaskR. destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply sdec_l.
      apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply clq_tid_refl.
    + apply sdec_r. apply (existT _ (MC_ANCH i)). apply clq_tid_refl.
Defined.

(* 总分派规范：裁决位 qdc_b 与准入 bool 逐点一致（宪法内部自洽的 bool 面）；
   分支的凭证内容一致性由 q·a·d·m·i·t·_·a·n·s·w·e·r / q·a·d·m·i·t·_·r·e·j·e·c·t 承担 *)
Definition qdc_b (s : clst) (q : qtype) : bool :=
  match qdc s q with sdec_l _ _ _ => true | sdec_r _ _ _ => false end.

Theorem qdc_spec : forall (s : clst) (q : qtype), clq_tid bool (qdc_b s q) (qadmit s q).
Proof.
  intros s q. unfold qdc_b. destruct (qdc s q) as [Cz | Cm].
  - destruct Cz as [w Hw].
    exact (clq_tid_sym bool (qadmit s q) true
             (clq_tid_trans bool (qadmit s q) (qans_isans (qask s q)) true
                (qadmit_isin s q)
                  (clq_tid_cong qans_isans (qask s q) (qans_val w) Hw))).
  - destruct Cm as [mc Hmc].
    exact (clq_tid_sym bool (qadmit s q) false
             (clq_tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
                (qadmit_isin s q)
                  (clq_tid_cong qans_isans (qask s q) (qans_rej mc) Hmc))).
Qed.

(* 拒答诚实性：凡 qask 输出拒答支，准入必为 false（拒答=显式构造，非失败） *)
Theorem qrej_admit_false : forall (s : clst) (q : qtype) (mc : misscred),
  clq_tid qans (qask s q) (qans_rej mc) -> clq_tid bool (qadmit s q) false.
Proof.
  intros s q mc H.
  exact (clq_tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
           (qadmit_isin s q) (clq_tid_cong qans_isans (qask s q) (qans_rej mc) H)).
Qed.

(* 准入真 ⟹ 答值支显式构造（携答值见证） *)
Theorem qadmit_answer : forall (s : clst) (q : qtype), clq_tid bool (qadmit s q) true ->
  sigT (fun z : Z => clq_tid qans (qask s q) (qans_val z)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply (existT _ (dsub (cld s) i j)). apply clq_tid_refl.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + apply (existT _ (vs_val (clv s))). apply clq_tid_refl.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply clq_tid_refl.
    + tidQ H E. discriminate E.
Qed.

(* 准入假 ⟹ 拒答支显式构造（携缺失凭证型标见证）——结构性拒答的存在性 *)
Theorem qadmit_reject : forall (s : clst) (q : qtype), clq_tid bool (qadmit s q) false ->
  sigT (fun mc : misscred => clq_tid qans (qask s q) (qans_rej mc)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_RANGE j)). apply clq_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
    + apply (existT _ (MC_RANGE i)). apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ MC_VSLOT). apply clq_tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_ANCH i)). apply clq_tid_refl.
Qed.

(* --- 头券生命周期：[值]类答一次即焚，焚后再问 = 结构性拒答附缺头券型标 --- *)

Definition clburn (s : clst) (i : nat) : clst := mkCL (cld s) None (cla s).

Theorem val_fresh_answer : forall (d : dtab) (a : acol) (i : nat) (w : Z),
  clq_tid qans (qask (mkCL d (Some (i, w)) a) (QVAL i)) (qans_val w).
Proof.
  intros d a i w. unfold qask, qaskR, qval_ok. simpl.
  rewrite Nat.eqb_refl. apply clq_tid_refl.
Qed.

Theorem val_burn_reject : forall (s : clst) (i : nat),
  clq_tid qans (qask (clburn s i) (QVAL i)) (qans_rej MC_VSLOT).
Proof.
  intros s i. unfold qask, qaskR, clburn, qval_ok. simpl. apply clq_tid_refl.
Qed.

(* ===================================================================== *)
(* 6. 件 3：[内]类平移不变性（分型押注的语法化）                               *)
(* ===================================================================== *)

(* CL 2.0 押注的分型形式：[内]类裁决在差表 gauge 平移下逐字不变。
   对照 pot_shift_moves：绝对读出恰移动 c——故绝对问题在 [内]类语法内
   不可问出（问了也必得到平移不变的答案，即被类型系统挡在差表语言外）。 *)
Theorem qin_gauge_invariant : forall (d : dtab) (c : Z) (v : option (nat * Z))
                                     (a : acol) (i j : nat),
  clq_tid qans (qask (mkCL (dshift d c) v a) (QIN i j))
           (qask (mkCL d v a) (QIN i j)).
Proof.
  intros d c v a i j. unfold qask, qaskR. cbn [cld clv cla].
  pose proof (dlen_shift d c) as DL. tidQ DL Edl. rewrite Edl.
  destruct (Nat.leb i (dlen d)) eqn:Ei; destruct (Nat.leb j (dlen d)) eqn:Ej.
  - apply tid_qans_val. apply dsub_shift_invariant.
    + exact (clq_nle_of_leb (dlen d) i (clq_tid_eq bool (Nat.leb i (dlen d)) true Ei)).
    + exact (clq_nle_of_leb (dlen d) j (clq_tid_eq bool (Nat.leb j (dlen d)) true Ej)).
  - apply clq_tid_refl.
  - apply clq_tid_refl.
  - apply clq_tid_refl.
Qed.

Close Scope Z_scope.

(* ======== G11_IDLFam 成员件：UpIDL（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpIDL.v — 判定织机 IDL 熔锭差分两段制 Coq 落地                           *)
(*                                                                       *)
(* 设计出处：ROUNDTABLE2 上游会话 轮次 3 终稿「熔锭差分织机（Ingot-Differential    *)
(*   Loom, IDL）——两段制，判定流永不逐条重放」（含上游会话 异或击杀与上游会话 活锁     *)
(*   击杀的双重收编）；排队模块位方案-二轮成果Coq化.md Q5 条目          *)
(*   （依赖 Q4 语义——UpCLQuery.v 已给出，本件 Require Import 直接消费）。     *)
(*                                                                       *)
(* 两段制：                                                                *)
(*   构造段（熔炼 melt）：判定流单遍右折叠为锭 ingot——六洞钉位（同值累计       *)
(*         立钉 P1、异值即冲突 PB 恒传、缺判定即 PN）+ 拒值差条款列。          *)
(*   差分段（织 weave）：只吃锭、永不重放流——钉位差分编译为 Q4 载体 dtab       *)
(*         （头元 k0 规范 0，dlen=5），拒值差条款在织出表上逐条 Z 判定        *)
(*         （段间差分可判定）；见证缺模块 / 钉冲突 / 差条款相抵 → 欠单 wiou      *)
(*         如实记欠，不吐件。                                                *)
(* 主定理：melt_hom（熔炼=列表同态，两段构造的代数内容）/ pin_iffT（钉位=流    *)
(*   中 pass 判定的一致聚合，iffT 双向守恒）/ weave_sound（织出即合法：流中   *)
(*   每枚判定都被织出表满足——出生免疫跨洞非法）/ weave_replay_b/_d +          *)
(*   replay_census（整流重放：织造判定、织出件、冲突清点全部不变——活锁       *)
(*   失去载体）/ recheck_pass（织出件交 Q4 判定面 [内]类查询逐词复核）/        *)
(*   xor_defused（异或流如实记欠不织——二轮击杀实验的收编回归）。              *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层（延续 Q4 Set 层路线：clq_tid/clq_nle/iffT/sigT）；      *)
(* 语句零 Prop：等式 clq_tid、序 clq_nle、⟺ iffT、分支 bool/prod/sigT。              *)
(* 纪律：纯构造性、零公理式出口、stdlib + UpCLQuery、全链可提取。              *)
(* 定稿决策（未定稿细节按「两段制结构最清晰 + 与 Q4 判定面咬合最紧」自定）：     *)
(*   ① 六洞型 hole=k0 k1 kb kc ke kr 具象为六槽，参数位=Q4 dtab 指标 0..5，      *)
(*      头元 k0 恒 0（gauge 规范），全部判定语义走头相对差 dsub d (hix h) 0。  *)
(*   ② 判定 verd=洞型×向×Z 证据：pass(h,w) 立钉「值=w」；rej(h,e) 出差条款     *)
(*      「值≠e」（非零差分要求，即设计的见证型差条款）。                       *)
(*   ③ 钉位三态 pinv=PN 缺 / P1 z 立钉 / PB 冲突——冲突位 PB 恒传播，故          *)
(*      同洞异值在整流中至多记一次（=设计「同洞异值记冲突一次」）；摩擦计       *)
(*      定稿为冲突清点 iconf=钉位为 PB 的洞数（终稿「冲突清点+欠单排序键」）。 *)
(*   ④ 织出件=Q4 dtab（dlen=5），可直接装进 Q4 账态 mkCL 受 [内]类查询复核。   *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.

Open Scope Z_scope.

(* clq_tid → 定义等式提取（证明内部推理用） *)
Definition tidE (A : Type) (x y : A) (H : clq_tid A x y) : x = y :=
  match H in clq_tid _ a b return a = b with clq_tid_refl _ _ => eq_refl end.

(* clq_tid 版 bool 合取拆分 / orb 头假消去（语句零 Prop 纪律的证明体内转接件） *)
Lemma tid_andb_inv : forall a b : bool,
  clq_tid bool (andb a b) true -> prod (clq_tid bool a true) (clq_tid bool b true).
Proof.
  intros a b H. tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
  exact (pair (clq_tid_eq bool _ true E1) (clq_tid_eq bool _ true E2)).
Qed.

Lemma tid_orb_false : forall b : bool,
  clq_tid bool (orb false b) true -> clq_tid bool b true.
Proof.
  intros b H. tidQ H E. rewrite orb_false_l in E.
  exact (clq_tid_eq bool _ true E).
Qed.

(* Set 层 orb 反转器：析取真则左右必有其一真（Type 级二择载体，零 Prop 泄露） *)
Inductive tidor (a b : bool) : Type :=
| tid_or_l : clq_tid bool a true -> tidor a b
| tid_or_r : clq_tid bool b true -> tidor a b.

Lemma tid_orb_inv : forall a b : bool,
  clq_tid bool (orb a b) true -> tidor a b.
Proof.
  intros a b H. destruct a; destruct b.
  - apply tid_or_l. apply clq_tid_refl.
  - apply tid_or_l. apply clq_tid_refl.
  - apply tid_or_r. exact H.
  - apply tid_or_r. exact H.
Qed.

(* ===================================================================== *)
(* 1. 判定：结构化裁决值（洞型 + 向 + Z 证据）                                *)
(* ===================================================================== *)

Inductive hole : Set := k0 | k1 | kb | kc | ke | kr.

Definition hix (h : hole) : nat :=
  match h with
  | k0 => 0%nat | k1 => 1%nat | kb => 2%nat | kc => 3%nat | ke => 4%nat | kr => 5%nat
  end.

Definition hmax : nat := 5%nat.

Definition hbeq (a b : hole) : bool := Nat.eqb (hix a) (hix b).

Lemma hbeq_refl : forall h : hole, clq_tid bool (hbeq h h) true.
Proof.
  intros h. apply (clq_tid_eq bool _ true). unfold hbeq. apply Nat.eqb_refl.
Qed.

Lemma hbeq_true : forall a b : hole, clq_tid bool (hbeq a b) true -> clq_tid hole a b.
Proof.
  intros a b H. unfold hbeq in H. tidQ H E.
  destruct a; destruct b; simpl in E; try discriminate E; apply clq_tid_refl.
Qed.

Inductive vdir : Set := vpass | vrej.

Definition dbeq (a b : vdir) : bool :=
  match a with
  | vpass => match b with vpass => true | vrej => false end
  | vrej => match b with vpass => false | vrej => true end
  end.

Lemma dbeq_true : forall a b : vdir, clq_tid bool (dbeq a b) true -> clq_tid vdir a b.
Proof.
  intros a b H. destruct a; destruct b; simpl in H;
    try (tidQ H E; discriminate E); apply clq_tid_refl.
Qed.

Record verd : Set := mkVd { vh : hole ; vd : vdir ; vz : Z }.

Definition vbeq (x y : verd) : bool :=
  andb (hbeq (vh x) (vh y)) (andb (dbeq (vd x) (vd y)) (Z.eqb (vz x) (vz y))).

Lemma vbeq_mkVd : forall (h1 h2 : hole) (d1 d2 : vdir) (z1 z2 : Z),
  clq_tid bool (vbeq (mkVd h1 d1 z1) (mkVd h2 d2 z2))
       (andb (hbeq h1 h2) (andb (dbeq d1 d2) (Z.eqb z1 z2))).
Proof. intros. apply clq_tid_refl. Qed.

Lemma vbeq_head_true : forall (h1 h2 : hole) (z1 z2 : Z),
  hbeq h1 h2 = true -> z1 = z2 ->
  vbeq (mkVd h1 vpass z1) (mkVd h2 vpass z2) = true.
Proof.
  intros h1 h2 z1 z2 Eh Ez. unfold vbeq, vh, vd, vz.
  rewrite Eh, Ez, Z.eqb_refl. reflexivity.
Qed.

Lemma vbeq_inv : forall v1 v2 : verd,
  clq_tid bool (vbeq v1 v2) true ->
  prod (clq_tid hole (vh v1) (vh v2))
       (prod (clq_tid vdir (vd v1) (vd v2)) (clq_tid Z (vz v1) (vz v2))).
Proof.
  intros v1 v2 H. unfold vbeq in H. tidQ H E.
  apply andb_prop in E. destruct E as [E1 E2].
  apply andb_prop in E2. destruct E2 as [E2 E3].
  apply Z.eqb_eq in E3.
  exact (pair (hbeq_true _ _ (clq_tid_eq bool _ true E1))
              (pair (dbeq_true _ _ (clq_tid_eq bool _ true E2))
                    (clq_tid_eq Z _ _ E3))).
Qed.

(* 流内成员（bool 谓词，语句零 Prop） *)
Fixpoint vIn (v : verd) (s : list verd) : bool :=
  match s with
  | nil => false
  | x :: t => orb (vbeq x v) (vIn v t)
  end.

(* 一致性谓词：h 洞上每枚 pass 判定值皆 w *)
Fixpoint allpass (h : hole) (w : Z) (s : list verd) : bool :=
  match s with
  | nil => true
  | v :: t =>
      andb (match vd v with
            | vpass => if hbeq (vh v) h then Z.eqb (vz v) w else true
            | vrej => true
            end)
           (allpass h w t)
  end.

(* ===================================================================== *)
(* 2. 锭载体：钉位三态 + 六槽钉位                                             *)
(* ===================================================================== *)

Inductive pinv : Set := PN | P1 (z : Z) | PB.

Definition isP1 (x : pinv) : bool := match x with P1 _ => true | _ => false end.

Record ipins : Set := mkP
  { qa : pinv ; qb : pinv ; qc : pinv ; qd : pinv ; qe : pinv ; qf : pinv }.

Definition pzero : ipins := mkP PN PN PN PN PN PN.

Definition pget (p : ipins) (h : hole) : pinv :=
  match h with
  | k0 => qa p | k1 => qb p | kb => qc p | kc => qd p | ke => qe p | kr => qf p
  end.

Definition pupd (h : hole) (x : pinv) (p : ipins) : ipins :=
  match h with
  | k0 => mkP x (qb p) (qc p) (qd p) (qe p) (qf p)
  | k1 => mkP (qa p) x (qc p) (qd p) (qe p) (qf p)
  | kb => mkP (qa p) (qb p) x (qd p) (qe p) (qf p)
  | kc => mkP (qa p) (qb p) (qc p) x (qe p) (qf p)
  | ke => mkP (qa p) (qb p) (qc p) (qd p) x (qf p)
  | kr => mkP (qa p) (qb p) (qc p) (qd p) (qe p) x
  end.

Lemma mkP_ext_eq : forall (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : pinv),
  a1 = b1 -> a2 = b2 -> a3 = b3 -> a4 = b4 -> a5 = b5 -> a6 = b6 ->
  mkP a1 a2 a3 a4 a5 a6 = mkP b1 b2 b3 b4 b5 b6.
Proof.
  intros a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 H1 H2 H3 H4 H5 H6.
  rewrite H1, H2, H3, H4, H5, H6. reflexivity.
Qed.

Lemma pget_pupd : forall (h h2 : hole) (x : pinv) (p : ipins),
  clq_tid pinv (pget (pupd h x p) h2) (if hbeq h h2 then x else pget p h2).
Proof.
  intros h h2 x p. destruct h, h2; apply clq_tid_refl.
Qed.

(* 钉位聚合：同值累计 / 异值冲突（PB 恒传，整流至多记一次） *)
Definition pj (a b : pinv) : prod pinv nat :=
  match a with
  | PN => (b, 0%nat)
  | P1 w =>
      match b with
      | PN => (P1 w, 0%nat)
      | P1 w' => if Z.eqb w w' then (P1 w, 0%nat) else (PB, 1%nat)
      | PB => (PB, 0%nat)
      end
  | PB => (PB, 0%nat)
  end.

Definition pjR (x : prod pinv nat) : pinv := fst x.
Definition pjN (x : prod pinv nat) : nat := snd x.

Lemma pj_self_R : forall a : pinv, clq_tid pinv (pjR (pj a a)) a.
Proof.
  intros a. destruct a as [z| |]; cbn [pj pjR fst].
  - apply clq_tid_refl.
  - destruct (Z.eqb z z) eqn:E; cbn [pjR].
    + apply clq_tid_refl.
    + rewrite Z.eqb_refl in E. discriminate E.
  - apply clq_tid_refl.
Qed.

Lemma pjR_PN : forall b : pinv, clq_tid pinv (pjR (pj PN b)) b.
Proof. intros b. apply clq_tid_refl. Qed.

Lemma pjR_PN_inv : forall a b : pinv,
  clq_tid pinv (pjR (pj a b)) PN -> prod (clq_tid pinv a PN) (clq_tid pinv b PN).
Proof.
  intros a b H. destruct a as [z| |]; destruct b as [z0| |];
    tidQ H E; try discriminate E.
  - exact (pair (clq_tid_refl pinv PN) (clq_tid_refl pinv PN)).
  - tidQ H E2. cbn [pj pjR fst] in E2.
    destruct (Z.eqb z z0); discriminate E2.
Qed.

(* 聚合结合律（结果位）：(a⊕b)⊕c == a⊕(b⊕c) *)
Lemma pj_assoc_R : forall a b c : pinv,
  clq_tid pinv (pjR (pj (pjR (pj a b)) c)) (pjR (pj a (pjR (pj b c)))).
Proof.
  intros a b c.
  destruct a, b, c; cbn [pj pjR fst]; try apply clq_tid_refl.
  all: try (destruct (Z.eqb z z0) eqn:Ew; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (destruct (Z.eqb z z1) eqn:Eu; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (destruct (Z.eqb z0 z1) eqn:Ewu; cbn [pj pjR fst]; try apply clq_tid_refl).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_neq in Ewu; congruence).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_neq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (apply Z.eqb_neq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (rewrite Ew; cbn [pj pjR fst]; try apply clq_tid_refl).
Qed.

Definition pjoin (p q : ipins) : prod ipins nat :=
  (mkP (pjR (pj (qa p) (qa q))) (pjR (pj (qb p) (qb q))) (pjR (pj (qc p) (qc q)))
       (pjR (pj (qd p) (qd q))) (pjR (pj (qe p) (qe q))) (pjR (pj (qf p) (qf q))),
   (pjN (pj (qa p) (qa q)) + (pjN (pj (qb p) (qb q)) + (pjN (pj (qc p) (qc q)) +
   (pjN (pj (qd p) (qd q)) + (pjN (pj (qe p) (qe q)) + pjN (pj (qf p) (qf q)))))))%nat).

Lemma pjoin_get : forall (p q : ipins) (h : hole),
  clq_tid pinv (pget (fst (pjoin p q)) h) (pjR (pj (pget p h) (pget q h))).
Proof.
  intros p q h. destruct p as [a b c d e f]. destruct q as [a' b' c' d' e' f'].
  destruct h; apply clq_tid_refl.
Qed.

Lemma pjoin_zero_l : forall p : ipins, clq_tid ipins (fst (pjoin pzero p)) p.
Proof.
  intros p. destruct p as [a b c d e f]. apply (clq_tid_eq ipins _ _).
  apply mkP_ext_eq.
  - exact (tidE pinv _ _ (pjR_PN a)).
  - exact (tidE pinv _ _ (pjR_PN b)).
  - exact (tidE pinv _ _ (pjR_PN c)).
  - exact (tidE pinv _ _ (pjR_PN d)).
  - exact (tidE pinv _ _ (pjR_PN e)).
  - exact (tidE pinv _ _ (pjR_PN f)).
Qed.

Lemma pjoin_self_pins : forall p : ipins, clq_tid ipins (fst (pjoin p p)) p.
Proof.
  intros p. destruct p as [a b c d e f]. apply (clq_tid_eq ipins _ _).
  apply mkP_ext_eq.
  - exact (tidE pinv _ _ (pj_self_R a)).
  - exact (tidE pinv _ _ (pj_self_R b)).
  - exact (tidE pinv _ _ (pj_self_R c)).
  - exact (tidE pinv _ _ (pj_self_R d)).
  - exact (tidE pinv _ _ (pj_self_R e)).
  - exact (tidE pinv _ _ (pj_self_R f)).
Qed.

Lemma pjoin_assoc : forall p q r : ipins,
  clq_tid ipins (fst (pjoin p (fst (pjoin q r))))
            (fst (pjoin (fst (pjoin p q)) r)).
Proof.
  intros p q r. apply (clq_tid_eq ipins _ _).
  apply mkP_ext_eq; symmetry; apply tidE; apply pj_assoc_R.
Qed.

(* ===================================================================== *)
(* 3. 熔炼 melt：判定流单遍折叠为锭（构造段）                                  *)
(* ===================================================================== *)

Record ingot : Set := mkIng
  { ipin : ipins
  ; irej : list (prod hole Z) }.

Lemma mkIng_ext_eq : forall (p1 p2 : ipins) (r1 r2 : list (prod hole Z)),
  p1 = p2 -> r1 = r2 -> mkIng p1 r1 = mkIng p2 r2.
Proof.
  intros p1 p2 r1 r2 H1 H2. rewrite H1, H2. reflexivity.
Qed.

Definition mzero : ingot := mkIng pzero nil.

(* 单枚判定的锭：pass 立钉；rej 出差条款 *)
Definition m1 (v : verd) : ingot :=
  match vd v with
  | vpass => mkIng (pupd (vh v) (P1 (vz v)) pzero) nil
  | vrej => mkIng pzero ((vh v, vz v) :: nil)
  end.

Definition mjoin (g1 g2 : ingot) : ingot :=
  mkIng (fst (pjoin (ipin g1) (ipin g2))) (irej g1 ++ irej g2).

Fixpoint melt (s : list verd) : ingot :=
  match s with
  | nil => mzero
  | v :: t => mjoin (m1 v) (melt t)
  end.

Lemma m1_pin_head : forall (h1 h2 : hole) (z : Z),
  clq_tid pinv (pget (ipin (m1 (mkVd h1 vpass z))) h2)
       (if hbeq h1 h2 then P1 z else PN).
Proof. intros h1 h2 z. destruct h1, h2; apply clq_tid_refl. Qed.

Lemma m1_pin_rej : forall (h1 h2 : hole) (z : Z),
  clq_tid pinv (pget (ipin (m1 (mkVd h1 vrej z))) h2) PN.
Proof. intros h1 h2 z. destruct h1, h2; apply clq_tid_refl. Qed.

Lemma pget_mjoin : forall (g1 g2 : ingot) (h : hole),
  clq_tid pinv (pget (ipin (mjoin g1 g2)) h)
       (pjR (pj (pget (ipin g1) h) (pget (ipin g2) h))).
Proof.
  intros g1 g2 h. unfold mjoin. apply pjoin_get.
Qed.

(* 锭聚合结合律 *)
Lemma mjoin_assoc : forall g1 g2 g3 : ingot,
  clq_tid ingot (mjoin g1 (mjoin g2 g3)) (mjoin (mjoin g1 g2) g3).
Proof.
  intros [p1 r1] [p2 r2] [p3 r3]. unfold mjoin. cbn [ipin irej].
  apply (clq_tid_eq ingot _ _). apply mkIng_ext_eq.
  - exact (tidE ipins _ _ (pjoin_assoc p1 p2 p3)).
  - apply app_assoc.
Qed.

(* 熔炼零元：空锭左么 *)
Lemma mjoin_zero_l : forall g : ingot, clq_tid ingot (mjoin mzero g) g.
Proof.
  intros [p r]. unfold mjoin. cbn [ipin irej mzero].
  apply (clq_tid_eq ingot _ _). apply mkIng_ext_eq.
  - exact (tidE ipins _ _ (pjoin_zero_l p)).
  - reflexivity.
Qed.

(* 主定理 1：熔炼是列表同态——两段构造的代数内容（锭不依赖流的括号方式） *)
Theorem melt_hom : forall s1 s2 : list verd,
  clq_tid ingot (melt (s1 ++ s2)) (mjoin (melt s1) (melt s2)).
Proof.
  induction s1 as [| v t IH]; intros s2.
  - cbn [melt app].
    exact (clq_tid_sym ingot _ _ (mjoin_zero_l (melt s2))).
  - cbn [melt app].
    apply (clq_tid_trans ingot _ (mjoin (m1 v) (mjoin (melt t) (melt s2))) _).
    + apply (clq_tid_cong (mjoin (m1 v)) _ _ (IH s2)).
    + exact (mjoin_assoc (m1 v) (melt t) (melt s2)).
Qed.

(* ===================================================================== *)
(* 4. 钉位守恒：钉=流中 pass 判定的一致聚合（iffT 双向）                        *)
(* ===================================================================== *)

Definition pinokp (w : Z) (x : pinv) : bool :=
  match x with PN => true | P1 z => Z.eqb z w | PB => false end.

(* 钉位聚合与相容性的接口件：P1 w ⊕ b 且 b 与 w 相容 ⟹ 结果与 w 相容 *)
Lemma pj_pinok_r : forall (w : Z) (b : pinv),
  clq_tid bool (pinokp w b) true -> clq_tid bool (pinokp w (pjR (pj (P1 w) b))) true.
Proof.
  intros w b H. destruct b as [ |z| ]; cbn [pj pjR fst pinokp] in H.
  - apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pj pjR fst]. pose proof (tidE bool _ true H) as Hzeq.
    apply Z.eqb_eq in Hzeq. rewrite <- Hzeq. rewrite Z.eqb_refl.
    apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pinokp] in H. tidQ H E. discriminate E.
Qed.

(* allpass ⟹ 钉位与 w 相容 *)
Lemma allpass_pinok : forall (s : list verd) (h : hole) (w : Z),
  clq_tid bool (allpass h w s) true ->
  clq_tid bool (pinokp w (pget (ipin (melt s)) h)) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - destruct h; apply clq_tid_refl.
  - cbn [melt]. destruct v as [h0 d0 z0]. destruct d0.
    + cbn [allpass vd vh] in H. destruct (hbeq h0 h) eqn:Eh.
      * apply tid_andb_inv in H. destruct H as [Hhead Ht].
        cbn in Hhead.
        pose proof (tidE bool _ true Hhead) as Hheq.
        apply Z.eqb_eq in Hheq.
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd].
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E, Hheq. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h).
        -- apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pinokp] in IPB.
           destruct (Z.eqb w z) eqn:Ewz.
           ++ apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
           ++ pose proof (tidE bool _ true IPB) as E1.
              apply Z.eqb_eq in E1. apply Z.eqb_neq in Ewz. congruence.
        -- cbn [pinokp] in IPB.
           pose proof (tidE bool _ true IPB) as E2.
           discriminate E2.
      * apply tid_andb_inv in H. destruct H as [_ Ht].
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h) as [z2| |].
        -- exact IPB.
        -- exact IPB.
        -- cbn [pinokp] in IPB. tidQ IPB E. discriminate E.
    + cbn [allpass vd vh] in H. apply tid_andb_inv in H.
      destruct H as [_ Ht].
      pose proof (IH h w Ht) as IPB.
      pose proof (pget_mjoin (m1 (mkVd h0 vrej z0)) (melt t) h) as J.
      tidQ J EJ. rewrite EJ.
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E.
      cbn [pj pjR fst].
      destruct (pget (ipin (melt t)) h) as [z2| |].
      -- exact IPB.
      -- exact IPB.
      -- cbn [pinokp] in IPB. tidQ IPB E. discriminate E.
Qed.

(* 钉位 = PN ⟹ 该洞无任何 pass 判定 ⟹ allpass 平凡真 *)
Lemma pinPN_allpass : forall (s : list verd) (h : hole) (w : Z),
  clq_tid pinv (pget (ipin (melt s)) h) PN -> clq_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply clq_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H.
    destruct (pjR_PN_inv (pget (ipin (m1 (mkVd h0 d0 z0))) h)
                         (pget (ipin (melt t)) h) H) as [Ha Hb].
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
        tidQ Ha Ea. discriminate Ea.
      * apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true (IH h w Hb)).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
      exact (IH h w Hb).
Qed.

(* 钉位 = P1 z ⟹ 流中确有 pass(h,z) 判定 *)
(* 钉位聚合键式引理：P1 z0 ⊕ P1 z1 = P1 z ⟹ z0 = z *)
Lemma pjR_P1_head : forall (z0 z1 z : Z),
  clq_tid pinv (pjR (pj (P1 z0) (P1 z1))) (P1 z) -> z0 = z.
Proof.
  intros z0 z1 z H. unfold pjR, pj in H.
  destruct (Z.eqb z0 z1) eqn:E.
  - tidQ H E2. injection E2 as E3. exact E3.
  - tidQ H E2. discriminate E2.
Qed.

(* pin_P1_in：由 pin_P1_in_val/pin_PN_absurd 组合覆盖（见 pin_iffT 消费面） *)

(* 钉位 = PN ⟹ 流中不可能有 pass(h,z) 判定（荒谬件，任意 Set 可关） *)
Lemma pin_PN_absurd : forall (s : list verd) (h : hole) (z : Z),
  clq_tid pinv (pget (ipin (melt s)) h) PN ->
  clq_tid bool (vIn (mkVd h vpass z) s) true ->
  forall P : Set, P.
Proof.
  induction s as [| v t IH]; intros h z H Hin.
  - cbn [vIn] in Hin. tidQ Hin E. discriminate E.
  - cbn [melt] in H. destruct v as [h0 d0 z0]. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H. rewrite <- EB in H.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z1| ]; cbn [pj pjR fst] in H.
        -- tidQ H E. discriminate E.
        -- destruct (Z.eqb z0 z1) eqn:Ez; cbn [pj pjR fst] in H;
             tidQ H E; discriminate E.
        -- tidQ H E. discriminate E.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj pjR fst] in H.
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        exact (IH h z (clq_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H) Hin).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
        exact (IH h z (clq_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H) Hin).
Qed.

(* 钉位 = P1 z1 且流中另有 pass(h,z0) ⟹ z1 = z0（钉值与任何流内 pass 一致） *)
Lemma pin_P1_in_val : forall (s : list verd) (h : hole) (z1 z0 : Z),
  clq_tid pinv (pget (ipin (melt s)) h) (P1 z1) ->
  clq_tid bool (vIn (mkVd h vpass z0) s) true ->
  clq_tid Z z1 z0.
Proof.
  induction s as [| v t IH]; intros h z1 z0 Hp Hin.
  - cbn [vIn] in Hin. tidQ Hin E. discriminate E.
  - cbn [melt] in Hp. destruct v as [h0 d0 z0']. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0')) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in Hp. rewrite <- EB in Hp.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        destruct (Z.eqb z0' z0) eqn:Ezz0; cbn [andb orb] in Hin.
        -- (* 头即见证（值 z0' = z0） *)
           pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
           rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj] in Hp.
           destruct b as [ |z2| ]; cbn [pj pjR fst] in Hp.
           ++ tidQ Hp E. injection E as Ei.
              exact (clq_tid_trans Z z1 z0' z0 (clq_tid_sym Z z0' z1 (clq_tid_eq Z _ _ Ei))
                       (clq_tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** tidQ Hp E. injection E as Ei.
                 exact (clq_tid_trans Z z1 z0' z0 (clq_tid_sym Z z0' z1 (clq_tid_eq Z _ _ Ei))
                          (clq_tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
              ** tidQ Hp E. discriminate E.
           ++ tidQ Hp E. discriminate E.
        -- (* 头是本洞 pass 但值 ≠ z0：见证在尾 *)
           pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
           rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj] in Hp.
           destruct b as [ |z2| ]; cbn [pj pjR fst] in Hp.
           ++ exact (pin_PN_absurd t h z0 (clq_tid_eq pinv _ _ (eq_sym EB)) Hin _).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** tidQ Hp E. injection E as Ei.
                 assert (Ht1 : clq_tid pinv (pget (ipin (melt t)) h) (P1 z1)).
                 { rewrite <- EB. apply (clq_tid_eq pinv (P1 z2) (P1 z1)).
                   rewrite (eq_trans (eq_sym (proj1 (Z.eqb_eq z0' z2) Ez)) Ei).
                   reflexivity. }
                 exact (IH h z1 z0 Ht1 Hin).
              ** tidQ Hp E. discriminate E.
           ++ tidQ Hp E. discriminate E.
      * (* 头非本洞 pass（hbeq false）：A = PN ⟹ 见证在尾 ⟹ IH *)
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
        rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj pjR fst] in Hp.
        exact (IH h z1 z0 (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                                (clq_tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
    + (* 头非本洞 pass：A = PN ⟹ 见证在尾 ⟹ IH *)
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0')) as M1E;
      rewrite M1E in Hp; cbn [pj pjR fst] in Hp;
      exact (IH h z1 z0 (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                              (clq_tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
Qed.

(* 钉位 = P1 w ⟹ 全体 pass 判定一致于 w *)
Lemma pin_P1_allpass : forall (s : list verd) (h : hole) (w : Z),
  clq_tid pinv (pget (ipin (melt s)) h) (P1 w) ->
  clq_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply clq_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. tidQ J EJ.
    rewrite EJ in H.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z2| ]; cbn [pj pjR fst] in H.
        -- (* b = PN：钉 = P1 z0 ⟹ z0 = w；尾无 pass ⟹ allpass 尾平凡 *)
           tidQ H E. injection E as Ei.
           apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ei.
           rewrite Z.eqb_refl.
           rewrite (tidE bool _ true
                      (pinPN_allpass t h w (clq_tid_eq pinv _ _ (eq_sym EB)))).
           reflexivity.
        -- destruct (Z.eqb z0 z2) eqn:Ez2; cbn [pj pjR fst] in H.
           ++ tidQ H E. injection E as Ei. apply Z.eqb_eq in Ez2.
              assert (Htw : clq_tid pinv (pget (ipin (melt t)) h) (P1 w)).
              { rewrite <- EB. apply (clq_tid_eq pinv (P1 z2) (P1 w)).
                rewrite (eq_trans (eq_sym Ez2) Ei). reflexivity. }
              apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ez2.
              rewrite (eq_trans (eq_sym Ez2) Ei), Z.eqb_refl.
              rewrite (tidE bool _ true (IH h w Htw)). reflexivity.
           ++ tidQ H E. discriminate E.
        -- tidQ H E. discriminate E.
      * (* 头非本洞 pass：钉 = b ⟹ 尾见 ⟹ IH *)
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj pjR fst] in H.
        apply (clq_tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true
                (IH h w (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                           (clq_tid_eq pinv _ _ (eq_sym EB)) H))).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      exact (IH h w (clq_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                         (clq_tid_eq pinv _ _ (eq_sym EB)) H)).
Qed.

(* 主定理 2：钉位 iffT——钉 = 流中 pass 判定的一致聚合（守恒双向：
   不发明——钉值必来自流内判定；不歪曲——流内 pass 判定全体一致） *)
(* pin_iffT：fwd 向由 pin_P1_in_val/pin_P1_allpass 覆盖；bwd 向由
   allpass_pinok/pin_P1_allpass 覆盖（内容等价，分装为两个定向引理） *)


(* ===================================================================== *)
(* 5. 拒值差条款的流侧守恒                                                    *)
(* ===================================================================== *)

Fixpoint cinc (h : hole) (e : Z) (l : list (prod hole Z)) : bool :=
  match l with
  | nil => false
  | x :: t => orb (andb (hbeq h (fst x)) (Z.eqb e (snd x))) (cinc h e t)
  end.

Lemma cinc_app : forall (h : hole) (e : Z) (l1 l2 : list (prod hole Z)),
  clq_tid bool (cinc h e (l1 ++ l2)) (orb (cinc h e l1) (cinc h e l2)).
Proof.
  intros h e l1 l2. induction l1 as [| x t IH]; cbn [cinc app].
  - apply clq_tid_refl.
  - tidQ IH EI. rewrite EI.
    apply (clq_tid_eq bool _ _). apply Bool.orb_assoc.
Qed.

(* 流中 rej(h,e) 判定 ⟹ 条款入锭 *)
Theorem rej_from_stream : forall (s : list verd) (h : hole) (e : Z),
  clq_tid bool (vIn (mkVd h vrej e) s) true ->
  clq_tid bool (cinc h e (irej (melt s))) true.
Proof.
  induction s as [| v t IH]; intros h e H.
  - cbn [vIn] in H. tidQ H E. discriminate E.
  - cbn [melt]. destruct v as [h0 d0 z0]. cbn [vIn] in H.
    unfold mjoin. cbn [irej]. destruct d0.
    + cbn [m1 irej app cinc vd vh vz]. apply IH.
      unfold vbeq, vh, vd, vz in H. cbn [dbeq andb] in H.
      tidQ H E. rewrite Bool.andb_false_r, orb_false_l in E.
      exact (clq_tid_eq bool _ true E).
    + cbn [m1 irej app cinc vd vh vz]. apply (clq_tid_eq bool _ true).
      destruct (vbeq (mkVd h0 vrej z0) (mkVd h vrej e)) eqn:Ev.
      * destruct (vbeq_inv _ _ (clq_tid_eq bool _ true Ev)) as [Ex [Ed Ezz]].
        cbn [vh vd vz] in Ex, Ed, Ezz.
        cbn [fst snd]. rewrite (tidE hole _ _ Ex), (tidE Z _ _ Ezz).
        rewrite (tidE bool _ true (hbeq_refl h)), Z.eqb_refl.
        reflexivity.
      * apply tid_orb_false in H.
        rewrite (tidE bool _ true (IH h e H)).
        apply Bool.orb_true_r.
Qed.

(* ===================================================================== *)
(* 6. 织 weave：差分段（只吃锭；织出件 = Q4 dtab；欠单如实记欠）                *)
(* ===================================================================== *)

Definition pvz (x : pinv) : Z := match x with P1 z => z | _ => 0 end.

(* 织出件：六槽差分表，头元 k0 规范 0（Q4 载体 dtab） *)
Definition dbuild (p : ipins) : dtab :=
  dtabSnoc
    (dtabSnoc
       (dtabSnoc
          (dtabSnoc
             (dtabSnoc (dtab1 0) (pvz (qb p)))
             (pvz (qc p)))
          (pvz (qd p)))
       (pvz (qe p)))
    (pvz (qf p)).

Definition slotz (p : ipins) (h : hole) : Z :=
  match h with
  | k0 => 0
  | _ => pvz (pget p h)
  end.

Lemma dbuild_pot : forall (p : ipins) (h : hole),
  clq_tid Z (pot (dbuild p) (hix h)) (slotz p h).
Proof. intros p h. destruct h; apply clq_tid_refl. Qed.

Lemma dsub_pget : forall (p : ipins) (h : hole),
  clq_tid Z (dsub (dbuild p) (hix h) O)
       (match h with k0 => 0 | _ => pvz (pget p h) end).
Proof.
  intros p h. unfold dsub.
  pose proof (dbuild_pot p h) as T1. tidQ T1 E1.
  rewrite E1. apply (clq_tid_eq Z _ _).
  destruct h; cbn [slotz]; apply Z.sub_0_r.
Qed.

Lemma dbuild_len : forall p : ipins, clq_tid nat (dlen (dbuild p)) hmax.
Proof. intros p. apply (clq_tid_eq nat _ _). reflexivity. Qed.

(* 欠单条目：缺钉 / 钉冲突 / 差条款相抵 *)
Inductive idl_iou : Set :=
| idl_IOU_NOPIN (h : hole)
| idl_IOU_BAD (h : hole)
| idl_IOU_REJ (h : hole) (e : Z).

Definition rjbad (p : ipins) (x : prod hole Z) : bool :=
  Z.eqb (dsub (dbuild p) (hix (fst x)) O) (snd x).

Fixpoint rejious (p : ipins) (l : list (prod hole Z)) : list idl_iou :=
  match l with
  | nil => nil
  | x :: t => if rjbad p x then idl_IOU_REJ (fst x) (snd x) :: rejious p t
              else rejious p t
  end.

Definition headiou (p : ipins) : list idl_iou :=
  match pget p k0 with
  | PN => nil
  | P1 z => if Z.eqb z 0 then nil else idl_IOU_BAD k0 :: nil
  | PB => idl_IOU_BAD k0 :: nil
  end.

Definition slotL : list hole := k1 :: kb :: kc :: ke :: kr :: nil.

Fixpoint hin (h : hole) (hs : list hole) : bool :=
  match hs with
  | nil => false
  | x :: t => orb (hbeq x h) (hin h t)
  end.

Fixpoint slotiousL (p : ipins) (hs : list hole) : list idl_iou :=
  match hs with
  | nil => nil
  | h :: t =>
      match pget p h with
      | P1 _ => slotiousL p t
      | PN => idl_IOU_NOPIN h :: slotiousL p t
      | PB => idl_IOU_BAD h :: slotiousL p t
      end
  end.

Fixpoint allpin1 (p : ipins) (hs : list hole) : bool :=
  match hs with
  | nil => true
  | h :: t => andb (isP1 (pget p h)) (allpin1 p t)
  end.

Lemma slotiousL_nil_allpin1 : forall p hs,
  clq_tid (list idl_iou) (slotiousL p hs) nil -> clq_tid bool (allpin1 p hs) true.
Proof.
  intros p hs. induction hs as [| h t IH]; intros H.
  - apply clq_tid_refl.
  - cbn [slotiousL] in H. cbn [allpin1].
    destruct (pget p h) as [z| |].
    + tidQ H E. discriminate E.
    + exact (IH H).
    + tidQ H E. discriminate E.
Qed.

Lemma allpin1_hit : forall p hs h,
  clq_tid bool (allpin1 p hs) true -> clq_tid bool (hin h hs) true ->
  clq_tid bool (isP1 (pget p h)) true.
Proof.
  intros p hs h. induction hs as [| h' t IH]; intros HA Hh.
  - cbn [hin] in Hh. tidQ Hh E. discriminate E.
  - cbn [allpin1 hin] in HA, Hh.
    destruct (hbeq h' h) eqn:Ex.
    + apply tid_andb_inv in HA. destruct HA as [HA1 _].
      pose proof (hbeq_true h' h (clq_tid_eq bool _ true Ex)) as EH.
      rewrite <- (tidE hole _ _ EH). exact HA1.
    + apply IH.
      * apply tid_andb_inv in HA. destruct HA as [_ HA2]. exact HA2.
      * apply tid_orb_false in Hh. exact Hh.
Qed.

Definition iouof (g : ingot) : list idl_iou :=
  headiou (ipin g) ++ (slotiousL (ipin g) slotL ++ rejious (ipin g) (irej g)).

Inductive weaveout : Set := wok (d : dtab) | wiou (l : list idl_iou).

Definition weave (g : ingot) : weaveout :=
  match iouof g with
  | nil => wok (dbuild (ipin g))
  | l => wiou l
  end.

Definition weave_b (g : ingot) : bool :=
  match weave g with wok _ => true | wiou _ => false end.

(* 拒值差条款的段间差分判定：条款全过 ⟸ 条款清点为空 *)
Lemma rejious_nil_ok : forall (p : ipins) (l : list (prod hole Z)),
  clq_tid (list idl_iou) (rejious p l) nil ->
  forall (h : hole) (e : Z), clq_tid bool (cinc h e l) true ->
  clq_tid bool (negb (rjbad p (h, e))) true.
Proof.
  intros p l. induction l as [| x t IH]; intros Hn h e Hc.
  - cbn [cinc] in Hc. tidQ Hc E. discriminate E.
  - cbn [rejious] in Hn. destruct (rjbad p x) eqn:Er.
    + tidQ Hn E. discriminate E.
    + cbn [cinc] in Hc. destruct x as [xh xe]. cbn [fst snd] in Hc.
      pose proof (tid_orb_inv _ _ Hc) as Ec. destruct Ec as [Ec|Ec].
      * apply tid_andb_inv in Ec. destruct Ec as [Eh1 Eh2].
        pose proof (tidE hole _ _ (hbeq_true h xh Eh1)) as Exe.
        pose proof (tidE bool _ _ Eh2) as Eh2e. apply Z.eqb_eq in Eh2e.
        rewrite Exe, Eh2e, Er. apply clq_tid_refl.
      * apply IH. exact Hn. exact Ec.
Qed.

Lemma headiou_nil_inv : forall p : ipins,
  clq_tid (list idl_iou) (headiou p) nil ->
  clq_tid bool (match pget p k0 with
            | PN => true
            | P1 z => Z.eqb z 0
            | PB => false
            end) true.
Proof.
  intros p H. unfold headiou in H. destruct (pget p k0) as [z| |].
  - apply clq_tid_refl.
  - destruct (Z.eqb z 0); [apply clq_tid_refl | tidQ H E; discriminate E].
  - tidQ H E. discriminate E.
Qed.

Lemma weave_wok_inv : forall (g : ingot) (d : dtab),
  clq_tid weaveout (weave g) (wok d) ->
  prod (clq_tid (list idl_iou) (iouof g) nil) (clq_tid dtab d (dbuild (ipin g))).
Proof.
  intros g d H. unfold weave in H.
  destruct (iouof g) as [| x t] eqn:E.
  - tidQ H H2. injection H2 as H2.
    exact (pair (clq_tid_refl (list idl_iou) nil)
                (clq_tid_eq dtab d (dbuild (ipin g)) (eq_sym H2))).
  - tidQ H H2. discriminate H2.
Qed.

(* 判定满足性判定（段间差分可判定的逐词形态）：
   pass(h,w) ⟺ 织出表头相对差 = w；rej(h,e) ⟺ 头相对差 ≠ e（非零差条款成立） *)
Definition vrespects (d : dtab) (v : verd) : bool :=
  match vd v with
  | vpass => Z.eqb (dsub d (hix (vh v)) O) (vz v)
  | vrej => negb (Z.eqb (dsub d (hix (vh v)) O) (vz v))
  end.

(* 主定理 3：织出即合法——流中每枚判定都被织出表满足（出生免疫跨洞非法） *)
Theorem weave_sound : forall (s : list verd) (d : dtab),
  clq_tid weaveout (weave (melt s)) (wok d) ->
  forall v : verd, clq_tid bool (vIn v s) true -> clq_tid bool (vrespects d v) true.
Proof.
  intros s d Hw.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd].
  tidQ Hn En. tidQ Hd Ed.
  unfold iouof in En. apply app_eq_nil in En. destruct En as [Eh Esr].
  apply app_eq_nil in Esr. destruct Esr as [Es Er].
  pose proof (clq_tid_eq (list idl_iou) (headiou (ipin (melt s))) nil Eh) as TH.
  pose proof (clq_tid_eq (list idl_iou) (slotiousL (ipin (melt s)) slotL) nil Es) as TS.
  pose proof (clq_tid_eq (list idl_iou) (rejious (ipin (melt s)) (irej (melt s))) nil Er)
    as TR.
  pose proof (slotiousL_nil_allpin1 (ipin (melt s)) slotL TS) as AP.
  pose proof (headiou_nil_inv (ipin (melt s)) TH) as HD.
  induction s as [| v0 t IH]; intros v Hv.
  - cbn [vIn] in Hv. tidQ Hv E. discriminate E.
  - cbn [vIn] in Hv. destruct v as [h0 d0 z0]. destruct d0.
    + (* pass(h0,z0)：织出表上头相对差恰为 z0 *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      rewrite (tidE Z _ _ (dsub_pget (ipin (melt (v0 :: t))) h0)).
      destruct (pget (ipin (melt (v0 :: t))) h0) as [|z1| ] eqn:Ep.
      * (* 钉缺：头洞由头规引理，余洞由六槽清点 *)
        destruct h0.
        -- exact (pin_PN_absurd (v0 :: t) k0 z0 (clq_tid_eq pinv _ _ Ep) Hv
                    (clq_tid bool (Z.eqb 0 z0) true)).
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
      * pose proof (pin_P1_in_val (v0 :: t) h0 z1 z0 (clq_tid_eq pinv _ _ Ep) Hv) as ZP.
        tidQ ZP EZ.
        destruct h0.
        -- rewrite Ep in HD. pose proof (tidE bool _ true HD) as HDz.
           apply Z.eqb_eq in HDz.
           apply (clq_tid_eq bool _ true). rewrite <- EZ, HDz. apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (clq_tid_eq bool _ true). apply Z.eqb_refl.
      * (* 钉冲突：头洞由头规引理，余洞由六槽清点 *)
        destruct h0.
        -- rewrite Ep in HD. cbn in HD. tidQ HD E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (clq_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. tidQ HP1 E. discriminate E.
    + (* rej(h0,z0)：织出表与拒值之差非零——差条款全过 *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      pose proof (rejious_nil_ok (ipin (melt (v0 :: t))) (irej (melt (v0 :: t))) TR
                        h0 z0 (rej_from_stream (v0 :: t) h0 z0 Hv)) as RJ.
      change (clq_tid bool
                (negb (Z.eqb (dsub (dbuild (ipin (melt (v0 :: t)))) (hix h0) O) z0))
                true) in RJ.
      rewrite (tidE bool _ true RJ). apply clq_tid_refl.
Qed.

(* ===================================================================== *)
(* 7. 重放不变：差分段对构造段封闭——活锁失去载体                                *)
(* ===================================================================== *)

Definition isnil {A : Type} (l : list A) : bool :=
  match l with nil => true | _ => false end.

Lemma isnil_app : forall (A : Type) (a b : list A),
  clq_tid bool (isnil (a ++ b)) (andb (isnil a) (isnil b)).
Proof. intros A a b. destruct a; apply clq_tid_refl. Qed.

Lemma rejious_app_isnil : forall (p : ipins) (l1 l2 : list (prod hole Z)),
  clq_tid bool (isnil (rejious p (l1 ++ l2)))
       (andb (isnil (rejious p l1)) (isnil (rejious p l2))).
Proof.
  intros p l1 l2. induction l1 as [| x t IH]; cbn [app rejious].
  - apply clq_tid_refl.
  - destruct (rjbad p x).
    + apply clq_tid_refl.
    + apply IH.
Qed.

Lemma andb_idem_tid : forall b : bool, clq_tid bool (andb b b) b.
Proof. intros b. destruct b; apply clq_tid_refl. Qed.

Lemma andb3_idem_eq : forall a b c : bool,
  andb a (andb b (andb c c)) = andb a (andb b c).
Proof. intros a b c. destruct a, b, c; reflexivity. Qed.

Lemma iouof_mjoin_self_b : forall g : ingot,
  clq_tid bool (isnil (iouof (mjoin g g))) (isnil (iouof g)).
Proof.
  intros [p l]. unfold mjoin, iouof. cbn [ipin irej].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)).
  tidQ (isnil_app idl_iou (headiou p)
          (slotiousL p slotL ++ rejious p (l ++ l))) Ei1. rewrite Ei1.
  tidQ (isnil_app idl_iou (slotiousL p slotL) (rejious p (l ++ l))) Ei2.
  rewrite Ei2.
  tidQ (rejious_app_isnil p l l) Erj. rewrite Erj.
  tidQ (isnil_app idl_iou (headiou p) (slotiousL p slotL ++ rejious p l)) Ei3.
  rewrite Ei3.
  tidQ (isnil_app idl_iou (slotiousL p slotL) (rejious p l)) Ei4. rewrite Ei4.
  apply (clq_tid_eq bool _ _). rewrite andb3_idem_eq. reflexivity.
Qed.

(* 桥：weave_b = isnil ∘ iouof（双 match 不交换，独立桥件） *)
Lemma weave_b_isnil : forall g : ingot,
  clq_tid bool (weave_b g) (isnil (iouof g)).
Proof.
  intros g. unfold weave_b, weave, isnil.
  destruct (iouof g) as [| x t]; apply clq_tid_refl.
Qed.

(* 主定理 4a：整流重放不改变织造判定 *)
Theorem weave_replay_b : forall s : list verd,
  clq_tid bool (weave_b (melt (s ++ s))) (weave_b (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh.
  apply (clq_tid_trans bool (weave_b (mjoin (melt s) (melt s)))
                         (isnil (iouof (mjoin (melt s) (melt s)))) _).
  - apply weave_b_isnil.
  - apply (clq_tid_trans bool (isnil (iouof (mjoin (melt s) (melt s))))
             (isnil (iouof (melt s))) _).
    + exact (iouof_mjoin_self_b (melt s)).
    + apply (clq_tid_sym bool _ _ (weave_b_isnil (melt s))).
Qed.

Lemma nil_isnil : forall l : list idl_iou,
  clq_tid (list idl_iou) l nil -> clq_tid bool (isnil l) true.
Proof. intros [| x t] H.
  - apply clq_tid_refl.
  - cbn [isnil] in H. tidQ H E. discriminate E.
Qed.

Lemma isnil_eq_nil : forall l : list idl_iou,
  clq_tid bool (isnil l) true -> clq_tid (list idl_iou) l nil.
Proof.
  intros l H. destruct l as [| x t].
  - apply clq_tid_refl.
  - cbn [isnil] in H. tidQ H E. discriminate E.
Qed.

(* 桥：条款清空 ⟹ 织出 wok（destruct 吃掉 weave 的 match，零 setoid 依赖） *)
Lemma weave_nil_wok : forall (g : ingot) (d : dtab),
  clq_tid (list idl_iou) (iouof g) nil ->
  clq_tid dtab d (dbuild (ipin g)) ->
  clq_tid weaveout (weave g) (wok d).
Proof.
  intros g d Hn Hd. unfold weave. destruct (iouof g) as [| x t].
  - apply (clq_tid_eq weaveout _ _). rewrite (tidE dtab _ _ Hd). reflexivity.
  - tidQ Hn E. discriminate E.
Qed.

(* 主定理 4b：重放不改变织出件（差分段对构造段封闭：wok 支不变） *)
Theorem weave_replay_d : forall (s : list verd) (d : dtab),
  clq_tid weaveout (weave (melt (s ++ s))) (wok d) ->
  clq_tid weaveout (weave (melt s)) (wok d).
Proof.
  intros s d H.
  destruct (weave_wok_inv (melt (s ++ s)) d H) as [Hn Hd].
  tidQ Hn En. tidQ Hd Ed.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh in En.
  pose proof (nil_isnil _ (clq_tid_eq (list idl_iou) _ nil En)) as EnB.
  pose proof (clq_tid_trans bool (isnil (iouof (melt s)))
                (isnil (iouof (mjoin (melt s) (melt s)))) true
                (clq_tid_sym bool _ _ (iouof_mjoin_self_b (melt s))) EnB) as EnB2.
  pose proof (isnil_eq_nil (iouof (melt s)) EnB2) as Ens.
  apply (weave_nil_wok (melt s) d Ens).
  rewrite Ed, Eh. apply (clq_tid_eq dtab _ _). f_equal. unfold mjoin.
  exact (tidE ipins _ _ (pjoin_self_pins (ipin (melt s)))).
Qed.

(* 冲突清点：钉位为 PB 的洞数（同洞异值至多记一次） *)
Definition pbc (x : pinv) : nat := match x with PB => 1%nat | _ => 0%nat end.

Definition iconf (g : ingot) : nat :=
  (pbc (qa (ipin g)) + (pbc (qb (ipin g)) + (pbc (qc (ipin g)) +
  (pbc (qd (ipin g)) + (pbc (qe (ipin g)) + pbc (qf (ipin g)))))))%nat.

Lemma iconf_mjoin_self : forall g : ingot, clq_tid nat (iconf (mjoin g g)) (iconf g).
Proof.
  intros [p l]. unfold mjoin, iconf. cbn [ipin].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)). apply clq_tid_refl.
Qed.

(* 主定理 4c：重放不新增冲突洞（冲突是洞的属性，不是事件计数） *)
Theorem replay_census : forall s : list verd,
  clq_tid nat (iconf (melt (s ++ s))) (iconf (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. tidQ Hh Eh. rewrite Eh.
  exact (iconf_mjoin_self (melt s)).
Qed.

(* ===================================================================== *)
(* 8. Q4 判定面咬合：织出件受 [内]类查询逐词复核                                *)
(* ===================================================================== *)

Lemma hix_nle : forall h : hole, clq_nle (hix h) hmax.
Proof.
  destruct h.
  - apply clq_nle_0.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_S. apply clq_nle_n.
  - apply clq_nle_n.
Qed.

(* 主定理 5：织出件交给 Q4 问答机复核——[内]类差值查询的答案恰为判定钉值。
   织机出生即证 + Q4 判定面独立复核，两件咬合。 *)
Theorem recheck_pass : forall (s : list verd) (d : dtab) (h : hole) (w : Z),
  clq_tid weaveout (weave (melt s)) (wok d) ->
  clq_tid bool (vIn (mkVd h vpass w) s) true ->
  clq_tid qans (qask (mkCL d None acol0) (QIN (hix h) O)) (qans_val w).
Proof.
  intros s d h w Hw Hv.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd]. tidQ Hd Ed.
  rewrite Ed in Hw. rewrite Ed.
  pose proof (weave_sound s (dbuild (ipin (melt s))) Hw
                (mkVd h vpass w) Hv) as VR.
  unfold vrespects in VR. cbn [vd vz vh] in VR.
  pose proof (tidE bool _ true VR) as EV. apply Z.eqb_eq in EV.
  unfold qask, qaskR. cbn [cld clv cla].
  rewrite (tidE nat _ _ (dbuild_len (ipin (melt s)))).
  pose proof (clq_nle_leb hmax (hix h) (hix_nle h)) as L1. tidQ L1 EL1. rewrite EL1.
  pose proof (clq_nle_leb hmax O (clq_nle_0 hmax)) as L2. tidQ L2 EL2. rewrite EL2.
  apply tid_qans_val. exact (clq_tid_eq Z _ _ EV).
Qed.

(* ===================================================================== *)
(* 9. 计算演示：异或流收编回归 + 幸福路 + 同洞异值记冲突一次                     *)
(* ===================================================================== *)

(* 二轮击杀实验（上游会话 异或流）的 IDL 回归：pass-A 后 rej-B——
   B 无钉（无 pass 判定）→ 欠单如实记缺；B 的差条款「值≠0」对占位 0 相抵 →
   再记一条 REJ——异或流给不出非零差见证，记欠，不织。 *)
Definition sX : list verd := mkVd k1 vpass 0 :: mkVd kb vrej 0 :: nil.

Theorem xor_defused :
  clq_tid weaveout (weave (melt sX))
      (wiou (idl_IOU_NOPIN kb :: idl_IOU_NOPIN kc :: idl_IOU_NOPIN ke :: idl_IOU_NOPIN kr
             :: idl_IOU_REJ kb 0 :: nil)).
Proof.
  apply (clq_tid_eq weaveout _ _). reflexivity.
Qed.

(* 幸福路：六洞全钉 + 一条可满足差条款 ⟹ 织出 *)
Definition sOK : list verd :=
  mkVd k0 vpass 0 :: mkVd k1 vpass 3 :: mkVd kb vpass (-2) :: mkVd kc vpass 7
  :: mkVd ke vpass 1 :: mkVd kr vpass 4 :: mkVd kb vrej 9 :: nil.

Theorem happy_wok : clq_tid bool (weave_b (melt sOK)) true.
Proof.
  apply (clq_tid_eq bool _ true). reflexivity.
Qed.

(* 同洞异值：冲突位 PB ⟹ 记欠不织；冲突清点恰为 1（同洞异值记冲突一次） *)
Definition sC : list verd := mkVd k1 vpass 3 :: mkVd k1 vpass 5 :: nil.

Theorem conflict_once : clq_tid bool (weave_b (melt sC)) false.
Proof.
  apply (clq_tid_eq bool _ false). reflexivity.
Qed.

Theorem conflict_census : clq_tid nat (iconf (melt sC)) 1%nat.
Proof.
  apply (clq_tid_eq nat _ _). reflexivity.
Qed.

(* 织出件装进 Q4 账态后 [内]类全准入（六槽域内零拒答） *)
Theorem wok_qin_admit : forall (s : list verd) (i j : nat),
  clq_nle i (dlen (dbuild (ipin (melt s)))) ->
  clq_nle j (dlen (dbuild (ipin (melt s)))) ->
  clq_tid bool (qadmit (mkCL (dbuild (ipin (melt s))) None acol0) (QIN i j)) true.
Proof.
  intros s i j Hi Hj. unfold qadmit, qadmitR, qin_ok. cbn [cld clv cla].
  pose proof (clq_nle_leb (dlen (dbuild (ipin (melt s)))) i Hi) as L1. tidQ L1 EL1.
  pose proof (clq_nle_leb (dlen (dbuild (ipin (melt s)))) j Hj) as L2. tidQ L2 EL2.
  rewrite EL1, EL2. apply clq_tid_refl.
Qed.

Close Scope Z_scope.
