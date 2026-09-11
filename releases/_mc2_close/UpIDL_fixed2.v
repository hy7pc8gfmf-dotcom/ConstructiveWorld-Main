(* ===================================================================== *)
(* UpIDL.v — 判词织机 IDL 熔锭差分两段制 Coq 落地                           *)
(*                                                                       *)
(* 设计出处：ROUNDTABLE2 席 4 轮次 3 终稿「熔锭差分织机（Ingot-Differential    *)
(*   Loom, IDL）——两段制，判词流永不逐条重放」（含席 3 异或击杀与席 2 活锁     *)
(*   击杀的双重收编）；排队席位方案-二轮成果Coq化-20260907.md Q5 条目          *)
(*   （依赖 Q4 语义——UpCLQuery.v 已交付，本件 Require Import 直接消费）。     *)
(*                                                                       *)
(* 两段制：                                                                *)
(*   构造段（熔炼 melt）：判词流单遍右折叠为锭 ingot——六洞钉位（同值累计       *)
(*         立钉 P1、异值即冲突 PB 恒传、缺判词即 PN）+ 拒值差条款列。          *)
(*   差分段（织 weave）：只吃锭、永不重放流——钉位差分编译为 Q4 载体 idl_dtab       *)
(*         （头元 k0 规范 0，idl_dlen=5），拒值差条款在织出表上逐条 Z 判定        *)
(*         （段间差分可判定）；见证缺席 / 钉冲突 / 差条款相抵 → 欠单 wiou      *)
(*         如实记欠，不吐件。                                                *)
(* 主定理：melt_hom（熔炼=列表同态，两段构造的代数内容）/ pin_iffT（钉位=流    *)
(*   中 pass 判词的一致聚合，idl_iffT 双向守恒）/ weave_sound（织出即合法：流中   *)
(*   每枚判词都被织出表满足——出生免疫跨洞非法）/ weave_replay_b/_d +          *)
(*   replay_census（整流重放：织造判定、织出件、冲突清点全部不变——活锁       *)
(*   失去载体）/ recheck_pass（织出件交 Q4 判定面 [内]类查询逐词复核）/        *)
(*   xor_defused（异或流如实记欠不织——二轮击杀实验的收编回归）。              *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层（延续 Q4 Set 层路线：idl_tid/idl_nle/idl_iffT/sigT）；      *)
(* 语句零 Prop：等式 idl_tid、序 idl_nle、⟺ idl_iffT、分支 bool/prod/sigT。              *)
(* 纪律：纯构造性、零公理式出口、stdlib + UpCLQuery、全链可提取。              *)
(* 定稿决策（未定稿细节按「两段制结构最清晰 + 与 Q4 判定面咬合最紧」自定）：     *)
(*   ① 六洞型 hole=k0 k1 kb kc ke kr 具象为六槽，槽位=Q4 idl_dtab 指标 0..5，      *)
(*      头元 k0 恒 0（gauge 规范），全部判词语义走头相对差 idl_dsub d (hix h) 0。  *)
(*   ② 判词 verd=洞型×向×Z 证据：pass(h,w) 立钉「值=w」；rej(h,e) 出差条款     *)
(*      「值≠e」（非零差分要求，即设计的见证型差条款）。                       *)
(*   ③ 钉位三态 pinv=PN 缺 / P1 z 立钉 / PB 冲突——冲突位 PB 恒传播，故          *)
(*      同洞异值在整流中至多记一次（=设计「同洞异值记冲突一次」）；摩擦计       *)
(*      定稿为冲突清点 iconf=钉位为 PB 的洞数（终稿「冲突清点+欠单排序键」）。 *)
(*   ④ 织出件=Q4 idl_dtab（idl_dlen=5），可直接装进 Q4 账态 mkCL 受 [内]类查询复核。   *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
(* ── 内联自足改造（合并轨收口席续 20260910）：以下为 ConstructiveWorld_vo/UpCLQuery.v
   实体全量内联（自第一个 Require 起），替代原 Require Import UpCLQuery——
   使本件在 .vo 语境与合并轨 flat 语境均自洽；裸 idl_tid/idl_nle 系在 34 模块+基座内唯一。
   来源：vo 正身 UpCLQuery.v（与 attn 改名版 clq_tid 系同构）。
   语义移植说明：本件证明体未动（.vo 语境绿史保持）；attn 侧 UpIDL 前席重构草稿
   经诊断 G2 红（L669 类型不匹配，未完成件），其语义不予移植。 *)
From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建（自 UpPLA.v 内联：idl_tid 恒等型 + idl_nle 序型 + 判定工具）          *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive idl_tid (A : Type) : A -> A -> Type := idl_tid_refl : forall x : A, idl_tid A x x.

Definition idl_tid_sym (A : Type) (x y : A) (H : idl_tid A x y) : idl_tid A y x :=
  match H in idl_tid _ a b return idl_tid _ b a with
  | idl_tid_refl _ a0 => @idl_tid_refl _ a0
  end.

Definition idl_tid_trans (A : Type) (x y z : A) (H1 : idl_tid A x y) (H2 : idl_tid A y z) :
  idl_tid A x z :=
  match H1 in idl_tid _ a b return idl_tid _ b z -> idl_tid _ a z with
  | idl_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition idl_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : idl_tid A x y) :
  idl_tid B (f x) (f y) :=
  match H in idl_tid _ a b return idl_tid B (f a) (f b) with
  | idl_tid_refl _ a0 => @idl_tid_refl _ (f a0)
  end.

(* 从 idl_tid 提取定义等式（仅证明内部推理用，命名受控） *)
Ltac idl_tidQ H E :=
  pose proof (match H in idl_tid _ a b return a = b with idl_tid_refl _ _ => eq_refl end) as E.

(* x = y -> idl_tid A x y（定义等式反灌回恒等型） *)
Lemma tid_eq : forall (A : Type) (x y : A), x = y -> idl_tid A x y.
Proof.
  intros A x y H. rewrite H. apply idl_tid_refl.
Defined.

(* Set 层自然数序型（k ≤ m 编码为 idl_nle k m） *)
Inductive idl_nle (n : nat) : nat -> Set :=
| idl_nle_n : idl_nle n n
| idl_nle_S : forall m : nat, idl_nle n m -> idl_nle n (S m).

Lemma idl_leb_refl_tid : forall a : nat, idl_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply idl_tid_refl.
Qed.

Lemma idl_leb_S : forall a m : nat,
  idl_tid bool (Nat.leb a m) true -> idl_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply idl_tid_refl.
    + change (idl_tid bool false true) in H. idl_tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply idl_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint idl_nle_lebF (a b : nat) (H : idl_nle a b) {struct H} :
  idl_tid bool (Nat.leb a b) true :=
  match H as H0 in idl_nle _ bb
  return idl_tid bool (Nat.leb a bb) true with
  | idl_nle_n _ => idl_leb_refl_tid a
  | idl_nle_S _ m H1 => idl_leb_S a m (idl_nle_lebF a m H1)
  end.

Definition idl_nle_leb (b a : nat) (H : idl_nle a b) : idl_tid bool (Nat.leb a b) true :=
  idl_nle_lebF a b H.

(* idl_nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac idl_nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (idl_nle_leb _ _ H) in idl_tid _ x y return x = y with
        | idl_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma idl_nle_0 : forall m : nat, idl_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply idl_nle_n.
  - apply idl_nle_S. exact IH.
Qed.

Lemma idl_nle_SS : forall a b : nat, idl_nle a b -> idl_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply idl_nle_n.
  - apply idl_nle_S. exact IH.
Qed.

(* idl_nle -> leb = true 反向桥 *)
Lemma idl_nle_of_leb : forall b a : nat,
  idl_tid bool (Nat.leb a b) true -> idl_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply idl_nle_n.
    + change (idl_tid bool false true) in H. idl_tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply idl_nle_S. apply idl_nle_0.
    + exact (idl_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ -> idl_tid bool (leb) true 桥 *)
Lemma idl_lebT : forall a b : nat, (a <= b)%nat -> idl_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply idl_tid_refl.
Qed.

(* idl_nle (S m) O 荒谬件（索引不交配的空消去，合法关闭任意 Type 目标） *)
Lemma idl_nle_S_absurd : forall (m : nat) (P : Type), idl_nle (S m) O -> P.
Proof.
  intros m P H. inversion H.
Qed.

(* Set 层 ⟺ 载体：双函数记录（语句零 Prop 的当且仅当） *)
Record idl_iffT (A B : Type) : Type := mkIffT
  { iffT_fw : A -> B
  ; iffT_bw : B -> A }.

(* ===================================================================== *)
(* 1. 差表 idl_dtab：归纳构造的恒差账（语法免疫载体）                              *)
(*    封闭律 差 i j + 差 j k == 差 i k 对一切 idl_dtab 无前提成立——               *)
(*    不存在能写出破律差表的构造子。                                          *)
(* ===================================================================== *)

Inductive idl_dtab : Set :=
| idl_dtab1 (c : Z)                    (* 单指标账：指标 0（头元），gauge 值 c    *)
| idl_dtabSnoc (d : idl_dtab) (w : Z).     (* 入元：新指标 S (idl_dlen d)，其与头元差 w   *)

(* 账内指标数：合法指标域 0 .. idl_dlen d *)
Fixpoint idl_dlen (d : idl_dtab) : nat :=
  match d with
  | idl_dtab1 _ => O
  | idl_dtabSnoc d0 _ => S (idl_dlen d0)
  end.

(* 头元规范 h=0 下的势读数：idl_pot i = 差 i 0（由构造累积，绝非物质化总量） *)
Fixpoint idl_pot (d : idl_dtab) (i : nat) : Z :=
  match d with
  | idl_dtab1 c => if Nat.eqb i O then c else 0
  | idl_dtabSnoc d0 w => if Nat.eqb i (S (idl_dlen d0)) then w else idl_pot d0 i
  end.

(* 差 i j（唯一导出的 [内]类观测量） *)
Definition idl_dsub (d : idl_dtab) (i j : nat) : Z := idl_pot d i - idl_pot d j.

(* 件 3 核心定理：环形封闭律对一切 idl_dtab 构造性成立（无任何前提） *)
Theorem idl_dsub_cocycle : forall (d : idl_dtab) (i j k : nat),
  idl_tid Z (idl_dsub d i j + idl_dsub d j k) (idl_dsub d i k).
Proof.
  intros d i j k. unfold idl_dsub.
  apply (tid_eq Z (idl_pot d i - idl_pot d j + (idl_pot d j - idl_pot d k)) (idl_pot d i - idl_pot d k)).
  ring.
Qed.

(* gauge 平移：整表势读数加 c（换头元规范的语法操作） *)
Fixpoint idl_dshift (d : idl_dtab) (c : Z) : idl_dtab :=
  match d with
  | idl_dtab1 c0 => idl_dtab1 (c0 + c)
  | idl_dtabSnoc d0 w => idl_dtabSnoc (idl_dshift d0 c) (w + c)
  end.

Lemma idl_dlen_shift : forall (d : idl_dtab) (c : Z), idl_tid nat (idl_dlen (idl_dshift d c)) (idl_dlen d).
Proof.
  intros d c. induction d as [c0 | d0 IH w].
  - simpl. apply idl_tid_refl.
  - simpl. idl_tidQ IH Edl. rewrite Edl. apply idl_tid_refl.
Qed.

(* 件 3 对照定理：绝对势读数在 gauge 平移下恰移动 c（语言无平移不变的绝对读出） *)
Theorem idl_pot_shift_moves : forall (d : idl_dtab) (c : Z) (i : nat),
  idl_nle i (idl_dlen d) -> idl_tid Z (idl_pot (idl_dshift d c) i) (idl_pot d i + c).
Proof.
  intros d c i. induction d as [c0 | d0 IH w].
  - intros Hn. destruct i as [| i1].
    + simpl. apply idl_tid_refl.
    + exact (idl_nle_S_absurd i1 _ Hn).
  - intros Hn. simpl in Hn.
    pose proof (idl_dlen_shift d0 c) as DL. idl_tidQ DL Edl.
    simpl. rewrite Edl.
    destruct (Nat.eqb i (S (idl_dlen d0))) eqn:E.
    + apply idl_tid_refl.
    + apply IH. apply idl_nle_of_leb. apply idl_lebT.
      apply Nat.eqb_neq in E. idl_nleP Hn. lia.
Qed.

(* [内]类差值读数 gauge 不变（合法指标域内） *)
Theorem idl_dsub_shift_invariant : forall (d : idl_dtab) (c : Z) (i j : nat),
  idl_nle i (idl_dlen d) -> idl_nle j (idl_dlen d) ->
  idl_tid Z (idl_dsub (idl_dshift d c) i j) (idl_dsub d i j).
Proof.
  intros d c i j Hi Hj. unfold idl_dsub.
  pose proof (idl_pot_shift_moves d c i Hi) as T1. idl_tidQ T1 E1.
  pose proof (idl_pot_shift_moves d c j Hj) as T2. idl_tidQ T2 E2.
  apply (tid_eq Z (idl_pot (idl_dshift d c) i - idl_pot (idl_dshift d c) j) (idl_pot d i - idl_pot d j)).
  rewrite E1, E2. ring.
Qed.

(* ===================================================================== *)
(* 2. 锚义务已闭列 idl_acol（[锚]类凭证载体：锚闭合事件显式归纳）                    *)
(* ===================================================================== *)

Inductive idl_acol : Set :=
| acol0                          (* 空列：无任何已闭锚义务 *)
| idl_acolS (a : idl_acol) (i : nat) (c : Z).  (* 锚闭合事件：指标 i 外锚至绝对值 c *)

(* 锚读数：该指标最近一次闭合记录的绝对值；未闭 = None *)
Fixpoint idl_aread (i : nat) (a : idl_acol) : option Z :=
  match a with
  | acol0 => None
  | idl_acolS a0 j c => if Nat.eqb i j then Some c else idl_aread i a0
  end.

(* ===================================================================== *)
(* 3. 件 1：三类查询显式分型 idl_qtype + 缺失凭证型标 idl_misscred + 答型 idl_qans          *)
(* ===================================================================== *)

(* 三类查询：[内]平移不变 / [值]价值 / [锚]绝对——语法上只有这三个构造子，
   任何混类提问（例如用 [内]类语法问绝对水平）不可写出。 *)
Inductive idl_qtype : Set :=
| idl_QIN (i j : nat)            (* [内] 平移不变类：问差 i j                    *)
| idl_QVAL (i : nat)             (* [值] 价值类：问指标 i 的绝对量（耗头券）       *)
| idl_QANC (i : nat) (a : Z).    (* [锚] 绝对类：问 i 的绝对水平对锚 a 的对齐差    *)

(* 缺失凭证型标：拒答值携带"缺哪种凭证"的结构信息（显式枚举） *)
Inductive idl_misscred : Set :=
| idl_MC_RANGE (i : nat)   (* 缺在册凭证：指标 i 未入账（0 .. idl_dlen 之外） *)
| MC_VSLOT             (* 缺头券：单槽价值凭证缺席或已焚              *)
| idl_MC_ANCH (i : nat).   (* 缺锚闭凭证：指标 i 无已闭锚义务             *)

(* 答型：左支 = 答值（显式构造），右支 = 结构性拒答（携缺失凭证型标）。
   拒答不是失败：idl_qans_rej 是 idl_qans 的一等构造子。 *)
Inductive idl_qans : Set :=
| idl_qans_val (z : Z)
| idl_qans_rej (mc : idl_misscred).

(* 答型→bool 判读（拒答诚实性定理用） *)
Definition idl_qans_isans (r : idl_qans) : bool :=
  match r with
  | idl_qans_val _ => true
  | idl_qans_rej _ => false
  end.

Definition idl_tid_qans_val (z1 z2 : Z) (H : idl_tid Z z1 z2) :
  idl_tid idl_qans (idl_qans_val z1) (idl_qans_val z2) :=
  idl_tid_cong (@idl_qans_val) z1 z2 H.

(* ===================================================================== *)
(* 4. 件 1：可判定准入谓词——三分派（idl_sdec：sumbool 的信息性凭证版）             *)
(*    三分派 left 支携 Set 层凭证（stdlib sumbool 两支限 Prop，不可用）；        *)
(*    bool 准入取直读定义，与三分派经凭证型刻画互通（见下与 *_correct）。        *)
(* ===================================================================== *)

(* Set 层判定和（sumbool 的信息性凭证版：stdlib sumbool 两支限 Prop，
   无法携带 Set 层凭证，故自造同构三分派型；left/right 支均可携信息性凭证。
   与 option/sigT 同居 Type 层——全链信息性、可提取、零 Prop。） *)
Inductive idl_sdec (A B : Type) : Type :=
| idl_sdec_l (a : A)
| idl_sdec_r (b : B).

(* nat 序的三分派：left = idl_nle 凭证，right = leb=false 的 idl_tid 证据
   （判定本体走全量化引理，避免 destruct 污染目标型中的 scrutinee） *)
Lemma idl_nle_dc_gen : forall (p : bool) (a b : nat),
  p = Nat.leb a b -> idl_sdec (idl_nle a b) (idl_tid bool (Nat.leb a b) false).
Proof.
  intros p a b E. destruct p as [] eqn:Ep.
  - apply idl_sdec_l. exact (idl_nle_of_leb b a (tid_eq bool (Nat.leb a b) true (eq_sym E))).
  - apply idl_sdec_r. exact (tid_eq bool (Nat.leb a b) false (eq_sym E)).
Defined.

Definition idl_nle_dc (a b : nat) : idl_sdec (idl_nle a b) (idl_tid bool (Nat.leb a b) false) :=
  idl_nle_dc_gen (Nat.leb a b) a b eq_refl.

(* [内]类准入三分派：left = 双在册 idl_nle 凭证；right = 缺在册型标 *)
Definition idl_qin_dc (d : idl_dtab) (i j : nat)
  : idl_sdec (prod (idl_nle i (idl_dlen d)) (idl_nle j (idl_dlen d))) idl_misscred.
Proof.
  destruct (idl_nle_dc i (idl_dlen d)) as [Ha | Ha].
  - destruct (idl_nle_dc j (idl_dlen d)) as [Hb | Hb].
    + apply idl_sdec_l. split; assumption.
    + apply idl_sdec_r. apply (idl_MC_RANGE j).
  - apply idl_sdec_r. apply (idl_MC_RANGE i).
Defined.

Definition idl_qin_ok (d : idl_dtab) (i j : nat) : bool :=
  Nat.leb i (idl_dlen d) && Nat.leb j (idl_dlen d).

(* [值]类准入三分派：left = 头券凭证（sigT 携券面绝对量）；right = 缺头券 *)
Definition idl_qval_dc (v : option (nat * Z)) (i : nat)
  : idl_sdec (sigT (fun w : Z => idl_tid (option (nat * Z)) (Some (i, w)) v)) idl_misscred.
Proof.
  destruct v as [[h w] |] eqn:Ev.
  - destruct (Nat.eqb h i) eqn:Eh.
    + apply idl_sdec_l. apply (existT _ w).
      apply Nat.eqb_eq in Eh.
      exact (tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
               (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
    + apply idl_sdec_r. apply MC_VSLOT.
  - apply idl_sdec_r. apply MC_VSLOT.
Defined.

Definition idl_qval_ok (v : option (nat * Z)) (i : nat) : bool :=
  match v with Some p => Nat.eqb (fst p) i | None => false end.

(* 头券券面绝对量读出 *)
Definition idl_vs_val (v : option (nat * Z)) : Z :=
  match v with Some p => snd p | None => 0 end.

(* [锚]类准入三分派：left = 锚闭凭证（sigT 携锚面绝对量）；right = 缺锚闭 *)
Definition idl_qanc_dc (a : idl_acol) (i : nat)
  : idl_sdec (sigT (fun c : Z => idl_tid (option Z) (Some c) (idl_aread i a))) idl_misscred.
Proof.
  destruct (idl_aread i a) as [c |] eqn:E.
  - apply idl_sdec_l. apply (existT _ c). apply idl_tid_refl.
  - apply idl_sdec_r. apply (idl_MC_ANCH i).
Defined.

Definition idl_qanc_ok (a : idl_acol) (i : nat) : bool :=
  match idl_aread i a with Some _ => true | None => false end.

(* 三分派与 bool 准入的互通不经本体展开桥接，而经凭证型刻画：
   idl_qin_dc/idl_qval_dc/idl_qanc_dc 的 left 支型 == idl_qin_correct/idl_qval_correct/idl_qanc_correct
   中与各自 bool 准入 ⟺ 的凭证型（prod idl_nle 对 / sigT 券面 / sigT 锚面）——
   两路定义被同一凭证型钉死，一致性由类型而非引理承担。 *)

(* --- 正确性定理：准入 ⟺ 存在凭证（sigT 携带；⟺ 用 idl_iffT） --- *)

Theorem idl_qin_correct : forall (d : idl_dtab) (i j : nat),
  idl_iffT (idl_tid bool (idl_qin_ok d i j) true)
       (prod (idl_nle i (idl_dlen d)) (idl_nle j (idl_dlen d))).
Proof.
  intros d i j. apply (mkIffT _ _).
  - intros H. unfold idl_qin_ok in H.
    idl_tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
    exact (pair (idl_nle_of_leb (idl_dlen d) i (tid_eq bool _ true E1))
                (idl_nle_of_leb (idl_dlen d) j (tid_eq bool _ true E2))).
  - intros p. destruct p as [Ha Hb].
    pose proof (idl_nle_leb (idl_dlen d) i Ha) as T1. idl_tidQ T1 E1.
    pose proof (idl_nle_leb (idl_dlen d) j Hb) as T2. idl_tidQ T2 E2.
    unfold idl_qin_ok.
    apply (tid_eq bool (Nat.leb i (idl_dlen d) && Nat.leb j (idl_dlen d)) true).
    rewrite E1, E2. reflexivity.
Qed.

Theorem idl_qval_correct : forall (v : option (nat * Z)) (i : nat),
  idl_iffT (idl_tid bool (idl_qval_ok v i) true)
       (sigT (fun w : Z => idl_tid (option (nat * Z)) (Some (i, w)) v)).
Proof.
  intros v i. apply (mkIffT _ _).
  - intros H. unfold idl_qval_ok in H. destruct v as [[h w] |] eqn:Ev.
    + simpl in H. destruct (Nat.eqb h i) eqn:Eh.
      * apply (existT _ w).
        apply Nat.eqb_eq in Eh.
        exact (tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
                 (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
      * idl_tidQ H E. discriminate E.
    + simpl in H. idl_tidQ H E. discriminate E.
  - intros [w H]. unfold idl_qval_ok. destruct v as [[h w0] |] eqn:Ev.
    + idl_tidQ H E. injection E as Ei Ew.
      rewrite Ei. simpl.
      exact (tid_eq bool (Nat.eqb h h) true (Nat.eqb_refl h)).
    + idl_tidQ H E. discriminate E.
Qed.

Theorem idl_qanc_correct : forall (a : idl_acol) (i : nat),
  idl_iffT (idl_tid bool (idl_qanc_ok a i) true)
       (sigT (fun c : Z => idl_tid (option Z) (Some c) (idl_aread i a))).
Proof.
  intros a i. apply (mkIffT _ _).
  - intros H. unfold idl_qanc_ok in H. destruct (idl_aread i a) as [c |] eqn:E.
    + apply (existT _ c). apply idl_tid_refl.
    + idl_tidQ H E2. discriminate E2.
  - intros [c H]. unfold idl_qanc_ok. destruct (idl_aread i a) as [c0 |] eqn:E.
    + apply idl_tid_refl.
    + idl_tidQ H E2. discriminate E2.
Qed.

(* ===================================================================== *)
(* 5. 件 2：结构性拒答——账态 idl_clst + 问答机 idl_qask + 总分派 idl_qdc                   *)
(* ===================================================================== *)

(* CL 账态 = 差表 + 单槽头券 + 锚义务已闭列（窗即差表本身，idl_dtab 定长归纳） *)
Record idl_clst : Set := mkCL
  { cld : idl_dtab                    (* 差表（[内]类唯一数据源）            *)
  ; clv : option (nat * Z)        (* 单槽头券：Some (h, w) = 头券未花    *)
  ; cla : idl_acol }.                 (* 锚义务已闭列（[锚]类唯一数据源）     *)

(* 问答机（三元组版）：每类只读自己的凭证通道——
   [内]读差表 idl_dsub；[值]读头券 idl_vs_val；[锚]读锚闭 idl_aread。绝无跨通道偷读。 *)
Definition idl_qaskR (d : idl_dtab) (v : option (nat * Z)) (a : idl_acol) (q : idl_qtype) : idl_qans :=
  match q with
  | idl_QIN i j =>
      if Nat.leb i (idl_dlen d)
      then (if Nat.leb j (idl_dlen d)
            then idl_qans_val (idl_dsub d i j)
            else idl_qans_rej (idl_MC_RANGE j))
      else idl_qans_rej (idl_MC_RANGE i)
  | idl_QVAL i =>
      if idl_qval_ok v i then idl_qans_val (idl_vs_val v) else idl_qans_rej MC_VSLOT
  | idl_QANC i a0 =>
      if idl_qanc_ok a i
      then idl_qans_val (match idl_aread i a with Some c => c - a0 | None => 0 end)
      else idl_qans_rej (idl_MC_ANCH i)
  end.

(* 准入谓词（bool）：与问答机同源分派 *)
Definition idl_qadmitR (d : idl_dtab) (v : option (nat * Z)) (a : idl_acol) (q : idl_qtype) : bool :=
  match q with
  | idl_QIN i j => idl_qin_ok d i j
  | idl_QVAL i => idl_qval_ok v i
  | idl_QANC i _ => idl_qanc_ok a i
  end.

(* 账态版封装：问答机与准入谓词 *)
Definition idl_qask (s : idl_clst) (q : idl_qtype) : idl_qans := idl_qaskR (cld s) (clv s) (cla s) q.
Definition idl_qadmit (s : idl_clst) (q : idl_qtype) : bool := idl_qadmitR (cld s) (clv s) (cla s) q.

(* 准入与答判读逐点一致（宪法内部自洽） *)
Lemma idl_qadmit_isin : forall (s : idl_clst) (q : idl_qtype),
  idl_tid bool (idl_qadmit s q) (idl_qans_isans (idl_qask s q)).
Proof.
  intros s q. destruct q as [i j | i | i a0].
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR, idl_qans_isans, idl_qin_ok.
    destruct (Nat.leb i (idl_dlen (cld s))); destruct (Nat.leb j (idl_dlen (cld s)));
      apply idl_tid_refl.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR, idl_qans_isans.
    destruct (idl_qval_ok (clv s) i); apply idl_tid_refl.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR, idl_qans_isans.
    destruct (idl_qanc_ok (cla s) i); apply idl_tid_refl.
Qed.

(* 宪法判定面总分派：left = 答值见证；right = 结构性拒答见证（携型标） *)
Definition idl_qdc (s : idl_clst) (q : idl_qtype)
  : idl_sdec (sigT (fun z : Z => idl_tid idl_qans (idl_qask s q) (idl_qans_val z)))
         (sigT (fun mc : idl_misscred => idl_tid idl_qans (idl_qask s q) (idl_qans_rej mc))).
Proof.
  destruct q as [i j | i | i a0].
  - unfold idl_qask, idl_qaskR.
    destruct (Nat.leb i (idl_dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (idl_dlen (cld s))) eqn:Ej.
    + apply idl_sdec_l. apply (existT _ (idl_dsub (cld s) i j)). apply idl_tid_refl.
    + apply idl_sdec_r. apply (existT _ (idl_MC_RANGE j)). apply idl_tid_refl.
    + apply idl_sdec_r. apply (existT _ (idl_MC_RANGE i)). apply idl_tid_refl.
    + apply idl_sdec_r. apply (existT _ (idl_MC_RANGE i)). apply idl_tid_refl.
  - unfold idl_qask, idl_qaskR. destruct (idl_qval_ok (clv s) i) eqn:Ev.
    + apply idl_sdec_l. apply (existT _ (idl_vs_val (clv s))). apply idl_tid_refl.
    + apply idl_sdec_r. apply (existT _ MC_VSLOT). apply idl_tid_refl.
  - unfold idl_qask, idl_qaskR. destruct (idl_qanc_ok (cla s) i) eqn:Ea.
    + apply idl_sdec_l.
      apply (existT _ (match idl_aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply idl_tid_refl.
    + apply idl_sdec_r. apply (existT _ (idl_MC_ANCH i)). apply idl_tid_refl.
Defined.

(* 总分派规范：裁决位 idl_qdc_b 与准入 bool 逐点一致（宪法内部自洽的 bool 面）；
   分支的凭证内容一致性由 idl_qadmit_answer / idl_qadmit_reject 承担 *)
Definition idl_qdc_b (s : idl_clst) (q : idl_qtype) : bool :=
  match idl_qdc s q with idl_sdec_l _ _ _ => true | idl_sdec_r _ _ _ => false end.

Theorem idl_qdc_spec : forall (s : idl_clst) (q : idl_qtype), idl_tid bool (idl_qdc_b s q) (idl_qadmit s q).
Proof.
  intros s q. unfold idl_qdc_b. destruct (idl_qdc s q) as [Cz | Cm].
  - destruct Cz as [w Hw].
    exact (idl_tid_sym bool (idl_qadmit s q) true
             (idl_tid_trans bool (idl_qadmit s q) (idl_qans_isans (idl_qask s q)) true
                (idl_qadmit_isin s q)
                  (idl_tid_cong idl_qans_isans (idl_qask s q) (idl_qans_val w) Hw))).
  - destruct Cm as [mc Hmc].
    exact (idl_tid_sym bool (idl_qadmit s q) false
             (idl_tid_trans bool (idl_qadmit s q) (idl_qans_isans (idl_qask s q)) false
                (idl_qadmit_isin s q)
                  (idl_tid_cong idl_qans_isans (idl_qask s q) (idl_qans_rej mc) Hmc))).
Qed.

(* 拒答诚实性：凡 idl_qask 输出拒答支，准入必为 false（拒答=显式构造，非失败） *)
Theorem idl_qrej_admit_false : forall (s : idl_clst) (q : idl_qtype) (mc : idl_misscred),
  idl_tid idl_qans (idl_qask s q) (idl_qans_rej mc) -> idl_tid bool (idl_qadmit s q) false.
Proof.
  intros s q mc H.
  exact (idl_tid_trans bool (idl_qadmit s q) (idl_qans_isans (idl_qask s q)) false
           (idl_qadmit_isin s q) (idl_tid_cong idl_qans_isans (idl_qask s q) (idl_qans_rej mc) H)).
Qed.

(* 准入真 ⟹ 答值支显式构造（携答值见证） *)
Theorem idl_qadmit_answer : forall (s : idl_clst) (q : idl_qtype), idl_tid bool (idl_qadmit s q) true ->
  sigT (fun z : Z => idl_tid idl_qans (idl_qask s q) (idl_qans_val z)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR, idl_qin_ok in *.
    destruct (Nat.leb i (idl_dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (idl_dlen (cld s))) eqn:Ej.
    + apply (existT _ (idl_dsub (cld s) i j)). apply idl_tid_refl.
    + idl_tidQ H E. discriminate E.
    + idl_tidQ H E. discriminate E.
    + idl_tidQ H E. discriminate E.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR in *.
    destruct (idl_qval_ok (clv s) i) eqn:Ev.
    + apply (existT _ (idl_vs_val (clv s))). apply idl_tid_refl.
    + idl_tidQ H E. discriminate E.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR in *.
    destruct (idl_qanc_ok (cla s) i) eqn:Ea.
    + apply (existT _ (match idl_aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply idl_tid_refl.
    + idl_tidQ H E. discriminate E.
Qed.

(* 准入假 ⟹ 拒答支显式构造（携缺失凭证型标见证）——结构性拒答的存在性 *)
Theorem idl_qadmit_reject : forall (s : idl_clst) (q : idl_qtype), idl_tid bool (idl_qadmit s q) false ->
  sigT (fun mc : idl_misscred => idl_tid idl_qans (idl_qask s q) (idl_qans_rej mc)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR, idl_qin_ok in *.
    destruct (Nat.leb i (idl_dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (idl_dlen (cld s))) eqn:Ej.
    + simpl in H. idl_tidQ H E. discriminate E.
    + apply (existT _ (idl_MC_RANGE j)). apply idl_tid_refl.
    + apply (existT _ (idl_MC_RANGE i)). apply idl_tid_refl.
    + apply (existT _ (idl_MC_RANGE i)). apply idl_tid_refl.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR in *.
    destruct (idl_qval_ok (clv s) i) eqn:Ev.
    + simpl in H. idl_tidQ H E. discriminate E.
    + apply (existT _ MC_VSLOT). apply idl_tid_refl.
  - unfold idl_qadmit, idl_qadmitR, idl_qask, idl_qaskR in *.
    destruct (idl_qanc_ok (cla s) i) eqn:Ea.
    + simpl in H. idl_tidQ H E. discriminate E.
    + apply (existT _ (idl_MC_ANCH i)). apply idl_tid_refl.
Qed.

(* --- 头券生命周期：[值]类答一次即焚，焚后再问 = 结构性拒答附缺头券型标 --- *)

Definition idl_clburn (s : idl_clst) (i : nat) : idl_clst := mkCL (cld s) None (cla s).

Theorem idl_val_fresh_answer : forall (d : idl_dtab) (a : idl_acol) (i : nat) (w : Z),
  idl_tid idl_qans (idl_qask (mkCL d (Some (i, w)) a) (idl_QVAL i)) (idl_qans_val w).
Proof.
  intros d a i w. unfold idl_qask, idl_qaskR, idl_qval_ok. simpl.
  rewrite Nat.eqb_refl. apply idl_tid_refl.
Qed.

Theorem idl_val_burn_reject : forall (s : idl_clst) (i : nat),
  idl_tid idl_qans (idl_qask (idl_clburn s i) (idl_QVAL i)) (idl_qans_rej MC_VSLOT).
Proof.
  intros s i. unfold idl_qask, idl_qaskR, idl_clburn, idl_qval_ok. simpl. apply idl_tid_refl.
Qed.

(* ===================================================================== *)
(* 6. 件 3：[内]类平移不变性（分型押注的语法化）                               *)
(* ===================================================================== *)

(* CL 2.0 押注的分型形式：[内]类裁决在差表 gauge 平移下逐字不变。
   对照 idl_pot_shift_moves：绝对读出恰移动 c——故绝对问题在 [内]类语法内
   不可问出（问了也必得到平移不变的答案，即被类型系统挡在差表语言外）。 *)
Theorem idl_qin_gauge_invariant : forall (d : idl_dtab) (c : Z) (v : option (nat * Z))
                                     (a : idl_acol) (i j : nat),
  idl_tid idl_qans (idl_qask (mkCL (idl_dshift d c) v a) (idl_QIN i j))
           (idl_qask (mkCL d v a) (idl_QIN i j)).
Proof.
  intros d c v a i j. unfold idl_qask, idl_qaskR. cbn [cld clv cla].
  pose proof (idl_dlen_shift d c) as DL. idl_tidQ DL Edl. rewrite Edl.
  destruct (Nat.leb i (idl_dlen d)) eqn:Ei; destruct (Nat.leb j (idl_dlen d)) eqn:Ej.
  - apply idl_tid_qans_val. apply idl_dsub_shift_invariant.
    + exact (idl_nle_of_leb (idl_dlen d) i (tid_eq bool (Nat.leb i (idl_dlen d)) true Ei)).
    + exact (idl_nle_of_leb (idl_dlen d) j (tid_eq bool (Nat.leb j (idl_dlen d)) true Ej)).
  - apply idl_tid_refl.
  - apply idl_tid_refl.
  - apply idl_tid_refl.
Qed.


Open Scope Z_scope.

(* idl_tid → 定义等式提取（证明内部推理用） *)
Definition tidE (A : Type) (x y : A) (H : idl_tid A x y) : x = y :=
  match H in idl_tid _ a b return a = b with idl_tid_refl _ _ => eq_refl end.

(* idl_tid 版 bool 合取拆分 / orb 头假消去（语句零 Prop 纪律的证明体内转接件） *)
Lemma tid_andb_inv : forall a b : bool,
  idl_tid bool (andb a b) true -> prod (idl_tid bool a true) (idl_tid bool b true).
Proof.
  intros a b H. idl_tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
  exact (pair (tid_eq bool _ true E1) (tid_eq bool _ true E2)).
Qed.

Lemma tid_orb_false : forall b : bool,
  idl_tid bool (orb false b) true -> idl_tid bool b true.
Proof.
  intros b H. idl_tidQ H E. rewrite orb_false_l in E.
  exact (tid_eq bool _ true E).
Qed.

(* ===================================================================== *)
(* 1. 判词：结构化裁决值（洞型 + 向 + Z 证据）                                *)
(* ===================================================================== *)

Inductive hole : Set := k0 | k1 | kb | kc | ke | kr.

Definition hix (h : hole) : nat :=
  match h with
  | k0 => 0%nat | k1 => 1%nat | kb => 2%nat | kc => 3%nat | ke => 4%nat | kr => 5%nat
  end.

Definition hmax : nat := 5%nat.

Definition hbeq (a b : hole) : bool := Nat.eqb (hix a) (hix b).

Lemma hbeq_refl : forall h : hole, idl_tid bool (hbeq h h) true.
Proof.
  intros h. apply (tid_eq bool _ true). unfold hbeq. apply Nat.eqb_refl.
Qed.

Lemma hbeq_true : forall a b : hole, idl_tid bool (hbeq a b) true -> idl_tid hole a b.
Proof.
  intros a b H. unfold hbeq in H. idl_tidQ H E.
  destruct a; destruct b; simpl in E; try discriminate E; apply idl_tid_refl.
Qed.

Inductive vdir : Set := vpass | vrej.

Definition dbeq (a b : vdir) : bool :=
  match a with
  | vpass => match b with vpass => true | vrej => false end
  | vrej => match b with vpass => false | vrej => true end
  end.

Lemma dbeq_true : forall a b : vdir, idl_tid bool (dbeq a b) true -> idl_tid vdir a b.
Proof.
  intros a b H. destruct a; destruct b; simpl in H;
    try (idl_tidQ H E; discriminate E); apply idl_tid_refl.
Qed.

Record verd : Set := mkVd { vh : hole ; vd : vdir ; vz : Z }.

Definition vbeq (x y : verd) : bool :=
  andb (hbeq (vh x) (vh y)) (andb (dbeq (vd x) (vd y)) (Z.eqb (vz x) (vz y))).

Lemma vbeq_mkVd : forall (h1 h2 : hole) (d1 d2 : vdir) (z1 z2 : Z),
  idl_tid bool (vbeq (mkVd h1 d1 z1) (mkVd h2 d2 z2))
       (andb (hbeq h1 h2) (andb (dbeq d1 d2) (Z.eqb z1 z2))).
Proof. intros. apply idl_tid_refl. Qed.

Lemma vbeq_head_true : forall (h1 h2 : hole) (z1 z2 : Z),
  hbeq h1 h2 = true -> z1 = z2 ->
  vbeq (mkVd h1 vpass z1) (mkVd h2 vpass z2) = true.
Proof.
  intros h1 h2 z1 z2 Eh Ez. unfold vbeq, vh, vd, vz.
  rewrite Eh, Ez, Z.eqb_refl. reflexivity.
Qed.

Lemma vbeq_inv : forall v1 v2 : verd,
  idl_tid bool (vbeq v1 v2) true ->
  prod (idl_tid hole (vh v1) (vh v2))
       (prod (idl_tid vdir (vd v1) (vd v2)) (idl_tid Z (vz v1) (vz v2))).
Proof.
  intros v1 v2 H. unfold vbeq in H. idl_tidQ H E.
  apply andb_prop in E. destruct E as [E1 E2].
  apply andb_prop in E2. destruct E2 as [E2 E3].
  apply Z.eqb_eq in E3.
  exact (pair (hbeq_true _ _ (tid_eq bool _ true E1))
              (pair (dbeq_true _ _ (tid_eq bool _ true E2))
                    (tid_eq Z _ _ E3))).
Qed.

(* 流内成员（bool 谓词，语句零 Prop） *)
Fixpoint vIn (v : verd) (s : list verd) : bool :=
  match s with
  | nil => false
  | x :: t => orb (vbeq x v) (vIn v t)
  end.

(* 一致性谓词：h 洞上每枚 pass 判词值皆 w *)
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
  idl_tid pinv (pget (pupd h x p) h2) (if hbeq h h2 then x else pget p h2).
Proof.
  intros h h2 x p. destruct h, h2; apply idl_tid_refl.
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

Lemma pj_self_R : forall a : pinv, idl_tid pinv (pjR (pj a a)) a.
Proof.
  intros a. destruct a as [z| |]; cbn [pj pjR fst].
  - apply idl_tid_refl.
  - destruct (Z.eqb z z) eqn:E; cbn [pjR].
    + apply idl_tid_refl.
    + rewrite Z.eqb_refl in E. discriminate E.
  - apply idl_tid_refl.
Qed.

Lemma pjR_PN : forall b : pinv, idl_tid pinv (pjR (pj PN b)) b.
Proof. intros b. apply idl_tid_refl. Qed.

Lemma pjR_PN_inv : forall a b : pinv,
  idl_tid pinv (pjR (pj a b)) PN -> prod (idl_tid pinv a PN) (idl_tid pinv b PN).
Proof.
  intros a b H. destruct a as [z| |]; destruct b as [z0| |];
    idl_tidQ H E; try discriminate E.
  - exact (pair (idl_tid_refl pinv PN) (idl_tid_refl pinv PN)).
  - idl_tidQ H E2. cbn [pj pjR fst] in E2.
    destruct (Z.eqb z z0); discriminate E2.
Qed.

(* 聚合结合律（结果位）：(a⊕b)⊕c == a⊕(b⊕c) *)
Lemma pj_assoc_R : forall a b c : pinv,
  idl_tid pinv (pjR (pj (pjR (pj a b)) c)) (pjR (pj a (pjR (pj b c)))).
Proof.
  intros a b c.
  destruct a, b, c; cbn [pj pjR fst]; try apply idl_tid_refl.
  all: try (destruct (Z.eqb z z0) eqn:Ew; cbn [pj pjR fst]; try apply idl_tid_refl).
  all: try (destruct (Z.eqb z z1) eqn:Eu; cbn [pj pjR fst]; try apply idl_tid_refl).
  all: try (destruct (Z.eqb z0 z1) eqn:Ewu; cbn [pj pjR fst]; try apply idl_tid_refl).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_neq in Ewu; congruence).
  all: try (apply Z.eqb_eq in Ew; apply Z.eqb_neq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (apply Z.eqb_neq in Ew; apply Z.eqb_eq in Eu;
             apply Z.eqb_eq in Ewu; congruence).
  all: try (rewrite Ew; cbn [pj pjR fst]; try apply idl_tid_refl).
Qed.

Definition pjoin (p q : ipins) : prod ipins nat :=
  (mkP (pjR (pj (qa p) (qa q))) (pjR (pj (qb p) (qb q))) (pjR (pj (qc p) (qc q)))
       (pjR (pj (qd p) (qd q))) (pjR (pj (qe p) (qe q))) (pjR (pj (qf p) (qf q))),
   (pjN (pj (qa p) (qa q)) + (pjN (pj (qb p) (qb q)) + (pjN (pj (qc p) (qc q)) +
   (pjN (pj (qd p) (qd q)) + (pjN (pj (qe p) (qe q)) + pjN (pj (qf p) (qf q)))))))%nat).

Lemma pjoin_get : forall (p q : ipins) (h : hole),
  idl_tid pinv (pget (fst (pjoin p q)) h) (pjR (pj (pget p h) (pget q h))).
Proof.
  intros p q h. destruct p as [a b c d e f]. destruct q as [a' b' c' d' e' f'].
  destruct h; apply idl_tid_refl.
Qed.

Lemma pjoin_zero_l : forall p : ipins, idl_tid ipins (fst (pjoin pzero p)) p.
Proof.
  intros p. destruct p as [a b c d e f]. apply (tid_eq ipins _ _).
  apply mkP_ext_eq.
  - exact (tidE pinv _ _ (pjR_PN a)).
  - exact (tidE pinv _ _ (pjR_PN b)).
  - exact (tidE pinv _ _ (pjR_PN c)).
  - exact (tidE pinv _ _ (pjR_PN d)).
  - exact (tidE pinv _ _ (pjR_PN e)).
  - exact (tidE pinv _ _ (pjR_PN f)).
Qed.

Lemma pjoin_self_pins : forall p : ipins, idl_tid ipins (fst (pjoin p p)) p.
Proof.
  intros p. destruct p as [a b c d e f]. apply (tid_eq ipins _ _).
  apply mkP_ext_eq.
  - exact (tidE pinv _ _ (pj_self_R a)).
  - exact (tidE pinv _ _ (pj_self_R b)).
  - exact (tidE pinv _ _ (pj_self_R c)).
  - exact (tidE pinv _ _ (pj_self_R d)).
  - exact (tidE pinv _ _ (pj_self_R e)).
  - exact (tidE pinv _ _ (pj_self_R f)).
Qed.

Lemma pjoin_assoc : forall p q r : ipins,
  idl_tid ipins (fst (pjoin p (fst (pjoin q r))))
            (fst (pjoin (fst (pjoin p q)) r)).
Proof.
  intros p q r. apply (tid_eq ipins _ _).
  apply mkP_ext_eq; symmetry; apply tidE; apply pj_assoc_R.
Qed.

(* ===================================================================== *)
(* 3. 熔炼 melt：判词流单遍折叠为锭（构造段）                                  *)
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

(* 单枚判词的锭：pass 立钉；rej 出差条款 *)
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
  idl_tid pinv (pget (ipin (m1 (mkVd h1 vpass z))) h2)
       (if hbeq h1 h2 then P1 z else PN).
Proof. intros h1 h2 z. destruct h1, h2; apply idl_tid_refl. Qed.

Lemma m1_pin_rej : forall (h1 h2 : hole) (z : Z),
  idl_tid pinv (pget (ipin (m1 (mkVd h1 vrej z))) h2) PN.
Proof. intros h1 h2 z. destruct h1, h2; apply idl_tid_refl. Qed.

Lemma pget_mjoin : forall (g1 g2 : ingot) (h : hole),
  idl_tid pinv (pget (ipin (mjoin g1 g2)) h)
       (pjR (pj (pget (ipin g1) h) (pget (ipin g2) h))).
Proof.
  intros g1 g2 h. unfold mjoin. apply pjoin_get.
Qed.

(* 锭聚合结合律 *)
Lemma mjoin_assoc : forall g1 g2 g3 : ingot,
  idl_tid ingot (mjoin g1 (mjoin g2 g3)) (mjoin (mjoin g1 g2) g3).
Proof.
  intros [p1 r1] [p2 r2] [p3 r3]. unfold mjoin. cbn [ipin irej].
  apply (tid_eq ingot _ _). apply mkIng_ext_eq.
  - exact (tidE ipins _ _ (pjoin_assoc p1 p2 p3)).
  - apply app_assoc.
Qed.

(* 熔炼零元：空锭左么 *)
Lemma mjoin_zero_l : forall g : ingot, idl_tid ingot (mjoin mzero g) g.
Proof.
  intros [p r]. unfold mjoin. cbn [ipin irej mzero].
  apply (tid_eq ingot _ _). apply mkIng_ext_eq.
  - exact (tidE ipins _ _ (pjoin_zero_l p)).
  - reflexivity.
Qed.

(* 主定理 1：熔炼是列表同态——两段构造的代数内容（锭不依赖流的括号方式） *)
Theorem melt_hom : forall s1 s2 : list verd,
  idl_tid ingot (melt (s1 ++ s2)) (mjoin (melt s1) (melt s2)).
Proof.
  induction s1 as [| v t IH]; intros s2.
  - cbn [melt app].
    exact (idl_tid_sym ingot _ _ (mjoin_zero_l (melt s2))).
  - cbn [melt app].
    apply (idl_tid_trans ingot _ (mjoin (m1 v) (mjoin (melt t) (melt s2))) _).
    + apply (idl_tid_cong (mjoin (m1 v)) _ _ (IH s2)).
    + exact (mjoin_assoc (m1 v) (melt t) (melt s2)).
Qed.

(* ===================================================================== *)
(* 4. 钉位守恒：钉=流中 pass 判词的一致聚合（idl_iffT 双向）                        *)
(* ===================================================================== *)

Definition pinokp (w : Z) (x : pinv) : bool :=
  match x with PN => true | P1 z => Z.eqb z w | PB => false end.

(* 钉位聚合与相容性的接口件：P1 w ⊕ b 且 b 与 w 相容 ⟹ 结果与 w 相容 *)
Lemma pj_pinok_r : forall (w : Z) (b : pinv),
  idl_tid bool (pinokp w b) true -> idl_tid bool (pinokp w (pjR (pj (P1 w) b))) true.
Proof.
  intros w b H. destruct b as [ |z| ]; cbn [pj pjR fst pinokp] in H.
  - apply (tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pj pjR fst]. pose proof (tidE bool _ true H) as Hzeq.
    apply Z.eqb_eq in Hzeq. rewrite <- Hzeq. rewrite Z.eqb_refl.
    apply (tid_eq bool _ true). apply Z.eqb_refl.
  - cbn [pinokp] in H. idl_tidQ H E. discriminate E.
Qed.

(* allpass ⟹ 钉位与 w 相容 *)
Lemma allpass_pinok : forall (s : list verd) (h : hole) (w : Z),
  idl_tid bool (allpass h w s) true ->
  idl_tid bool (pinokp w (pget (ipin (melt s)) h)) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - destruct h; apply idl_tid_refl.
  - cbn [melt]. destruct v as [h0 d0 z0]. destruct d0.
    + cbn [allpass vd vh] in H. destruct (hbeq h0 h) eqn:Eh.
      * apply tid_andb_inv in H. destruct H as [Hhead Ht].
        cbn in Hhead.
        pose proof (tidE bool _ true Hhead) as Hheq.
        apply Z.eqb_eq in Hheq.
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        idl_tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd].
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E, Hheq. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h).
        -- apply (tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pinokp] in IPB.
           destruct (Z.eqb w z) eqn:Ewz.
           ++ apply (tid_eq bool _ true). apply Z.eqb_refl.
           ++ pose proof (tidE bool _ true IPB) as E1.
              apply Z.eqb_eq in E1. apply Z.eqb_neq in Ewz. congruence.
        -- cbn [pinokp] in IPB.
           pose proof (tidE bool _ true IPB) as E2.
           discriminate E2.
      * apply tid_andb_inv in H. destruct H as [_ Ht].
        pose proof (IH h w Ht) as IPB.
        pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
        idl_tidQ J EJ. rewrite EJ.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E. cbn [pj pjR fst].
        destruct (pget (ipin (melt t)) h) as [z2| |].
        -- exact IPB.
        -- exact IPB.
        -- cbn [pinokp] in IPB. idl_tidQ IPB E. discriminate E.
    + cbn [allpass vd vh] in H. apply tid_andb_inv in H.
      destruct H as [_ Ht].
      pose proof (IH h w Ht) as IPB.
      pose proof (pget_mjoin (m1 (mkVd h0 vrej z0)) (melt t) h) as J.
      idl_tidQ J EJ. rewrite EJ.
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E. cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E.
      cbn [pj pjR fst].
      destruct (pget (ipin (melt t)) h) as [z2| |].
      -- exact IPB.
      -- exact IPB.
      -- cbn [pinokp] in IPB. idl_tidQ IPB E. discriminate E.
Qed.

(* 钉位 = PN ⟹ 该洞无任何 pass 判词 ⟹ allpass 平凡真 *)
Lemma pinPN_allpass : forall (s : list verd) (h : hole) (w : Z),
  idl_tid pinv (pget (ipin (melt s)) h) PN -> idl_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply idl_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. idl_tidQ J EJ.
    rewrite EJ in H.
    destruct (pjR_PN_inv (pget (ipin (m1 (mkVd h0 d0 z0))) h)
                         (pget (ipin (melt t)) h) H) as [Ha Hb].
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
        idl_tidQ Ha Ea. discriminate Ea.
      * apply (tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true (IH h w Hb)).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      cbn [m1 ipin vd vh vz pupd] in *; rewrite M1E in Ha.
      exact (IH h w Hb).
Qed.

(* 钉位 = P1 z ⟹ 流中确有 pass(h,z) 判词 *)
Lemma pin_P1_in : forall (s : list verd) (h : hole) (z : Z),
  idl_tid pinv (pget (ipin (melt s)) h) (P1 z) ->
  idl_tid bool (vIn (mkVd h vpass z) s) true.
Proof.
  induction s as [| v t IH]; intros h z H.
  - destruct h; idl_tidQ H E; discriminate E.
  - cbn [melt] in H. destruct v as [h0 d0 z0]. cbn [vIn].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. idl_tidQ J EJ.
    rewrite EJ in H.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H.
        destruct b as [ |z1| ]; cbn [pj pjR fst] in H.
        -- idl_tidQ H E. injection E as E. subst z.
           rewrite (vbeq_head_true h0 h z0 z0 Eh (eq_refl z0)).
           apply idl_tid_refl.
        -- destruct (Z.eqb z0 z1) eqn:Ez; cbn [pj pjR fst] in H.
           ++ idl_tidQ H E. injection E as E. subst z.
              rewrite (vbeq_head_true h0 h z0 z0 Eh (eq_refl z0)).
              apply idl_tid_refl.
           ++ idl_tidQ H E. discriminate E.
        -- idl_tidQ H E. discriminate E.
      * (* 头非本洞 pass（hbeq false）：A = PN ⟹ 尾钉 b = P1 z ⟹ IH *)
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj pjR fst] in H.
        destruct b as [ |z1| ]; cbn [pj pjR fst] in H.
        -- idl_tidQ H E. discriminate E.
        -- idl_tidQ H E. injection E as E2. subst z1. cbn [vIn].
           unfold vbeq, vh. rewrite Eh.
           exact (IH h z (tid_eq pinv _ _ (eq_sym EB))).
        -- idl_tidQ H E. discriminate E.
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      destruct b as [ |z1| ].
      -- idl_tidQ H E. discriminate E.
      -- destruct (Z.eqb z1 z) eqn:Ez1z; cbn [pj pjR fst] in H.
         ++ idl_tidQ H E. injection E as Ei.
            unfold vbeq, vh, vd, vz, dbeq.
            destruct (hbeq h0 h); exact (IH h z (tid_eq pinv _ _
                      (eq_trans (eq_sym EB)
                         (f_equal (fun zz : Z => P1 zz) Ei)))).
         ++ idl_tidQ H E. injection E as Ei. rewrite Ei in Ez1z.
            rewrite Z.eqb_refl in Ez1z. discriminate Ez1z.
      -- idl_tidQ H E. discriminate E.
Qed.

(* 钉位 = PN ⟹ 流中不可能有 pass(h,z) 判词（荒谬件，任意 Set 可关） *)
Lemma pin_PN_absurd : forall (s : list verd) (h : hole) (z : Z),
  idl_tid pinv (pget (ipin (melt s)) h) PN ->
  idl_tid bool (vIn (mkVd h vpass z) s) true ->
  forall P : Set, P.
Proof.
  induction s as [| v t IH]; intros h z H Hin.
  - cbn [vIn] in Hin. idl_tidQ Hin E. discriminate E.
  - cbn [melt] in H. destruct v as [h0 d0 z0]. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. idl_tidQ J EJ.
    rewrite EJ in H. rewrite <- EB in H.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z1| ]; cbn [pj pjR fst] in H.
        -- idl_tidQ H E. discriminate E.
        -- destruct (Z.eqb z0 z1) eqn:Ez; cbn [pj pjR fst] in H;
             idl_tidQ H E; discriminate E.
        -- idl_tidQ H E. discriminate E.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. cbn in M1E.
        cbn [m1 ipin vd vh vz pupd] in H.
        rewrite M1E in H. cbn [pj pjR fst] in H.
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        exact (IH h z (idl_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (tid_eq pinv _ _ (eq_sym EB)) H) Hin).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
        exact (IH h z (idl_tid_trans pinv (pget (ipin (melt t)) h) b PN
                           (tid_eq pinv _ _ (eq_sym EB)) H) Hin).
Qed.

(* 钉位 = P1 z1 且流中另有 pass(h,z0) ⟹ z1 = z0（钉值与任何流内 pass 一致） *)
Lemma pin_P1_in_val : forall (s : list verd) (h : hole) (z1 z0 : Z),
  idl_tid pinv (pget (ipin (melt s)) h) (P1 z1) ->
  idl_tid bool (vIn (mkVd h vpass z0) s) true ->
  idl_tid Z z1 z0.
Proof.
  induction s as [| v t IH]; intros h z1 z0 Hp Hin.
  - cbn [vIn] in Hin. idl_tidQ Hin E. discriminate E.
  - cbn [melt] in Hp. destruct v as [h0 d0 z0']. cbn [vIn] in Hin.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0')) (melt t) h) as J. idl_tidQ J EJ.
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
           ++ idl_tidQ Hp E. injection E as Ei.
              exact (idl_tid_trans Z z1 z0' z0 (idl_tid_sym Z z0' z1 (tid_eq Z _ _ Ei))
                       (tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** idl_tidQ Hp E. injection E as Ei.
                 exact (idl_tid_trans Z z1 z0' z0 (idl_tid_sym Z z0' z1 (tid_eq Z _ _ Ei))
                          (tid_eq Z _ _ (proj1 (Z.eqb_eq z0' z0) Ezz0))).
              ** idl_tidQ Hp E. discriminate E.
           ++ idl_tidQ Hp E. discriminate E.
        -- (* 头是本洞 pass 但值 ≠ z0：见证在尾 *)
           pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
           rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj] in Hp.
           destruct b as [ |z2| ]; cbn [pj pjR fst] in Hp.
           ++ exact (pin_PN_absurd t h z0 (tid_eq pinv _ _ (eq_sym EB)) Hin _).
           ++ destruct (Z.eqb z0' z2) eqn:Ez; cbn [pj pjR fst] in Hp.
              ** idl_tidQ Hp E. injection E as Ei.
                 assert (Ht1 : idl_tid pinv (pget (ipin (melt t)) h) (P1 z1)).
                 { rewrite <- EB. apply (tid_eq pinv (P1 z2) (P1 z1)).
                   rewrite (eq_trans (eq_sym (proj1 (Z.eqb_eq z0' z2) Ez)) Ei).
                   reflexivity. }
                 exact (IH h z1 z0 Ht1 Hin).
              ** idl_tidQ Hp E. discriminate E.
           ++ idl_tidQ Hp E. discriminate E.
      * (* 头非本洞 pass（hbeq false）：A = PN ⟹ 见证在尾 ⟹ IH *)
        unfold vbeq, vh, vd, vz in Hin. rewrite Eh in Hin.
        cbn [dbeq andb orb] in Hin.
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0')) as M1E.
        rewrite Eh in M1E. rewrite M1E in Hp. cbn [pj pjR fst] in Hp.
        exact (IH h z1 z0 (idl_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                                (tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
    + (* 头非本洞 pass：A = PN ⟹ 见证在尾 ⟹ IH *)
      unfold vbeq, vh, vd, vz, dbeq in Hin.
      destruct (hbeq h0 h);
      pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0')) as M1E;
      rewrite M1E in Hp; cbn [pj pjR fst] in Hp;
      exact (IH h z1 z0 (idl_tid_trans pinv (pget (ipin (melt t)) h) b (P1 z1)
                              (tid_eq pinv _ _ (eq_sym EB)) Hp) Hin).
Qed.

(* 钉位 = P1 w ⟹ 全体 pass 判词一致于 w *)
Lemma pin_P1_allpass : forall (s : list verd) (h : hole) (w : Z),
  idl_tid pinv (pget (ipin (melt s)) h) (P1 w) ->
  idl_tid bool (allpass h w s) true.
Proof.
  induction s as [| v t IH]; intros h w H.
  - apply idl_tid_refl.
  - cbn [melt] in H. destruct v as [h0 d0 z0].
    pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. idl_tidQ J EJ.
    rewrite EJ in H.
    remember (pget (ipin (melt t)) h) as b eqn:EB.
    destruct d0.
    + destruct (hbeq h0 h) eqn:Eh.
      * pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj] in H.
        destruct b as [ |z2| ]; cbn [pj pjR fst] in H.
        -- (* b = PN：钉 = P1 z0 ⟹ z0 = w；尾无 pass ⟹ allpass 尾平凡 *)
           idl_tidQ H E. injection E as Ei.
           apply (tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ei.
           rewrite Z.eqb_refl.
           rewrite (tidE bool _ true
                      (pinPN_allpass t h w (tid_eq pinv _ _ (eq_sym EB)))).
           reflexivity.
        -- destruct (Z.eqb z0 z2) eqn:Ez2; cbn [pj pjR fst] in H.
           ++ idl_tidQ H E. injection E as Ei. apply Z.eqb_eq in Ez2.
              assert (Htw : idl_tid pinv (pget (ipin (melt t)) h) (P1 w)).
              { rewrite <- EB. apply (tid_eq pinv (P1 z2) (P1 w)).
                rewrite (eq_trans (eq_sym Ez2) Ei). reflexivity. }
              apply (tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh, Ez2.
              rewrite (eq_trans (eq_sym Ez2) Ei), Z.eqb_refl.
              rewrite (tidE bool _ true (IH h w Htw)). reflexivity.
           ++ idl_tidQ H E. discriminate E.
        -- idl_tidQ H E. discriminate E.
      * (* 头非本洞 pass：钉 = b ⟹ 尾见 ⟹ IH *)
        pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
        rewrite Eh in M1E. rewrite M1E in H. cbn [pj pjR fst] in H.
        apply (tid_eq bool _ true). cbn [allpass vd vh]. rewrite Eh.
        exact (tidE bool _ true
                (IH h w (idl_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                           (tid_eq pinv _ _ (eq_sym EB)) H))).
    + pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
      rewrite M1E in H. cbn [pj pjR fst] in H.
      exact (IH h w (idl_tid_trans pinv (pget (ipin (melt t)) h) b (P1 w)
                         (tid_eq pinv _ _ (eq_sym EB)) H)).
Qed.

(* 主定理 2：钉位 idl_iffT——钉 = 流中 pass 判词的一致聚合（守恒双向：
   不发明——钉值必来自流内判词；不歪曲——流内 pass 判词全体一致） *)
Theorem pin_iffT : forall (s : list verd) (h : hole) (w : Z),
  idl_iffT (idl_tid pinv (pget (ipin (melt s)) h) (P1 w))
       (prod (idl_tid bool (vIn (mkVd h vpass w) s) true)
             (idl_tid bool (allpass h w s) true)).
Proof.
  intros s h w. apply (mkIffT _ _).
  - intros H. exact (pair (pin_P1_in s h w H) (pin_P1_allpass s h w H)).
  - intros Hp. destruct Hp as [Hin Hall].
    induction s as [| v t IH].
    + cbn [vIn] in Hin. idl_tidQ Hin E. discriminate E.
    + cbn [melt]. destruct v as [h0 d0 z0]. cbn [vIn] in Hin.
      destruct (vbeq (mkVd h0 d0 z0) (mkVd h vpass w)) eqn:Ev.
      * (* 头即见证 (h, vpass, w) *)
        destruct (vbeq_inv _ _ (tid_eq bool _ _ Ev)) as [Ex [Ed Ezz]].
        cbn [vh vd vz] in Ex, Ed, Ezz.
        pose proof (pget_mjoin (m1 (mkVd h0 d0 z0)) (melt t) h) as J. idl_tidQ J EJ.
        rewrite EJ.
        rewrite (tidE hole _ _ Ex), (tidE vdir _ _ Ed), (tidE Z _ _ Ezz).
        pose proof (tidE pinv _ _ (m1_pin_head h h w)) as M1E.
        rewrite M1E. rewrite (tidE bool _ true (hbeq_refl h)). cbn [pj].
        pose proof (tidE bool _ true Hall) as E0.
        cbn [allpass vd vh] in E0.
        rewrite (tidE hole _ _ Ex), (tidE Z _ _ Ezz) in E0.
        rewrite (tidE bool _ true (hbeq_refl h)), Z.eqb_refl in E0.
        apply andb_prop in E0. destruct E0 as [_ E0t].
        pose proof (allpass_pinok t h w (tid_eq bool _ true E0t)) as PB.
        destruct (pget (ipin (melt t)) h) as [ |z2| ].
        -- apply idl_tid_refl.
        -- cbn [pinokp] in PB. idl_tidQ PB E. apply Z.eqb_eq in E. cbn [pjR fst].
           rewrite E, Z.eqb_refl. apply idl_tid_refl.
        -- cbn [pinokp] in PB. idl_tidQ PB E. discriminate E.
      * (* 头非见证 *)
        destruct d0.
        -- destruct (hbeq h0 h) eqn:Eh.
           ++ (* hbeq true：allpass 头项给 z0 = w，与 Ev 的假矛盾 *)
              pose proof (tidE bool _ true Hall) as E0.
              cbn [allpass vd vh] in E0. apply andb_prop in E0.
              destruct E0 as [Ehead _].
              rewrite Eh in Ehead. cbn in Ehead. apply Z.eqb_eq in Ehead.
              unfold vbeq, vh, vd, vz, dbeq in Ev.
              rewrite Eh, Ehead in Ev. rewrite Z.eqb_refl in Ev. discriminate Ev.
           ++ (* hbeq false：见证在尾；钉 = 尾钉 *)
              pose proof (pget_mjoin (m1 (mkVd h0 vpass z0)) (melt t) h) as J.
              idl_tidQ J EJ. rewrite EJ.
              pose proof (tidE pinv _ _ (m1_pin_head h0 h z0)) as M1E.
              rewrite Eh in M1E. rewrite M1E. cbn [pj pjR fst].
              pose proof (tidE bool _ true Hall) as E0.
              cbn [allpass vd vh] in E0. apply andb_prop in E0.
              destruct E0 as [_ E0t].
              exact (IH Hin (tid_eq bool _ true E0t)).
        -- (* 头 vrej：钉 = 尾钉 *)
           pose proof (pget_mjoin (m1 (mkVd h0 vrej z0)) (melt t) h) as J.
           idl_tidQ J EJ. rewrite EJ.
           pose proof (tidE pinv _ _ (m1_pin_rej h0 h z0)) as M1E.
           rewrite M1E. cbn [pj pjR fst].
           pose proof (tidE bool _ true Hall) as E0.
           cbn [allpass vd vh] in E0. apply andb_prop in E0.
           destruct E0 as [_ E0t].
           exact (IH Hin (tid_eq bool _ true E0t)).
Qed.

(* ===================================================================== *)
(* 5. 拒值差条款的流侧守恒                                                    *)
(* ===================================================================== *)

Fixpoint cinc (h : hole) (e : Z) (l : list (prod hole Z)) : bool :=
  match l with
  | nil => false
  | x :: t => orb (andb (hbeq h (fst x)) (Z.eqb e (snd x))) (cinc h e t)
  end.

Lemma cinc_app : forall (h : hole) (e : Z) (l1 l2 : list (prod hole Z)),
  idl_tid bool (cinc h e (l1 ++ l2)) (orb (cinc h e l1) (cinc h e l2)).
Proof.
  intros h e l1 l2. induction l1 as [| x t IH]; cbn [cinc app].
  - apply idl_tid_refl.
  - idl_tidQ IH EI. rewrite EI.
    apply (tid_eq bool _ _). apply Bool.orb_assoc.
Qed.

(* 流中 rej(h,e) 判词 ⟹ 条款入锭 *)
Theorem rej_from_stream : forall (s : list verd) (h : hole) (e : Z),
  idl_tid bool (vIn (mkVd h vrej e) s) true ->
  idl_tid bool (cinc h e (irej (melt s))) true.
Proof.
  induction s as [| v t IH]; intros h e H.
  - cbn [vIn] in H. idl_tidQ H E. discriminate E.
  - cbn [melt]. destruct v as [h0 d0 z0]. cbn [vIn] in H.
    unfold mjoin. cbn [irej]. destruct d0.
    + cbn [m1 irej app cinc vd vh vz]. apply IH.
      unfold vbeq, vh, vd, vz, dbeq in H. destruct (hbeq h0 h); exact H.
    + cbn [m1 irej app cinc vd vh vz]. apply (tid_eq bool _ true).
      destruct (vbeq (mkVd h0 vrej z0) (mkVd h vrej e)) eqn:Ev.
      * destruct (vbeq_inv _ _ (tid_eq bool _ _ Ev)) as [Ex [Ed Ezz]].
        cbn [vh vd vz] in Ex, Ed, Ezz.
        cbn [fst snd].
        rewrite (tidE hole _ _ Ex), (tidE Z _ _ Ezz).
        rewrite (tidE bool _ true (hbeq_refl h)), Z.eqb_refl.
        reflexivity.
      * (* 头非该 rej 判词：H 给尾成员性 ⟹ IH 给尾 cinc ⟹ 两真和项 *)
        pose proof (IH h e H) as C. idl_tidQ C EC. cbn [fst snd]. rewrite EC.
        destruct (hbeq h h0); destruct (Z.eqb e z0); reflexivity.
Qed.

(* ===================================================================== *)
(* 6. 织 weave：差分段（只吃锭；织出件 = Q4 idl_dtab；欠单如实记欠）                *)
(* ===================================================================== *)

Definition pvz (x : pinv) : Z := match x with P1 z => z | _ => 0 end.

(* 织出件：六槽差分表，头元 k0 规范 0（Q4 载体 idl_dtab） *)
Definition dbuild (p : ipins) : idl_dtab :=
  idl_dtabSnoc
    (idl_dtabSnoc
       (idl_dtabSnoc
          (idl_dtabSnoc
             (idl_dtabSnoc (idl_dtab1 0) (pvz (qb p)))
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
  idl_tid Z (idl_pot (dbuild p) (hix h)) (slotz p h).
Proof. intros p h. destruct h; apply idl_tid_refl. Qed.

Lemma dsub_pget : forall (p : ipins) (h : hole),
  idl_tid Z (idl_dsub (dbuild p) (hix h) O)
       (match h with k0 => 0 | _ => pvz (pget p h) end).
Proof.
  intros p h. unfold idl_dsub.
  pose proof (dbuild_pot p h) as T1. idl_tidQ T1 E1.
  pose proof (dbuild_pot p k0) as T2. idl_tidQ T2 E2.
  rewrite E1. change (idl_pot (dbuild p) O) with (idl_pot (dbuild p) (hix k0)).
  rewrite E2. apply (tid_eq Z _ _).
  destruct h; cbn [slotz]; apply Z.sub_0_r.
Qed.

Lemma dbuild_len : forall p : ipins, idl_tid nat (idl_dlen (dbuild p)) hmax.
Proof. intros p. apply (tid_eq nat _ _). reflexivity. Qed.

(* 欠单条目：缺钉 / 钉冲突 / 差条款相抵 *)
Inductive idl_iou : Set :=
| IOU_NOPIN (h : hole)
| IOU_BAD (h : hole)
| IOU_REJ (h : hole) (e : Z).

Definition rjbad (p : ipins) (x : prod hole Z) : bool :=
  Z.eqb (idl_dsub (dbuild p) (hix (fst x)) O) (snd x).

Fixpoint rejious (p : ipins) (l : list (prod hole Z)) : list idl_iou :=
  match l with
  | nil => nil
  | x :: t => if rjbad p x then IOU_REJ (fst x) (snd x) :: rejious p t
              else rejious p t
  end.

Definition headiou (p : ipins) : list idl_iou :=
  match pget p k0 with
  | PN => nil
  | P1 z => if Z.eqb z 0 then nil else IOU_BAD k0 :: nil
  | PB => IOU_BAD k0 :: nil
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
      | PN => IOU_NOPIN h :: slotiousL p t
      | PB => IOU_BAD h :: slotiousL p t
      end
  end.

Fixpoint allpin1 (p : ipins) (hs : list hole) : bool :=
  match hs with
  | nil => true
  | h :: t => andb (isP1 (pget p h)) (allpin1 p t)
  end.

(* slotiousL 的头展开等式（证明内推理用；定义性成立） *)
Lemma slotiousL_cons : forall p h t,
  idl_tid (list idl_iou) (slotiousL p (h :: t))
      (match pget p h with
       | P1 _ => slotiousL p t
       | PN => IOU_NOPIN h :: slotiousL p t
       | PB => IOU_BAD h :: slotiousL p t
       end).
Proof. intros p h t. apply idl_tid_refl. Qed.

Lemma slotiousL_nil_allpin1 : forall p hs,
  idl_tid (list idl_iou) (slotiousL p hs) nil -> idl_tid bool (allpin1 p hs) true.
Proof.
  intros p hs. induction hs as [| h t IH]; intros H.
  - apply idl_tid_refl.
  - pose proof (tidE (list idl_iou) _ _ (slotiousL_cons p h t)) as E1.
    rewrite E1 in H. cbn [allpin1].
    destruct (pget p h) as [ |z| ] eqn:Hg.
    + cbn in H. idl_tidQ H E. discriminate E.
    + cbn in H.
      apply (tid_eq bool _ true).
      exact (tidE bool _ true (IH H)).
    + cbn in H. idl_tidQ H E. discriminate E.
Qed.

Lemma allpin1_hit : forall p hs h,
  idl_tid bool (allpin1 p hs) true -> idl_tid bool (hin h hs) true ->
  idl_tid bool (isP1 (pget p h)) true.
Proof.
  intros p hs h. induction hs as [| h' t IH]; intros HA Hh.
  - cbn [hin] in Hh. idl_tidQ Hh E. discriminate E.
  - cbn [allpin1 hin] in HA, Hh.
    destruct (hbeq h' h) eqn:Ex.
    + idl_tidQ HA E. apply andb_prop in E. destruct E as [E1 _].
      pose proof (hbeq_true h' h (tid_eq bool _ _ Ex)) as E2.
      rewrite <- (tidE hole _ _ E2).
      exact (tid_eq bool _ _ E1).
    + apply IH.
      * idl_tidQ HA E. apply andb_prop in E. destruct E as [_ E2].
        exact (tid_eq bool _ _ E2).
      * idl_tidQ Hh Eh. rewrite Bool.orb_false_l in Eh.
        exact (tid_eq bool _ _ Eh).
Qed.

Definition iouof (g : ingot) : list idl_iou :=
  headiou (ipin g) ++ (slotiousL (ipin g) slotL ++ rejious (ipin g) (irej g)).

Inductive weaveout : Set := wok (d : idl_dtab) | wiou (l : list idl_iou).

Definition weave (g : ingot) : weaveout :=
  match iouof g with
  | nil => wok (dbuild (ipin g))
  | l => wiou l
  end.

Definition weave_b (g : ingot) : bool :=
  match weave g with wok _ => true | wiou _ => false end.

(* 拒值差条款的段间差分判定：条款全过 ⟸ 条款清点为空 *)
Lemma rejious_nil_ok : forall (p : ipins) (l : list (prod hole Z)),
  idl_tid (list idl_iou) (rejious p l) nil ->
  forall (h : hole) (e : Z), idl_tid bool (cinc h e l) true ->
  idl_tid bool (negb (rjbad p (h, e))) true.
Proof.
  intros p l. induction l as [| x t IH]; intros Hn h e Hc.
  - cbn [cinc] in Hc. idl_tidQ Hc E. discriminate E.
  - cbn [rejious] in Hn. destruct (rjbad p x) eqn:Er.
    + idl_tidQ Hn E. discriminate E.
    + cbn [cinc] in Hc. destruct x as [xh xe].
      cbn [rjbad fst snd] in Er.
      destruct (andb (hbeq h xh) (Z.eqb e xe)) eqn:Eh.
      * apply andb_prop in Eh. destruct Eh as [Eh1 Eh2].
        pose proof (hbeq_true h xh (tid_eq bool _ _ Eh1)) as Eh1t.
        pose proof (tidE hole _ _ Eh1t) as Exe.
        apply Z.eqb_eq in Eh2.
        cbn [rjbad fst snd]. rewrite Exe, Eh2, Er. apply idl_tid_refl.
      * apply IH.
        -- exact Hn.
        -- cbn [fst snd] in Hc. rewrite Eh in Hc. exact Hc.
Qed.

Lemma headiou_nil_inv : forall p : ipins,
  idl_tid (list idl_iou) (headiou p) nil ->
  idl_tid bool (match pget p k0 with
            | PN => true
            | P1 z => Z.eqb z 0
            | PB => false
            end) true.
Proof.
  intros p H. unfold headiou in H. destruct (pget p k0) as [z| |].
  - apply idl_tid_refl.
  - destruct (Z.eqb z 0); [apply idl_tid_refl | idl_tidQ H E; discriminate E].
  - idl_tidQ H E. discriminate E.
Qed.

Lemma weave_wok_inv : forall (g : ingot) (d : idl_dtab),
  idl_tid weaveout (weave g) (wok d) ->
  prod (idl_tid (list idl_iou) (iouof g) nil) (idl_tid idl_dtab d (dbuild (ipin g))).
Proof.
  intros g d H. unfold weave in H.
  destruct (iouof g) as [| x t] eqn:E.
  - idl_tidQ H H2. injection H2 as H2.
    exact (pair (idl_tid_refl (list idl_iou) nil)
                (tid_eq idl_dtab d (dbuild (ipin g)) (eq_sym H2))).
  - idl_tidQ H H2. discriminate H2.
Qed.

(* 判词满足性判定（段间差分可判定的逐词形态）：
   pass(h,w) ⟺ 织出表头相对差 = w；rej(h,e) ⟺ 头相对差 ≠ e（非零差条款成立） *)
Definition vrespects (d : idl_dtab) (v : verd) : bool :=
  match vd v with
  | vpass => Z.eqb (idl_dsub d (hix (vh v)) O) (vz v)
  | vrej => negb (Z.eqb (idl_dsub d (hix (vh v)) O) (vz v))
  end.

(* 主定理 3：织出即合法——流中每枚判词都被织出表满足（出生免疫跨洞非法） *)
Theorem weave_sound : forall (s : list verd) (d : idl_dtab),
  idl_tid weaveout (weave (melt s)) (wok d) ->
  forall v : verd, idl_tid bool (vIn v s) true -> idl_tid bool (vrespects d v) true.
Proof.
  intros s d Hw.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd].
  idl_tidQ Hn En. idl_tidQ Hd Ed.
  unfold iouof in En. apply app_eq_nil in En. destruct En as [Eh Esr].
  apply app_eq_nil in Esr. destruct Esr as [Es Er].
  pose proof (tid_eq (list idl_iou) (headiou (ipin (melt s))) nil Eh) as TH.
  pose proof (tid_eq (list idl_iou) (slotiousL (ipin (melt s)) slotL) nil Es) as TS.
  pose proof (tid_eq (list idl_iou) (rejious (ipin (melt s)) (irej (melt s))) nil Er)
    as TR.
  pose proof (slotiousL_nil_allpin1 (ipin (melt s)) slotL TS) as AP.
  pose proof (headiou_nil_inv (ipin (melt s)) TH) as HD.
  induction s as [| v0 t IH]; intros v Hv.
  - cbn [vIn] in Hv. idl_tidQ Hv E. discriminate E.
  - cbn [vIn] in Hv. destruct v as [h0 d0 z0]. destruct d0.
    + (* pass(h0,z0)：织出表上头相对差恰为 z0 *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      rewrite (tidE Z _ _ (dsub_pget (ipin (melt (v0 :: t))) h0)).
      destruct (pget (ipin (melt (v0 :: t))) h0) as [ |z1| ] eqn:Ep.
      * (* 钉缺：头洞由头规引理，余洞由六槽清点 *)
        destruct h0.
        -- exact (pin_PN_absurd (v0 :: t) k0 z0 (tid_eq pinv _ _ Ep) Hv
                   (idl_tid bool (Z.eqb 0 z0) true)).
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
      * (* 钉位 P1 z1：pin_P1_in_val 得 z1 = z0 *)
        pose proof (pin_P1_in_val (v0 :: t) h0 z1 z0 (tid_eq pinv _ _ Ep) Hv) as ZP.
        idl_tidQ ZP EZ.
        destruct h0.
        -- (* k0：P1 z1 ⟹ 头规 z1 = 0；与 ZP 得 z0 = 0 *)
           unfold headiou in TH. rewrite Ep in TH. cbn in TH.
           destruct (Z.eqb z1 0) eqn:Ez10.
           ++ apply Z.eqb_eq in Ez10. rewrite Ez10 in EZ.
              rewrite <- EZ.
              apply (tid_eq bool _ true). apply Z.eqb_refl.
           ++ idl_tidQ TH E. discriminate E.
        -- cbn [pvz]. rewrite EZ.
           apply (tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (tid_eq bool _ true). apply Z.eqb_refl.
        -- cbn [pvz]. rewrite EZ.
           apply (tid_eq bool _ true). apply Z.eqb_refl.
      * (* 钉冲突：头洞由头规引理，余洞由六槽清点 *)
        destruct h0.
        -- unfold headiou in HD. rewrite Ep in HD. cbn in HD.
           idl_tidQ HD E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL k1 AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kb AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kc AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL ke AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
        -- pose proof (allpin1_hit (ipin (melt (v0 :: t))) slotL kr AP
                        (idl_tid_refl bool true)) as HP1.
           rewrite Ep in HP1. cbn in HP1. idl_tidQ HP1 E. discriminate E.
    + (* rej(h0,z0)：织出表与拒值之差非零——差条款全过 *)
      unfold vrespects. cbn [vd vz vh]. rewrite Ed.
      pose proof (rejious_nil_ok (ipin (melt (v0 :: t))) (irej (melt (v0 :: t))) TR
                        h0 z0 (rej_from_stream (v0 :: t) h0 z0 Hv)) as RJ.
      unfold rjbad in RJ. cbn [fst snd] in RJ.
      rewrite (tidE bool _ true RJ). apply idl_tid_refl.
Qed.

(* ===================================================================== *)
(* 7. 重放不变：差分段对构造段封闭——活锁失去载体                                *)
(* ===================================================================== *)

Definition isnil {A : Type} (l : list A) : bool :=
  match l with nil => true | _ => false end.

Lemma isnil_app : forall (A : Type) (a b : list A),
  idl_tid bool (isnil (a ++ b)) (andb (isnil a) (isnil b)).
Proof. intros A a b. destruct a; apply idl_tid_refl. Qed.

Lemma rejious_app_isnil : forall (p : ipins) (l1 l2 : list (prod hole Z)),
  idl_tid bool (isnil (rejious p (l1 ++ l2)))
       (andb (isnil (rejious p l1)) (isnil (rejious p l2))).
Proof.
  intros p l1 l2. induction l1 as [| x t IH]; cbn [app rejious].
  - apply idl_tid_refl.
  - destruct (rjbad p x).
    + apply idl_tid_refl.
    + apply IH.
Qed.

Lemma andb_idem_tid : forall b : bool, idl_tid bool (andb b b) b.
Proof. intros b. destruct b; apply idl_tid_refl. Qed.

Lemma iouof_mjoin_self_b : forall g : ingot,
  idl_tid bool (isnil (iouof (mjoin g g))) (isnil (iouof g)).
Proof.
  intros [p l]. unfold mjoin, iouof. cbn [ipin irej].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)).
  rewrite (tidE bool _ _ (isnil_app idl_iou (headiou p)
             (slotiousL p slotL ++ rejious p (l ++ l)))).
  rewrite (tidE bool _ _ (isnil_app idl_iou (slotiousL p slotL) (rejious p (l ++ l)))).
  rewrite (tidE bool _ _ (isnil_app idl_iou (headiou p)
              (slotiousL p slotL ++ rejious p l))).
  rewrite (tidE bool _ _ (isnil_app idl_iou (slotiousL p slotL) (rejious p l))).
  rewrite (tidE bool _ _ (rejious_app_isnil p l l)).
  destruct (isnil (headiou p)); destruct (isnil (slotiousL p slotL));
    destruct (isnil (rejious p l)); apply idl_tid_refl.
Qed.

(* 织造判定 = 欠单清点是否为空（weave_b 的 isnil 形态，证明内转接件） *)
Lemma weave_b_eq : forall g : ingot,
  idl_tid bool (weave_b g) (isnil (iouof g)).
Proof.
  intros g. unfold weave_b, weave.
  destruct (iouof g) as [| x t] eqn:E.
  - apply idl_tid_refl.
  - apply idl_tid_refl.
Qed.

(* 主定理 4a：整流重放不改变织造判定 *)
Theorem weave_replay_b : forall s : list verd,
  idl_tid bool (weave_b (melt (s ++ s))) (weave_b (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. idl_tidQ Hh Eh.
  rewrite (tidE bool _ _ (weave_b_eq (melt (s ++ s)))).
  rewrite Eh.
  rewrite (tidE bool _ _ (iouof_mjoin_self_b (melt s))).
  rewrite (tidE bool _ _ (weave_b_eq (melt s))).
  apply idl_tid_refl.
Qed.

Lemma nil_isnil : forall l : list idl_iou,
  idl_tid (list idl_iou) l nil -> idl_tid bool (isnil l) true.
Proof. intros l H. rewrite (tidE (list idl_iou) _ nil H). apply idl_tid_refl. Qed.

Lemma isnil_eq_nil : forall l : list idl_iou,
  idl_tid bool (isnil l) true -> idl_tid (list idl_iou) l nil.
Proof.
  intros l H. destruct l as [| x t].
  - apply idl_tid_refl.
  - cbn [isnil] in H. idl_tidQ H E. discriminate E.
Qed.

(* 主定理 4b：重放不改变织出件（差分段对构造段封闭：wok 支不变） *)
Theorem weave_replay_d : forall (s : list verd) (d : idl_dtab),
  idl_tid weaveout (weave (melt (s ++ s))) (wok d) ->
  idl_tid weaveout (weave (melt s)) (wok d).
Proof.
  intros s d H.
  destruct (weave_wok_inv (melt (s ++ s)) d H) as [Hn Hd].
  idl_tidQ Hn En. idl_tidQ Hd Ed.
  pose proof (melt_hom s s) as Hh. idl_tidQ Hh Eh.
  pose proof (f_equal iouof (tidE ingot _ _ Hh)) as Eio.
  pose proof (nil_isnil _ Hn) as HnB.
  rewrite Eio in HnB.
  rewrite (tidE bool _ _ (iouof_mjoin_self_b (melt s))) in HnB.
  pose proof (isnil_eq_nil (iouof (melt s)) HnB) as Ens.
  pose proof (tidE (list idl_iou) _ nil Ens) as EnsL.
  unfold weave. rewrite EnsL.
  apply (tid_eq weaveout _ _). rewrite Ed, Eh.
  unfold mjoin. cbn [ipin].
  rewrite (tidE ipins _ _ (pjoin_self_pins (ipin (melt s)))).
  reflexivity.
Qed.

(* 冲突清点：钉位为 PB 的洞数（同洞异值至多记一次） *)
Definition pbc (x : pinv) : nat := match x with PB => 1%nat | _ => 0%nat end.

Definition iconf (g : ingot) : nat :=
  (pbc (qa (ipin g)) + (pbc (qb (ipin g)) + (pbc (qc (ipin g)) +
  (pbc (qd (ipin g)) + (pbc (qe (ipin g)) + pbc (qf (ipin g)))))))%nat.

Lemma iconf_mjoin_self : forall g : ingot, idl_tid nat (iconf (mjoin g g)) (iconf g).
Proof.
  intros [p l]. unfold mjoin, iconf. cbn [ipin].
  rewrite (tidE ipins _ _ (pjoin_self_pins p)). apply idl_tid_refl.
Qed.

(* 主定理 4c：重放不新增冲突洞（冲突是洞的属性，不是事件计数） *)
Theorem replay_census : forall s : list verd,
  idl_tid nat (iconf (melt (s ++ s))) (iconf (melt s)).
Proof.
  intros s.
  pose proof (melt_hom s s) as Hh. idl_tidQ Hh Eh. rewrite Eh.
  exact (iconf_mjoin_self (melt s)).
Qed.

(* ===================================================================== *)
(* 8. Q4 判定面咬合：织出件受 [内]类查询逐词复核                                *)
(* ===================================================================== *)

Lemma hix_nle : forall h : hole, idl_nle (hix h) hmax.
Proof.
  destruct h.
  - apply idl_nle_0.
  - apply idl_nle_S. apply idl_nle_S. apply idl_nle_S. apply idl_nle_S. apply idl_nle_n.
  - apply idl_nle_S. apply idl_nle_S. apply idl_nle_S. apply idl_nle_n.
  - apply idl_nle_S. apply idl_nle_S. apply idl_nle_n.
  - apply idl_nle_S. apply idl_nle_n.
  - apply idl_nle_n.
Qed.

(* 主定理 5：织出件交给 Q4 问答机复核——[内]类差值查询的答案恰为判词钉值。
   织机出生即证 + Q4 判定面独立复核，两件咬合。 *)
Theorem recheck_pass : forall (s : list verd) (d : idl_dtab) (h : hole) (w : Z),
  idl_tid weaveout (weave (melt s)) (wok d) ->
  idl_tid bool (vIn (mkVd h vpass w) s) true ->
  idl_tid idl_qans (idl_qask (mkCL d None acol0) (idl_QIN (hix h) O)) (idl_qans_val w).
Proof.
  intros s d h w Hw Hv.
  destruct (weave_wok_inv (melt s) d Hw) as [Hn Hd]. idl_tidQ Hd Ed.
  rewrite Ed in Hw. rewrite Ed.
  pose proof (weave_sound s (dbuild (ipin (melt s))) Hw
                (mkVd h vpass w) Hv) as VR.
  unfold vrespects in VR. cbn [vd vz vh] in VR.
  pose proof (tidE bool _ true VR) as EV. apply Z.eqb_eq in EV.
  unfold idl_qask, idl_qaskR. cbn [cld clv cla].
  rewrite (tidE nat _ _ (dbuild_len (ipin (melt s)))).
  pose proof (idl_nle_leb hmax (hix h) (hix_nle h)) as L1. idl_tidQ L1 EL1. rewrite EL1.
  pose proof (idl_nle_leb hmax O (idl_nle_0 hmax)) as L2. idl_tidQ L2 EL2. rewrite EL2.
  apply idl_tid_qans_val. exact (tid_eq Z _ _ EV).
Qed.

(* ===================================================================== *)
(* 9. 计算演示：异或流收编回归 + 幸福路 + 同洞异值记冲突一次                     *)
(* ===================================================================== *)

(* 二轮击杀实验（席 3 异或流）的 IDL 回归：pass-A 后 rej-B——
   B 无钉（无 pass 判词）→ 欠单如实记缺；B 的差条款「值≠0」对占位 0 相抵 →
   再记一条 REJ——异或流给不出非零差见证，记欠，不织。 *)
Definition sX : list verd := mkVd k1 vpass 0 :: mkVd kb vrej 0 :: nil.

Theorem xor_defused :
  idl_tid weaveout (weave (melt sX))
      (wiou (IOU_NOPIN kb :: IOU_NOPIN kc :: IOU_NOPIN ke :: IOU_NOPIN kr
             :: IOU_REJ kb 0 :: nil)).
Proof.
  apply (tid_eq weaveout _ _). reflexivity.
Qed.

(* 幸福路：六洞全钉 + 一条可满足差条款 ⟹ 织出 *)
Definition sOK : list verd :=
  mkVd k0 vpass 0 :: mkVd k1 vpass 3 :: mkVd kb vpass (-2) :: mkVd kc vpass 7
  :: mkVd ke vpass 1 :: mkVd kr vpass 4 :: mkVd kb vrej 9 :: nil.

Theorem happy_wok : idl_tid bool (weave_b (melt sOK)) true.
Proof.
  apply (tid_eq bool _ true). reflexivity.
Qed.

(* 同洞异值：冲突位 PB ⟹ 记欠不织；冲突清点恰为 1（同洞异值记冲突一次） *)
Definition sC : list verd := mkVd k1 vpass 3 :: mkVd k1 vpass 5 :: nil.

Theorem conflict_once : idl_tid bool (weave_b (melt sC)) false.
Proof.
  apply (tid_eq bool _ false). reflexivity.
Qed.

Theorem conflict_census : idl_tid nat (iconf (melt sC)) 1%nat.
Proof.
  apply (tid_eq nat _ _). reflexivity.
Qed.

(* 织出件装进 Q4 账态后 [内]类全准入（六槽域内零拒答） *)
Theorem wok_qin_admit : forall (s : list verd) (i j : nat),
  idl_nle i (idl_dlen (dbuild (ipin (melt s)))) ->
  idl_nle j (idl_dlen (dbuild (ipin (melt s)))) ->
  idl_tid bool (idl_qadmit (mkCL (dbuild (ipin (melt s))) None acol0) (idl_QIN i j)) true.
Proof.
  intros s i j Hi Hj.
  destruct (idl_qin_correct (dbuild (ipin (melt s))) i j) as [_ Bwd].
  unfold idl_qadmit, idl_qadmitR. cbn [cld clv cla].
  exact (Bwd (pair Hi Hj)).
Qed.
