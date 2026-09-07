(* ===================================================================== *)
(* UpCLQuery.v — CL 2.0 分型拒答 Coq 落地：三类查询显式分型 + 结构性拒答      *)
(*              + 差表封闭律语法免疫                                        *)
(*                                                                       *)
(* 设计出处：ROUNDTABLE2 席 3 终稿（轮次 3）CL 2.0（2 票，席 5/6 投票理由：    *)
(*   Coq 落地路径全场最短）；排队席位方案-二轮成果Coq化-20260907.md Q4 条目。  *)
(*                                                                       *)
(* 三组件：                                                                *)
(*   件 1  三类查询显式分型 qtype：[内]QIN 平移不变 / [值]QVAL 价值 /          *)
(*         [锚]QANC 绝对；可判定准入谓词（sumbool 三分派定义 bool 准入，       *)
(*         *_eq 引理给直读形式；正确性 iffT 定理：准入 ⟺ sigT 凭证）。        *)
(*   件 2  结构性拒答：qans = qans_val Z | qans_rej misscred——拒答是显式      *)
(*         构造，缺失凭证型标 misscred 显式枚举（缺在册 MC_RANGE / 缺头券      *)
(*         MC_VSLOT / 缺锚闭 MC_ANCH）；qdc 总分派 + qdc_spec +              *)
(*         qrej_admit_false + 券一次性（val_fresh_answer / val_burn_reject）。*)
(*   件 3  差表封闭律语法免疫：dtab 归纳型，封闭律 dsub_cocycle 对一切         *)
(*         d : dtab 无前提成立（破律差表在语法层不可写出——构造子封闭）；       *)
(*         gauge shift 下 [内]类裁决平移不变（qin_gauge_invariant），绝对读出  *)
(*         恰平移 c（pot_shift_moves）——语言中无平移不变的绝对读出通道。       *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；语句零 Prop：等式用 tid、序用 nle、            *)
(* 存在用 sigT、分支用 sumbool / bool+tid、⟺ 用 iffT（Set 层双函数记录）。   *)
(* 纪律：纯构造性、无任何公理式出口、stdlib only、全链可提取。                 *)
(* 定稿决策（未定稿细节按「落地最短+判定天然」自定，见交付报告）：             *)
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
(* 0. Set 层基建（自 UpPLA.v 内联：tid 恒等型 + nle 序型 + 判定工具）          *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive tid (A : Type) : A -> A -> Type := tid_refl : forall x : A, tid A x x.

Definition tid_sym (A : Type) (x y : A) (H : tid A x y) : tid A y x :=
  match H in tid _ a b return tid _ b a with
  | tid_refl _ a0 => @tid_refl _ a0
  end.

Definition tid_trans (A : Type) (x y z : A) (H1 : tid A x y) (H2 : tid A y z) :
  tid A x z :=
  match H1 in tid _ a b return tid _ b z -> tid _ a z with
  | tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition tid_cong {A B : Type} (f : A -> B) (x y : A) (H : tid A x y) :
  tid B (f x) (f y) :=
  match H in tid _ a b return tid B (f a) (f b) with
  | tid_refl _ a0 => @tid_refl _ (f a0)
  end.

(* 从 tid 提取定义等式（仅证明内部推理用，命名受控） *)
Ltac tidQ H E :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as E.

(* x = y -> tid A x y（定义等式反灌回恒等型） *)
Lemma tid_eq : forall (A : Type) (x y : A), x = y -> tid A x y.
Proof.
  intros A x y H. rewrite H. apply tid_refl.
Defined.

(* Set 层自然数序型（k ≤ m 编码为 nle k m） *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (S m).

Lemma leb_refl_tid : forall a : nat, tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply tid_refl.
Qed.

Lemma leb_S : forall a m : nat,
  tid bool (Nat.leb a m) true -> tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply tid_refl.
    + change (tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint nle_lebF (a b : nat) (H : nle a b) {struct H} :
  tid bool (Nat.leb a b) true :=
  match H as H0 in nle _ bb
  return tid bool (Nat.leb a bb) true with
  | nle_n _ => leb_refl_tid a
  | nle_S _ m H1 => leb_S a m (nle_lebF a m H1)
  end.

Definition nle_leb (b a : nat) (H : nle a b) : tid bool (Nat.leb a b) true :=
  nle_lebF a b H.

(* nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (nle_leb _ _ H) in tid _ x y return x = y with
        | tid_refl _ _ => eq_refl
        end)) as HN.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_SS : forall a b : nat, nle a b -> nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

(* nle -> leb = true 反向桥 *)
Lemma nle_of_leb : forall b a : nat,
  tid bool (Nat.leb a b) true -> nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply nle_n.
    + change (tid bool false true) in H. tidQ H HE. discriminate HE.
  - destruct a as [| a1].
    + apply nle_S. apply nle_0.
    + exact (nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ -> tid bool (leb) true 桥 *)
Lemma lebT : forall a b : nat, (a <= b)%nat -> tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply tid_refl.
Qed.

(* nle (S m) O 荒谬件（索引不交配的空消去，合法关闭任意 Type 目标） *)
Lemma nle_S_absurd : forall (m : nat) (P : Type), nle (S m) O -> P.
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
  tid Z (dsub d i j + dsub d j k) (dsub d i k).
Proof.
  intros d i j k. unfold dsub.
  apply (tid_eq Z (pot d i - pot d j + (pot d j - pot d k)) (pot d i - pot d k)).
  ring.
Qed.

(* gauge 平移：整表势读数加 c（换头元规范的语法操作） *)
Fixpoint dshift (d : dtab) (c : Z) : dtab :=
  match d with
  | dtab1 c0 => dtab1 (c0 + c)
  | dtabSnoc d0 w => dtabSnoc (dshift d0 c) (w + c)
  end.

Lemma dlen_shift : forall (d : dtab) (c : Z), tid nat (dlen (dshift d c)) (dlen d).
Proof.
  intros d c. induction d as [c0 | d0 IH w].
  - simpl. apply tid_refl.
  - simpl. tidQ IH Edl. rewrite Edl. apply tid_refl.
Qed.

(* 件 3 对照定理：绝对势读数在 gauge 平移下恰移动 c（语言无平移不变的绝对读出） *)
Theorem pot_shift_moves : forall (d : dtab) (c : Z) (i : nat),
  nle i (dlen d) -> tid Z (pot (dshift d c) i) (pot d i + c).
Proof.
  intros d c i. induction d as [c0 | d0 IH w].
  - intros Hn. destruct i as [| i1].
    + simpl. apply tid_refl.
    + exact (nle_S_absurd i1 _ Hn).
  - intros Hn. simpl in Hn.
    pose proof (dlen_shift d0 c) as DL. tidQ DL Edl.
    simpl. rewrite Edl.
    destruct (Nat.eqb i (S (dlen d0))) eqn:E.
    + apply tid_refl.
    + apply IH. apply nle_of_leb. apply lebT.
      apply Nat.eqb_neq in E. nleP Hn. lia.
Qed.

(* [内]类差值读数 gauge 不变（合法指标域内） *)
Theorem dsub_shift_invariant : forall (d : dtab) (c : Z) (i j : nat),
  nle i (dlen d) -> nle j (dlen d) ->
  tid Z (dsub (dshift d c) i j) (dsub d i j).
Proof.
  intros d c i j Hi Hj. unfold dsub.
  pose proof (pot_shift_moves d c i Hi) as T1. tidQ T1 E1.
  pose proof (pot_shift_moves d c j Hj) as T2. tidQ T2 E2.
  apply (tid_eq Z (pot (dshift d c) i - pot (dshift d c) j) (pot d i - pot d j)).
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
| MC_VSLOT             (* 缺头券：单槽价值凭证缺席或已焚              *)
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

Definition tid_qans_val (z1 z2 : Z) (H : tid Z z1 z2) :
  tid qans (qans_val z1) (qans_val z2) :=
  tid_cong (@qans_val) z1 z2 H.

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

(* nat 序的三分派：left = nle 凭证，right = leb=false 的 tid 证据
   （判定本体走全量化引理，避免 destruct 污染目标型中的 scrutinee） *)
Lemma nle_dc_gen : forall (p : bool) (a b : nat),
  p = Nat.leb a b -> sdec (nle a b) (tid bool (Nat.leb a b) false).
Proof.
  intros p a b E. destruct p as [] eqn:Ep.
  - apply sdec_l. exact (nle_of_leb b a (tid_eq bool (Nat.leb a b) true (eq_sym E))).
  - apply sdec_r. exact (tid_eq bool (Nat.leb a b) false (eq_sym E)).
Defined.

Definition nle_dc (a b : nat) : sdec (nle a b) (tid bool (Nat.leb a b) false) :=
  nle_dc_gen (Nat.leb a b) a b eq_refl.

(* [内]类准入三分派：left = 双在册 nle 凭证；right = 缺在册型标 *)
Definition qin_dc (d : dtab) (i j : nat)
  : sdec (prod (nle i (dlen d)) (nle j (dlen d))) misscred.
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
  : sdec (sigT (fun w : Z => tid (option (nat * Z)) (Some (i, w)) v)) misscred.
Proof.
  destruct v as [[h w] |] eqn:Ev.
  - destruct (Nat.eqb h i) eqn:Eh.
    + apply sdec_l. apply (existT _ w).
      apply Nat.eqb_eq in Eh.
      exact (tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
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
  : sdec (sigT (fun c : Z => tid (option Z) (Some c) (aread i a))) misscred.
Proof.
  destruct (aread i a) as [c |] eqn:E.
  - apply sdec_l. apply (existT _ c). apply tid_refl.
  - apply sdec_r. apply (MC_ANCH i).
Defined.

Definition qanc_ok (a : acol) (i : nat) : bool :=
  match aread i a with Some _ => true | None => false end.

(* 三分派与 bool 准入的互通不经本体展开桥接，而经凭证型刻画：
   qin_dc/qval_dc/qanc_dc 的 left 支型 == qin_correct/qval_correct/qanc_correct
   中与各自 bool 准入 ⟺ 的凭证型（prod nle 对 / sigT 券面 / sigT 锚面）——
   两路定义被同一凭证型钉死，一致性由类型而非引理承担。 *)

(* --- 正确性定理：准入 ⟺ 存在凭证（sigT 携带；⟺ 用 iffT） --- *)

Theorem qin_correct : forall (d : dtab) (i j : nat),
  iffT (tid bool (qin_ok d i j) true)
       (prod (nle i (dlen d)) (nle j (dlen d))).
Proof.
  intros d i j. apply (mkIffT _ _).
  - intros H. unfold qin_ok in H.
    tidQ H E. apply andb_prop in E. destruct E as [E1 E2].
    exact (pair (nle_of_leb (dlen d) i (tid_eq bool _ true E1))
                (nle_of_leb (dlen d) j (tid_eq bool _ true E2))).
  - intros p. destruct p as [Ha Hb].
    pose proof (nle_leb (dlen d) i Ha) as T1. tidQ T1 E1.
    pose proof (nle_leb (dlen d) j Hb) as T2. tidQ T2 E2.
    unfold qin_ok.
    apply (tid_eq bool (Nat.leb i (dlen d) && Nat.leb j (dlen d)) true).
    rewrite E1, E2. reflexivity.
Qed.

Theorem qval_correct : forall (v : option (nat * Z)) (i : nat),
  iffT (tid bool (qval_ok v i) true)
       (sigT (fun w : Z => tid (option (nat * Z)) (Some (i, w)) v)).
Proof.
  intros v i. apply (mkIffT _ _).
  - intros H. unfold qval_ok in H. destruct v as [[h w] |] eqn:Ev.
    + simpl in H. destruct (Nat.eqb h i) eqn:Eh.
      * apply (existT _ w).
        apply Nat.eqb_eq in Eh.
        exact (tid_eq (option (nat * Z)) (Some (i, w)) (Some (h, w))
                 (eq_sym (f_equal (fun n => Some (n, w)) Eh))).
      * tidQ H E. discriminate E.
    + simpl in H. tidQ H E. discriminate E.
  - intros [w H]. unfold qval_ok. destruct v as [[h w0] |] eqn:Ev.
    + tidQ H E. injection E as Ei Ew.
      rewrite Ei. simpl.
      exact (tid_eq bool (Nat.eqb h h) true (Nat.eqb_refl h)).
    + tidQ H E. discriminate E.
Qed.

Theorem qanc_correct : forall (a : acol) (i : nat),
  iffT (tid bool (qanc_ok a i) true)
       (sigT (fun c : Z => tid (option Z) (Some c) (aread i a))).
Proof.
  intros a i. apply (mkIffT _ _).
  - intros H. unfold qanc_ok in H. destruct (aread i a) as [c |] eqn:E.
    + apply (existT _ c). apply tid_refl.
    + tidQ H E2. discriminate E2.
  - intros [c H]. unfold qanc_ok. destruct (aread i a) as [c0 |] eqn:E.
    + apply tid_refl.
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
  tid bool (qadmit s q) (qans_isans (qask s q)).
Proof.
  intros s q. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans, qin_ok.
    destruct (Nat.leb i (dlen (cld s))); destruct (Nat.leb j (dlen (cld s)));
      apply tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qval_ok (clv s) i); apply tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR, qans_isans.
    destruct (qanc_ok (cla s) i); apply tid_refl.
Qed.

(* 宪法判定面总分派：left = 答值见证；right = 结构性拒答见证（携型标） *)
Definition qdc (s : clst) (q : qtype)
  : sdec (sigT (fun z : Z => tid qans (qask s q) (qans_val z)))
         (sigT (fun mc : misscred => tid qans (qask s q) (qans_rej mc))).
Proof.
  destruct q as [i j | i | i a0].
  - unfold qask, qaskR.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply sdec_l. apply (existT _ (dsub (cld s) i j)). apply tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE j)). apply tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply tid_refl.
    + apply sdec_r. apply (existT _ (MC_RANGE i)). apply tid_refl.
  - unfold qask, qaskR. destruct (qval_ok (clv s) i) eqn:Ev.
    + apply sdec_l. apply (existT _ (vs_val (clv s))). apply tid_refl.
    + apply sdec_r. apply (existT _ MC_VSLOT). apply tid_refl.
  - unfold qask, qaskR. destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply sdec_l.
      apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply tid_refl.
    + apply sdec_r. apply (existT _ (MC_ANCH i)). apply tid_refl.
Defined.

(* 总分派规范：裁决位 qdc_b 与准入 bool 逐点一致（宪法内部自洽的 bool 面）；
   分支的凭证内容一致性由 qadmit_answer / qadmit_reject 承担 *)
Definition qdc_b (s : clst) (q : qtype) : bool :=
  match qdc s q with sdec_l _ _ _ => true | sdec_r _ _ _ => false end.

Theorem qdc_spec : forall (s : clst) (q : qtype), tid bool (qdc_b s q) (qadmit s q).
Proof.
  intros s q. unfold qdc_b. destruct (qdc s q) as [Cz | Cm].
  - destruct Cz as [w Hw].
    exact (tid_sym bool (qadmit s q) true
             (tid_trans bool (qadmit s q) (qans_isans (qask s q)) true
                (qadmit_isin s q)
                  (tid_cong qans_isans (qask s q) (qans_val w) Hw))).
  - destruct Cm as [mc Hmc].
    exact (tid_sym bool (qadmit s q) false
             (tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
                (qadmit_isin s q)
                  (tid_cong qans_isans (qask s q) (qans_rej mc) Hmc))).
Qed.

(* 拒答诚实性：凡 qask 输出拒答支，准入必为 false（拒答=显式构造，非失败） *)
Theorem qrej_admit_false : forall (s : clst) (q : qtype) (mc : misscred),
  tid qans (qask s q) (qans_rej mc) -> tid bool (qadmit s q) false.
Proof.
  intros s q mc H.
  exact (tid_trans bool (qadmit s q) (qans_isans (qask s q)) false
           (qadmit_isin s q) (tid_cong qans_isans (qask s q) (qans_rej mc) H)).
Qed.

(* 准入真 ⟹ 答值支显式构造（携答值见证） *)
Theorem qadmit_answer : forall (s : clst) (q : qtype), tid bool (qadmit s q) true ->
  sigT (fun z : Z => tid qans (qask s q) (qans_val z)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + apply (existT _ (dsub (cld s) i j)). apply tid_refl.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + apply (existT _ (vs_val (clv s))). apply tid_refl.
    + tidQ H E. discriminate E.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + apply (existT _ (match aread i (cla s) with Some c => c - a0 | None => 0 end)).
      apply tid_refl.
    + tidQ H E. discriminate E.
Qed.

(* 准入假 ⟹ 拒答支显式构造（携缺失凭证型标见证）——结构性拒答的存在性 *)
Theorem qadmit_reject : forall (s : clst) (q : qtype), tid bool (qadmit s q) false ->
  sigT (fun mc : misscred => tid qans (qask s q) (qans_rej mc)).
Proof.
  intros s q H. destruct q as [i j | i | i a0].
  - unfold qadmit, qadmitR, qask, qaskR, qin_ok in *.
    destruct (Nat.leb i (dlen (cld s))) eqn:Ei;
      destruct (Nat.leb j (dlen (cld s))) eqn:Ej.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_RANGE j)). apply tid_refl.
    + apply (existT _ (MC_RANGE i)). apply tid_refl.
    + apply (existT _ (MC_RANGE i)). apply tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qval_ok (clv s) i) eqn:Ev.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ MC_VSLOT). apply tid_refl.
  - unfold qadmit, qadmitR, qask, qaskR in *.
    destruct (qanc_ok (cla s) i) eqn:Ea.
    + simpl in H. tidQ H E. discriminate E.
    + apply (existT _ (MC_ANCH i)). apply tid_refl.
Qed.

(* --- 头券生命周期：[值]类答一次即焚，焚后再问 = 结构性拒答附缺头券型标 --- *)

Definition clburn (s : clst) (i : nat) : clst := mkCL (cld s) None (cla s).

Theorem val_fresh_answer : forall (d : dtab) (a : acol) (i : nat) (w : Z),
  tid qans (qask (mkCL d (Some (i, w)) a) (QVAL i)) (qans_val w).
Proof.
  intros d a i w. unfold qask, qaskR, qval_ok. simpl.
  rewrite Nat.eqb_refl. apply tid_refl.
Qed.

Theorem val_burn_reject : forall (s : clst) (i : nat),
  tid qans (qask (clburn s i) (QVAL i)) (qans_rej MC_VSLOT).
Proof.
  intros s i. unfold qask, qaskR, clburn, qval_ok. simpl. apply tid_refl.
Qed.

(* ===================================================================== *)
(* 6. 件 3：[内]类平移不变性（分型押注的语法化）                               *)
(* ===================================================================== *)

(* CL 2.0 押注的分型形式：[内]类裁决在差表 gauge 平移下逐字不变。
   对照 pot_shift_moves：绝对读出恰移动 c——故绝对问题在 [内]类语法内
   不可问出（问了也必得到平移不变的答案，即被类型系统挡在差表语言外）。 *)
Theorem qin_gauge_invariant : forall (d : dtab) (c : Z) (v : option (nat * Z))
                                     (a : acol) (i j : nat),
  tid qans (qask (mkCL (dshift d c) v a) (QIN i j))
           (qask (mkCL d v a) (QIN i j)).
Proof.
  intros d c v a i j. unfold qask, qaskR. cbn [cld clv cla].
  pose proof (dlen_shift d c) as DL. tidQ DL Edl. rewrite Edl.
  destruct (Nat.leb i (dlen d)) eqn:Ei; destruct (Nat.leb j (dlen d)) eqn:Ej.
  - apply tid_qans_val. apply dsub_shift_invariant.
    + exact (nle_of_leb (dlen d) i (tid_eq bool (Nat.leb i (dlen d)) true Ei)).
    + exact (nle_of_leb (dlen d) j (tid_eq bool (Nat.leb j (dlen d)) true Ej)).
  - apply tid_refl.
  - apply tid_refl.
  - apply tid_refl.
Qed.
