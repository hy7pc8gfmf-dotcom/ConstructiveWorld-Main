(* ===================================================================== *)
(* UpRecast.v — GRM 再铸链 Coq 落地：use 事件账本 + survive 幸存扫描 +       *)
(*              recast 再铸 + 未桥尾义务（可再入）+ 摩擦计量                 *)
(*                                                                       *)
(* 二轮圆桌 Q3 立项（2 票：席 2/席 3，投票理由：全场最干净结构性抢救 +       *)
(* 首尾咬合）。设计出处：                                                  *)
(*   ROUNDTABLE2.md 席 1 段落（GRM 签名草稿 + v2 终稿）；                   *)
(*   ROUNDTABLE2.md 席 1 实验区【抢救一：WPM → GRM 账本上的再铸链】；        *)
(*   成果存档/圆桌会议/排队席位方案-二轮成果Coq化-20260907.md Q3 条目。       *)
(*                                                                       *)
(* 载体全程 Z/nat/bool 判定层；语句零 Prop（Set/Type 层 tid 恒等型 + nle 序型  *)
(* + pick 双分支判定，Rocq 9.1 sumbool 参数为 Prop 不可载 Type 见件 2 注）；    *)
(* stdlib only；纯构造性。                                                  *)
(*                                                                       *)
(* 五件：                                                                 *)
(*   件 1  use 事件账本（append-only 账本推进 + 逐字段 use 账户单调）         *)
(*   件 2  survive 幸存扫描（长度分割守恒 + 幸存者纯净 + bool 判定全覆盖）     *)
(*   件 3  recast 再铸（普查不增 + 义务不灭 + 总账平衡 + 等级质量守恒）        *)
(*   件 4  未桥尾义务可再入（rebridge 清账再入 + recast∘rebridge 循环咬合     *)
(*         + 任意长再铸链 chain 总账守恒）                                  *)
(*   件 5  摩擦计量（每轮精确差值 +1/+2 + 全链单调 + 循环严格推进）            *)
(*                                                                       *)
(* 定稿决策（原设计未定稿处，按「结构最干净 + 首尾咬合」定稿）：               *)
(*   D1  载体细化：fid=tier=nat、evid=Z（证据强度取 |ev| 的 nat 编码）；       *)
(*       Cert = 普查 census + 未桥义务账 obls + 计量 meter 三分账，           *)
(*       义务账户独立成账（原草稿义务混在普查标记里），首尾咬合更干净。         *)
(*   D2  行内测验语义：passes f ev c := find 普查读出 f 的等级 t，             *)
(*       t <= |ev| 判通过（bool 全判定）；通过档计量 +1 不动普查，             *)
(*       击穿档走 survive 扫描降级再铸（计量 +1+1）。                         *)
(*   D3  击穿粒度：survive 扫描按字段整体过滤，f 的全部条目整体降级，           *)
(*       义务账逐条携带原等级（verbatim 转移）——等级质量守恒因此成立。         *)
(*   D4  再入语义：rebridge c f 把义务账中 f 的全部条目移回普查尾部的，        *)
(*       同一 keepF/hitF 判定面复用于普查与义务两账（一台机器两本账）；        *)
(*       recast∘rebridge 循环严格增摩擦 + 总账守恒，即可无限再入的链。         *)
(*   D5  v2 耦合谱系账的归并机制不在本件（属上游普查结构假设，E1 反例          *)
(*       已证字段独立公理不可依赖）；本件在任意普查上建账，耦合谱系可作为      *)
(*       上游换代挂入，recast 链接口不变——与 Q3 条目「未定稿细节自行定稿」    *)
(*       一致，诚实声明而非降级。                                           *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Open Scope Z_scope.

(* ===================================================================== *)
(* 0. Set 层基建：tid 恒等型 / nle 序型 / 判定存活工具（内联自 UpPLA §0）      *)
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

(* Set 层自然数序型（k < m 编码为 nle (S k) m） *)
Inductive nle (n : nat) : nat -> Set :=
| nle_n : nle n n
| nle_S : forall m : nat, nle n m -> nle n (S m).

Ltac tidE H :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : tid bool X true、H2 : tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

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
    + change (tid bool false true) in H. tidE H. discriminate HE.
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

Lemma nle_SS : forall a b : nat, nle a b -> nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_0 : forall m : nat, nle O m.
Proof.
  induction m as [| m1 IH].
  - apply nle_n.
  - apply nle_S. exact IH.
Qed.

Lemma nle_of_leb : forall b a : nat,
  tid bool (Nat.leb a b) true -> nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply nle_n.
    + change (tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply nle_0.
    + apply nle_SS. exact (IB a1 H).
Qed.

Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

(* nle (S a) (S b) -> nle a b *)
Lemma nle_pred : forall a b : nat, nle (S a) (S b) -> nle a b.
Proof.
  intros a b H. apply nle_of_leb.
  exact (nle_leb (S b) (S a) H).
Qed.

Lemma nle_add_r : forall a b : nat, nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply nle_0.
  - exact (nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- 本件新增基建 ---- *)

Lemma nle_S_diag : forall a : nat, nle a (S a).
Proof.
  induction a as [| a IH].
  - apply nle_0.
  - apply nle_SS. exact IH.
Qed.

Lemma nle_add_r_any : forall a b c : nat, nle a b -> nle (a + c) (b + c).
Proof.
  intros a b c H. induction H as [| m H IH].
  - apply nle_n.
  - replace (Nat.add (S m) c) with (S (Nat.add m c)) by reflexivity.
    apply nle_S. exact IH.
Qed.

Lemma nle_add_l_any : forall a b c : nat, nle b c -> nle (a + b) (a + c).
Proof.
  intros a b c H. induction a as [| a IH].
  - exact H.
  - apply nle_SS. exact IH.
Qed.

(* nat/bool 层 eq -> tid 桥（证明内部收尾用） *)
Lemma tid_nat_eq : forall a b : nat, a = b -> tid nat a b.
Proof.
  intros a b H. rewrite H. apply tid_refl.
Qed.

Lemma tid_bool_eq : forall x y : bool, x = y -> tid bool x y.
Proof.
  intros x y H. rewrite H. apply tid_refl.
Qed.

(* ---- 通用列表算术（自证防 stdlib 改名漂移） ---- *)

Lemma rc_len_app : forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = Nat.add (length l1) (length l2).
Proof.
  intros A l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rc_filter_partition_len : forall (A : Type) (g : A -> bool) (l : list A),
  length l = Nat.add (length (filter g l)) (length (filter (fun x => negb (g x)) l)).
Proof.
  intros A g l. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (g a); simpl; lia.
Qed.

Lemma rc_filter_app : forall (A : Type) (g : A -> bool) (l1 l2 : list A),
  filter g (l1 ++ l2) = filter g l1 ++ filter g l2.
Proof.
  intros A g l1. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - destruct (g a); simpl; rewrite IH; reflexivity.
Qed.

Lemma rc_filter_filter_len : forall (A : Type) (g : A -> bool) (l : list A),
  length (filter g (filter g l)) = length (filter g l).
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - destruct (g a) eqn:Ega.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. rewrite IH. reflexivity.
    + simpl. rewrite ?Ega. simpl. rewrite ?Ega. simpl. exact IH.
Qed.

Lemma rc_existsb_filter_neg : forall (A : Type) (g : A -> bool) (l : list A),
  existsb g (filter (fun x => negb (g x)) l) = false.
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (g a) eqn:Ega.
    + cbn [existsb negb]. exact IH.
    + cbn [existsb negb]. rewrite ?Ega. simpl. exact IH.
Qed.

Lemma rc_existsb_filter_id : forall (A : Type) (g : A -> bool) (l : list A),
  existsb g (filter g l) = existsb g l.
Proof.
  intros A g l. induction l as [| a l IH].
  - reflexivity.
  - change (existsb g (filter g (a :: l)))
      with (existsb g (if g a then a :: filter g l else filter g l)).
    change (existsb g (a :: l)) with (orb (g a) (existsb g l)).
    destruct (g a) eqn:Ega.
    + simpl. rewrite Ega. reflexivity.
    + exact IH.
Qed.

(* ===================================================================== *)
(* 件 1. use 事件账本：append-only 账本 + 逐字段行使账户                      *)
(* ===================================================================== *)

Definition fid : Set := nat.
Definition tier : Set := nat.
Definition evid : Set := Z.

Inductive evt : Set := use : fid -> evid -> evt.

Record meter : Set := mkM { m_ev : nat; m_rc : nat }.

Record Cert : Set := mkC {
  census : list (fid * tier);   (* 幸存普查：字段 × 等级 *)
  obls   : list (fid * tier);   (* 未桥尾义务账：被击穿字段 × 失守等级     *)
  mtr    : meter                (* 摩擦计量：行使计数 + 再铸计数           *)
}.

(* 账本推进：事件只追加，历史永不改写 *)
Definition ledger_step (l : list evt) (e : evt) : list evt := l ++ [e].

(* 字段 f 的行使判定面（账本逐事件的分类 bool） *)
Definition is_use_f (f : fid) (e : evt) : bool :=
  match e with use g _ => Nat.eqb f g end.

(* 字段 f 的 use 行使账户：账本上对该字段行使的次数 *)
Definition use_cnt (f : fid) (l : list evt) : nat :=
  length (filter (is_use_f f) l).

Theorem ledger_len_step : forall (l : list evt) (e : evt),
  tid nat (S (length l)) (length (ledger_step l e)).
Proof.
  intros l e. apply tid_nat_eq. unfold ledger_step. rewrite rc_len_app. simpl. lia.
Qed.

(* 账本推进守恒/单调：use 事件只增不减逐字段账户 *)
Theorem ledger_use_mono : forall (f : fid) (l : list evt) (e : evt),
  nle (use_cnt f l) (use_cnt f (ledger_step l e)).
Proof.
  intros f l. induction l as [| a l IH]; intros e.
  - apply nle_0.
  - destruct a as [g ev]. unfold use_cnt in *. simpl.
    destruct (Nat.eqb f g).
    + apply nle_SS. exact (IH e).
    + exact (IH e).
Qed.

(* ===================================================================== *)
(* 件 2. survive 幸存扫描：最大幸存子证书（字段集过滤）+ bool 判定全覆盖       *)
(* ===================================================================== *)

Definition fidb (f g : fid) : bool := Nat.eqb f g.

(* 幸存判定面：字段不等于被击穿字段则幸存 *)
Definition keepF (f : fid) (p : fid * tier) : bool := negb (fidb f (fst p)).
(* 击穿判定面：字段恰为被击穿字段 *)
Definition hitF (f : fid) (p : fid * tier) : bool := fidb f (fst p).

(* 最大幸存子证书：普查中剔除被击穿字段的全部条目 *)
Definition survive_scan (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (keepF f) l.
(* 被击穿而降级的条目（与幸存扫描互补，同一判定面） *)
Definition pierced (f : fid) (l : list (fid * tier)) : list (fid * tier) :=
  filter (hitF f) l.

(* 字段在册性的 bool 判定（零 Prop 的 In 代用品） *)
Definition occurs (f : fid) (l : list (fid * tier)) : bool :=
  existsb (hitF f) l.

(* 扫描完备性之一：长度分割守恒——幸存 + 击穿 = 全普查，一枚不丢 *)
Theorem scan_partition_len : forall (f : fid) (l : list (fid * tier)),
  tid nat (length l)
           (Nat.add (length (survive_scan f l)) (length (pierced f l))).
Proof.
  intros f l. apply tid_nat_eq. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  exact (rc_filter_partition_len (fid * tier) (hitF f) l).
Qed.

(* 扫描完备性之二：幸存者纯净——幸存子证书不再含被击穿字段 *)
Theorem scan_survivor_pure : forall (f : fid) (l : list (fid * tier)),
  tid bool (occurs f (survive_scan f l)) false.
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, survive_scan.
  exact (rc_existsb_filter_neg (fid * tier) (hitF f) l).
Qed.

(* 扫描完备性之三：判定全覆盖——击穿侧恰捕获全部在册条目 *)
Theorem scan_pierce_capture : forall (f : fid) (l : list (fid * tier)),
  tid bool (occurs f (pierced f l)) (occurs f l).
Proof.
  intros f l. apply tid_bool_eq. unfold occurs, pierced.
  exact (rc_existsb_filter_id (fid * tier) (hitF f) l).
Qed.

(* bool 判定全覆盖：在册性总判定器（Type 排序双分支，零 Prop）。              *)
(* 定稿决策：Rocq 9.1 的 sumbool 参数已改 (A B : Prop)，装不下 tid 的 Type    *)
(* 载荷，故自建 Type 排序双分支载体 pick（判定器语义不变：分支即判定结果）。   *)
Inductive pick (A B : Type) : Type := pick_l : A -> pick A B | pick_r : B -> pick A B.

Theorem occurs_dec : forall (f : fid) (l : list (fid * tier)),
  pick (tid bool (occurs f l) true) (tid bool (occurs f l) false).
Proof.
  intros f l. unfold occurs.
  destruct (existsb (hitF f) l).
  - apply pick_l. apply tid_bool_eq. reflexivity.
  - apply pick_r. apply tid_bool_eq. reflexivity.
Qed.

(* 幸存子证书规模不超原普查 *)
Theorem scan_scan_mono : forall (f : fid) (l : list (fid * tier)),
  nle (length (survive_scan f l)) (length l).
Proof.
  intros f l. pose proof (scan_partition_len f l) as HP. tidE HP.
  rewrite HE. apply nle_add_r.
Qed.

(* 等级质量：普查条目的等级总和 *)
Definition tsum (l : list (fid * tier)) : nat :=
  fold_right (fun p a => Nat.add (snd p) a) O l.

Lemma rc_tsum_app : forall (l1 l2 : list (fid * tier)),
  tsum (l1 ++ l2) = Nat.add (tsum l1) (tsum l2).
Proof.
  intros l1. unfold tsum. induction l1 as [| a l1 IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma rc_tsum_filter_partition : forall (g : fid * tier -> bool)
                                        (l : list (fid * tier)),
  tsum l = Nat.add (tsum (filter g l)) (tsum (filter (fun x => negb (g x)) l)).
Proof.
  intros g l. unfold tsum. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (g a); simpl; lia.
Qed.

(* 扫描完备性之四：等级质量分割守恒——幸存 + 击穿 = 原质量 *)
Lemma rc_tsum_scan : forall (f : fid) (l : list (fid * tier)),
  tsum l = Nat.add (tsum (survive_scan f l)) (tsum (pierced f l)).
Proof.
  intros f l. unfold survive_scan, pierced.
  rewrite Nat.add_comm.
  exact (rc_tsum_filter_partition (hitF f) l).
Qed.

(* ===================================================================== *)
(* 件 3. recast 再铸：行内测验（bool 判定）+ 降级 + 义务转移 + 计量差值        *)
(* ===================================================================== *)

(* 等级读出：普查上 find 出字段 f 的条目，读出其等级 *)
Definition level_at (f : fid) (l : list (fid * tier)) : option tier :=
  match find (hitF f) l with
  | Some p => Some (snd p)
  | None => None
  end.

(* 行内测验（可判定准入）：证据强度 |ev| 不低于字段等级 t 则通过；           *)
(* 无等级在册（已降级/未发行）则不通过。全 bool，零 Prop。                  *)
Definition passes (f : fid) (ev : evid) (c : Cert) : bool :=
  match level_at f (census c) with
  | Some t => Nat.leb t (Z.to_nat (Z.abs ev))
  | None => false
  end.

(* 再铸本体：按测验 bool 分档（recast_b 提出分支，recast 只做 iota 分发，     *)
(* 使全部定理可用 change 一步落入可重写形态）                               *)
Definition recast_b (c : Cert) (f : fid) (ev : evid) (b : bool) : Cert :=
  if b
  then mkC (census c) (obls c) (mkM (S (m_ev (mtr c))) (m_rc (mtr c)))
  else mkC (survive_scan f (census c))
           (obls c ++ pierced f (census c))
           (mkM (S (m_ev (mtr c))) (S (m_rc (mtr c)))).

(* 消费事件驱动的再铸：下游实例化即行使一次行内测验 *)
Definition recast (c : Cert) (e : evt) : Cert :=
  match e with
  | use f ev => recast_b c f ev (passes f ev c)
  end.

(* 总账：普查条目 + 义务条目（再铸链的不变量载体） *)
Definition total_acc (c : Cert) : nat :=
  Nat.add (length (census c)) (length (obls c)).

(* 再铸分档辅助：通过档普查恒等 *)
Theorem recast_pass_census : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) true ->
  tid (list (fid * tier)) (census c) (census (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (tid_refl (list (fid * tier)) (census c)).
Qed.

(* 再铸分档辅助：通过档旧义务全保留（义务不灭半边） *)
Theorem recast_pass_obls : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) true ->
  tid (list (fid * tier)) (obls c) (obls (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. exact (tid_refl (list (fid * tier)) (obls c)).
Qed.

(* 再铸击穿档：普查缩减恰为被击穿条目（义务转移的来源侧） *)
Theorem recast_pierce_partition : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) false ->
  tid nat (length (census c))
           (Nat.add (length (census (recast c (use f ev))))
                    (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [census].
  exact (scan_partition_len f (census c)).
Qed.

(* 再铸击穿档：新义务恰为降级条目（义务转移的去向侧；旧义务消⟹新义务生） *)
Theorem recast_pierce_obls_len : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) false ->
  tid nat (length (obls (recast c (use f ev))))
           (Nat.add (length (obls c)) (length (pierced f (census c)))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. unfold recast_b. cbn [obls].
  apply tid_nat_eq. rewrite rc_len_app. reflexivity.
Qed.

(* 普查单调：再铸永不增发普查条目 *)
Theorem recast_census_mono : forall (c : Cert) (e : evt),
  nle (length (census (recast c e))) (length (census c)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply nle_n.
  - exact (scan_scan_mono f (census c)).
Qed.

(* 义务单调：再铸永不销毁既有义务 *)
Theorem recast_obls_mono : forall (c : Cert) (e : evt),
  nle (length (obls c)) (length (obls (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply nle_n.
  - unfold recast_b. cbn [obls]. rewrite rc_len_app. apply nle_add_r.
Qed.

(* 义务转移封闭性·总账平衡：任意再铸后总账守恒（账户总账平衡） *)
Theorem acc_balance : forall (c : Cert) (e : evt),
  tid nat (total_acc c) (total_acc (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply tid_refl.
  - apply tid_nat_eq. unfold total_acc, recast_b. cbn [census obls].
    rewrite rc_len_app.
    pose proof (scan_partition_len f (census c)) as HP. tidE HP.
    rewrite HE. lia.
Qed.

(* 义务转移封闭性·等级质量守恒：降级 verbatim 转账，质量分毫不差 *)
Theorem tier_balance : forall (c : Cert) (e : evt),
  tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (recast c e))) (tsum (obls (recast c e)))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - apply tid_refl.
  - apply tid_nat_eq. unfold recast_b. cbn [census obls].
    rewrite rc_tsum_app.
    rewrite (rc_tsum_scan f (census c)).
    lia.
Qed.

(* ===================================================================== *)
(* 件 5（先行）. 摩擦计量：精确差值 + 单调                                   *)
(* ===================================================================== *)

(* 摩擦计量总值 = 行使计数 + 再铸计数 *)
Definition friction (c : Cert) : nat := Nat.add (m_ev (mtr c)) (m_rc (mtr c)).

(* 通过档精确差值：恰 +1（行使计数 +1，再铸计数不动） *)
Theorem friction_pass_step : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) true ->
  tid nat (S (friction c)) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply tid_refl.
Qed.

(* 击穿档精确差值：恰 +2（行使 +1、再铸 +1） *)
Theorem friction_pierce_step : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev c) false ->
  tid nat (S (S (friction c))) (friction (recast c (use f ev))).
Proof.
  intros c f ev H.
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  tidE H. rewrite HE. apply tid_nat_eq. unfold friction, recast_b. simpl. lia.
Qed.

(* 摩擦计量单调：任意再铸摩擦不减 *)
Theorem friction_mono : forall (c : Cert) (e : evt),
  nle (friction c) (friction (recast c e)).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c))) (m_rc (mtr c))
             (nle_S_diag (m_ev (mtr c)))).
  - exact (nle_trans (Nat.add (m_ev (mtr c)) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (m_rc (mtr c)))
                     (Nat.add (S (m_ev (mtr c))) (S (m_rc (mtr c))))
                     (nle_add_r_any (m_ev (mtr c)) (S (m_ev (mtr c)))
                        (m_rc (mtr c)) (nle_S_diag (m_ev (mtr c))))
                     (nle_add_l_any (S (m_ev (mtr c))) (m_rc (mtr c))
                        (S (m_rc (mtr c))) (nle_S_diag (m_rc (mtr c))))).
Qed.

(* 行使计数单调 *)
Theorem meter_ev_mono : forall (c : Cert) (e : evt),
  nle (m_ev (mtr c)) (m_ev (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_S_diag (m_ev (mtr c))).
  - exact (nle_S_diag (m_ev (mtr c))).
Qed.

(* 再铸计数单调 *)
Theorem meter_rc_mono : forall (c : Cert) (e : evt),
  nle (m_rc (mtr c)) (m_rc (mtr (recast c e))).
Proof.
  intros c e. destruct e as [f ev].
  change (recast c (use f ev)) with (recast_b c f ev (passes f ev c)).
  destruct (passes f ev c).
  - exact (nle_n (m_rc (mtr c))).
  - exact (nle_S_diag (m_rc (mtr c))).
Qed.

(* ===================================================================== *)
(* 件 4. 未桥尾义务可再入：rebridge 清账再入 + 循环咬合 + 任意长再铸链        *)
(* ===================================================================== *)

(* 再入：把义务账中 f 的全部条目移回普查尾部（同一判定面复用于两本账） *)
Definition rebridge (c : Cert) (f : fid) : Cert :=
  mkC (census c ++ pierced f (obls c)) (survive_scan f (obls c)) (mtr c).

(* 再入守恒之一：总账平衡 *)
Theorem rebridge_balance : forall (c : Cert) (f : fid),
  tid nat (total_acc c) (total_acc (rebridge c f)).
Proof.
  intros c f. apply tid_nat_eq. unfold total_acc, rebridge. cbn [census obls].
  rewrite rc_len_app.
  pose proof (scan_partition_len f (obls c)) as HP. tidE HP.
  rewrite HE. lia.
Qed.

(* 再入守恒之二：等级质量守恒 *)
Theorem rebridge_tier_balance : forall (c : Cert) (f : fid),
  tid nat (Nat.add (tsum (census c)) (tsum (obls c)))
           (Nat.add (tsum (census (rebridge c f))) (tsum (obls (rebridge c f)))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge. cbn [census obls].
  rewrite rc_tsum_app.
  rewrite (rc_tsum_scan f (obls c)).
  lia.
Qed.

(* 再入清账：义务账中 f 的在册性清零（该字段义务全部清偿回普查） *)
Theorem rebridge_clears : forall (c : Cert) (f : fid),
  tid bool (occurs f (obls (rebridge c f))) false.
Proof.
  intros c f. apply tid_bool_eq. unfold rebridge, occurs. cbn [obls].
  unfold survive_scan.
  exact (rc_existsb_filter_neg (fid * tier) (hitF f) (obls c)).
Qed.

(* 义务字段计数：f 在账上的条目数 *)
Definition cnt (f : fid) (l : list (fid * tier)) : nat :=
  length (pierced f l).

(* 再入回补：普查上 f 的条目数 = 原普查条目 + 义务账条目（可再入的记账面） *)
Theorem rebridge_cnt_reentry : forall (c : Cert) (f : fid),
  tid nat (cnt f (census (rebridge c f)))
           (Nat.add (cnt f (census c)) (cnt f (obls c))).
Proof.
  intros c f. apply tid_nat_eq. unfold rebridge, cnt. cbn [census].
  unfold pierced. rewrite rc_filter_app. rewrite rc_len_app.
  rewrite (rc_filter_filter_len (fid * tier) (hitF f) (obls c)).
  reflexivity.
Qed.

(* 首尾咬合·循环总账平衡：rebridge 再入后任意再铸，总账仍守恒——           *)
(* 义务账（尾）回补普查（头），循环可无限再入                              *)
Theorem cycle_balance : forall (c : Cert) (f : fid) (e : evt),
  tid nat (total_acc c) (total_acc (recast (rebridge c f) e)).
Proof.
  intros c f e. apply tid_trans with (y := total_acc (rebridge c f)).
  - apply rebridge_balance.
  - apply acc_balance.
Qed.

(* 首尾咬合·循环严格推进：击穿再铸一轮摩擦精确 +2（链不死锁、单调递增） *)
Theorem cycle_friction_strict : forall (c : Cert) (f : fid) (ev : evid),
  tid bool (passes f ev (rebridge c f)) false ->
  tid nat (S (S (friction c))) (friction (recast (rebridge c f) (use f ev))).
Proof.
  intros c f ev H. exact (friction_pierce_step (rebridge c f) f ev H).
Qed.

(* 再铸链驱动器：n 轮燃料消费事件流（{struct n} 保证结构递归） *)
Fixpoint chain (n : nat) (c : Cert) (es : list evt) {struct n} : Cert :=
  match n with
  | O => c
  | S n' =>
      match es with
      | [] => c
      | e :: rest => chain n' (recast c e) rest
      end
  end.

(* 链守恒：任意长度再铸链总账平衡 *)
Theorem chain_balance : forall (n : nat) (c : Cert) (es : list evt),
  tid nat (total_acc c) (total_acc (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply tid_refl.
  - destruct es as [| e rest].
    + apply tid_refl.
    + apply tid_trans with (y := total_acc (recast c e)).
      * apply acc_balance.
      * apply IH.
Qed.

(* 链单调：任意长度再铸链摩擦不减（计量沿链累计） *)
Theorem chain_friction_mono : forall (n : nat) (c : Cert) (es : list evt),
  nle (friction c) (friction (chain n c es)).
Proof.
  intros n. induction n as [| n IH]; intros c es; simpl.
  - apply nle_n.
  - destruct es as [| e rest].
    + apply nle_n.
    + apply nle_trans with (b := friction (recast c e)).
      * apply friction_mono.
      * apply IH.
Qed.
