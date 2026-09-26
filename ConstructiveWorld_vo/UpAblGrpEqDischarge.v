(* ============================================================ *)
(* UpAblGrpEqDischarge.v —— 族A grp_eq_dec 前提的具体载体实例化通路示范件 *)
(* 前提：S15_TailFEPUp.v 的 grp_eq_dec（Variable grp_eq_dec : forall      *)
(*   i j : Group, Or (Id i j) (Not (Id i j))，族A·可判等）。          *)
(* 世界：Group := bool 二元枚举型；R := nat 极小 Set 层载体。          *)
(* 依赖清单：零本库依赖（§0 S01 同型极小基座自建零依赖；Stdlib Extraction 直引）。 *)
(* 零承认件：本件纯构造，无任何承认式底层，全部 Qed，可提取。          *)
(* 范围注记：抽象 Group 上的 grp_eq_dec 一般构造仍属未竟（本件不改变   *)
(*   此状况）；本件为载体相对性实证——可判等实例依托 bool 载体的        *)
(*   构造性区分，仿 S17 keep_dec 实例先例单列。                        *)
(* 参照出口（只读）：S15_TailFEPUp.v Module UpExtras219 之             *)
(*   counter_ex_indicator_sum_two / counter_ex_reward_sum_two_c 双副本 *)
(*   枚举世界为反例构造；本件为单副本 bool 枚举的正向实例化构造。      *)
(* 与世界装配件（UpAblGrpEqDecWorld.v）各自独立、互不依赖。            *)
(* 编译配方：9.1 直调（coqc 无 -Q），cpu_guard 包裹，-o 输出临时目录。 *)
(* ============================================================ *)

(* ================= §0 S01 同型极小基座（自建零依赖） ================= *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition Or (A B : Set) : Set := A + B.
Definition Not (A : Set) : Set := A -> Empty_set.

Definition id_sym {A : Set} {x y : A} (p : Id x y) : Id y x :=
  match p with
  | id_refl => id_refl
  end.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

Definition id_cong {A B : Set} (f : A -> B) {x y : A} (p : Id x y) : Id (f x) (f y) :=
  match p with
  | id_refl => id_refl
  end.

Definition id_cong2 {A B C : Set} (f : A -> B -> C) {x x' : A} {y y' : B}
                    (p : Id x x') (q : Id y y') : Id (f x y) (f x' y') :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* 构造性 list 成员关系（Set 层，S01 同型） *)
Inductive InT {A : Set} (x : A) : list A -> Set :=
| InT_here : forall l, InT x (x :: l)
| InT_next : forall y l, InT x l -> InT x (y :: l).

Arguments InT_here {A} x l.
Arguments InT_next {A} x y l H.

Definition not_InT {A : Set} (x : A) (l : list A) : Set :=
  InT x l -> Empty_set.

(* 成员关系 cons 头尾二分（依赖消去回送形，替代反转策略） *)
Lemma InT_cons_cases : forall (A : Set) (j a : A) (rest : list A),
  InT j (a :: rest) -> Or (Id j a) (InT j rest).
Proof.
  intros A j a rest Hin.
  refine
    (match Hin as Hin0 in (InT _ l0)
           return (match l0 with
                   | nil => unit
                   | cons b rest0 => Or (Id j b) (InT j rest0)
                   end)
     with
     | InT_here _ rest0 => @inl _ _ id_refl
     | InT_next _ b rest0 Hin2 => @inr _ _ Hin2
     end).
Qed.

(* ================= §1 nat 载体 R 侧极小算术（S01 同型名） ================= *)

Definition zero : nat := O.
Definition one : nat := Datatypes.S O.

Fixpoint rplus (a b : nat) : nat :=
  match a with
  | O => b
  | Datatypes.S a' => Datatypes.S (rplus a' b)
  end.

Lemma plus_zero : forall b : nat, Id (rplus b zero) b.
Proof.
  intro b. induction b as [| b IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_S_swap : forall a b : nat,
  Id (rplus a (Datatypes.S b)) (Datatypes.S (rplus a b)).
Proof.
  intro a. intro b. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_comm : forall a b : nat, Id (rplus a b) (rplus b a).
Proof.
  intro a. intro b. induction a as [| a IH].
  - cbn [rplus]. apply (id_sym (plus_zero b)).
  - cbn [rplus]. apply (id_trans (id_cong (fun n : nat => Datatypes.S n) IH)).
    apply (id_sym (plus_S_swap b a)).
Qed.

Lemma plus_assoc : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus (rplus a b) c).
Proof.
  intros a b c. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

(* Set 层序（自建，禁 sig 形）：ltT a b := leT (S a) b *)
Fixpoint leT (a b : nat) : Set :=
  match a with
  | O => unit
  | Datatypes.S a' =>
      match b with
      | O => Empty_set
      | Datatypes.S b' => leT a' b'
      end
  end.

Definition ltT (a b : nat) : Set := leT (Datatypes.S a) b.

(* nat 到载体的嵌入（S15:1430 同型） *)
Fixpoint nat_to_R_g (k : nat) : nat :=
  match k with
  | O => zero
  | Datatypes.S m => rplus one (nat_to_R_g m)
  end.

Lemma nat_to_R_g_pos : forall k : nat, ltT zero (nat_to_R_g (Datatypes.S k)).
Proof.
  intro k. exact tt.
Qed.

(* ================= §2 bool 二元枚举世界（前提逐项供给） ================= *)

(* 世界承载体：Group := bool *)
(* 前提 grp_eq_dec 的实例化核心：bool 判定到 @inl/@inr 依赖消去 *)
Lemma btt_ne_bff : Not (Id true false).
Proof.
  intro h. exact (match h with end).
Qed.

Lemma bff_ne_btt : Not (Id false true).
Proof.
  intro h. exact (match h with end).
Qed.

Definition bg_grp_eq_dec : forall i j : bool, Or (Id i j) (Not (Id i j)) :=
  fun i j =>
    match i as x return (forall j0 : bool, Or (Id x j0) (Not (Id x j0))) with
    | true =>
        fun j0 =>
          match j0 as y return (Or (Id true y) (Not (Id true y))) with
          | true => @inl (Id true true) (Not (Id true true)) id_refl
          | false => @inr (Id true false) (Not (Id true false)) btt_ne_bff
          end
    | false =>
        fun j0 =>
          match j0 as y return (Or (Id false y) (Not (Id false y))) with
          | true => @inr (Id false true) (Not (Id false true)) bff_ne_btt
          | false => @inl (Id false false) (Not (Id false false)) id_refl
          end
    end j.

(* 伴生前提照 S15:1408-1419 实形逐项供给 *)
Definition bg_enum : list bool := true :: false :: nil.

Definition bg_cover : forall i : bool, InT i bg_enum :=
  fun i =>
    match i as x return (InT x (true :: false :: nil)) with
    | true => InT_here true (false :: nil)
    | false => InT_next false true (false :: nil) (InT_here false nil)
    end.

(* 数据位（直接给出，照 S17 常零函数先例）：reward_group := 常零 *)
Definition bg_reward : bool -> nat := fun _ : bool => zero.

(* 组大小正性伴生（G := nat_to_R_g (length enum)，G_pos 前提） *)
Definition bg_G : nat := nat_to_R_g (length bg_enum).
Definition bg_G_pos : ltT zero bg_G := tt.

(* Set 层无重复谓词（S15:1662 同型，载体泛型） *)
Fixpoint nodup_g {A : Set} (l : list A) : Set :=
  match l with
  | nil => unit
  | cons x t => prod (not_InT x t) (nodup_g t)
  end.

Definition bg_nodup_enum : nodup_g bg_enum :=
  @pair (not_InT true (false :: nil)) (nodup_g (false :: nil))
    (fun Hin : InT true (false :: nil) =>
       match Hin with
       | InT_next _ false nil Hin2 => match Hin2 with end
       end)
    (@pair (not_InT false nil) unit
       (fun Hin : InT false nil => match Hin with end) tt).

(* ================= §3 GRPO 枚举节计数器（grp_eq_dec 实例驱动） ================= *)

(* 组求和（列表 fold，载体 Id 层；S15:1448 同型，载体泛型） *)
Fixpoint list_sum_g {A : Set} (f : A -> nat) (l : list A) : nat :=
  match l with
  | nil => zero
  | cons i rest => rplus (f i) (list_sum_g f rest)
  end.

Lemma list_sum_g_zero_fn : forall (A : Set) (f : A -> nat) (l : list A),
  (forall i : A, InT i l -> Id (f i) zero) ->
  Id (list_sum_g f l) zero.
Proof.
  intros A f l H. induction l as [| x rest IH].
  - apply id_refl.
  - apply (id_trans (id_cong2 rplus (H x (InT_here x rest))
                                (id_refl : Id (list_sum_g f rest) (list_sum_g f rest)))).
    apply (id_trans (plus_comm zero (list_sum_g f rest))).
    apply (id_trans (plus_zero (list_sum_g f rest))).
    exact (IH (fun i : A => fun Hin : InT i rest => H i (InT_next i x rest Hin))).
Qed.

(* 计数器（实例 bg_grp_eq_dec 驱动；S15:1462 同型） *)
Fixpoint count_g (j : bool) (l : list bool) : nat :=
  match l with
  | nil => O
  | cons x rest =>
      match bg_grp_eq_dec x j with
      | inl _ => Datatypes.S (count_g j rest)
      | inr _ => count_g j rest
      end
  end.

Fixpoint removeT_g (j : bool) (l : list bool) : list bool :=
  match l with
  | nil => nil
  | cons x rest =>
      match bg_grp_eq_dec x j with
      | inl _ => removeT_g j rest
      | inr _ => x :: removeT_g j rest
      end
  end.

Lemma InT_transport : forall (x y : bool) (l : list bool),
  Id x y -> InT x l -> InT y l.
Proof.
  intros x y l H Hin. destruct H. exact Hin.
Qed.

Lemma not_InT_count_zero : forall (j : bool) (l : list bool),
  not_InT j l -> @Id nat (count_g j l) O.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hn.
  - apply id_refl.
  - cbn [count_g]. destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + exact (match Hn (InT_transport x j (x :: rest) Hxj (InT_here x rest)) with end).
    + exact (IH (fun Hin : InT j rest => Hn (InT_next j x rest Hin))).
Qed.

(* 头元素 ≠ j ⟹ 成员关系在尾部（S15:1654 同型，经 InT_cons_cases） *)
Lemma InT_tail_of_neq : forall (j a : bool) (rest : list bool),
  Not (Id a j) -> InT j (a :: rest) -> InT j rest.
Proof.
  intros j a rest Hne Hin.
  destruct (InT_cons_cases bool j a rest Hin) as [Hja | Hrest].
  - exact (match Hne (id_sym Hja) with end).
  - exact Hrest.
Qed.

Lemma count_zero_remove_id : forall (j : bool) (l : list bool),
  @Id nat (count_g j l) O -> @Id (list bool) (removeT_g j l) l.
Proof.
  intros j l. induction l as [| x rest IH]; intro Hc.
  - apply id_refl.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + inversion Hc.
    + apply (id_cong (fun l0 : list bool => cons x l0)). exact (IH Hc).
Qed.

Lemma remove_notin_aux : forall (j x : bool) (l : list bool),
  InT x (removeT_g j l) -> Not (Id x j).
Proof.
  intros j x l. induction l as [| y rest IH]; intro Hin.
  - exact (match Hin with end).
  - cbn [removeT_g] in Hin.
    destruct (bg_grp_eq_dec y j) as [Hyj | Hnyj].
    + exact (IH Hin).
    + destruct (InT_cons_cases bool x y (removeT_g j rest) Hin) as [Hxy | Hrest].
      * exact (fun hxj : Id x j => Hnyj (id_trans (id_sym Hxy) hxj)).
      * exact (IH Hrest).
Qed.

(* 恰计一次的拆分：count == 1 ⟹ Σ l f == f j + Σ (removeT_g j l) f *)
Lemma split_count_one_id : forall (f : bool -> nat) (j : bool) (l : list bool),
  @Id nat (count_g j l) (Datatypes.S O) ->
  Id (list_sum_g f l) (rplus (f j) (list_sum_g f (removeT_g j l))).
Proof.
  intros f j l. induction l as [| x rest IH]; intro Hc.
  - inversion Hc.
  - cbn [count_g] in Hc. cbn [removeT_g].
    destruct (bg_grp_eq_dec x j) as [Hxj | Hnxj].
    + assert (Hc0 : @Id nat (count_g j rest) O).
      { exact (id_cong Nat.pred Hc). }
      assert (Hrid : @Id (list bool) (removeT_g j rest) rest)
        by exact (count_zero_remove_id j rest Hc0).
      apply (id_trans (id_cong2 rplus (id_cong f Hxj)
                                     (id_refl : Id (list_sum_g f rest)
                                                   (list_sum_g f rest)))).
      apply (id_cong2 rplus (id_refl : Id (f j) (f j))
                           (id_cong (fun l0 : list bool => list_sum_g f l0)
                                    (id_sym Hrid))).
    + apply (id_trans (id_cong2 rplus (id_refl : Id (f x) (f x)) (IH Hc))).
      apply (id_trans (plus_assoc (f x) (f j) (list_sum_g f (removeT_g j rest)))).
      apply (id_trans (id_cong2 rplus (plus_comm (f x) (f j))
                                     (id_refl : Id (list_sum_g f (removeT_g j rest))
                                                   (list_sum_g f (removeT_g j rest))))).
      apply (id_sym (plus_assoc (f j) (f x) (list_sum_g f (removeT_g j rest)))).
Qed.

(* 恰计一次（B1，S15:1672 同型）：覆盖 + 无重复 ⟹ 每元素恰计一次 *)
Theorem grpo_count_one : forall (l : list bool) (Hnd : nodup_g l)
    (j : bool), InT j l -> @Id nat (count_g j l) (Datatypes.S O).
Proof.
  intros l Hnd. induction l as [| a rest IH]; intros j Hin.
  - exact (match Hin with end).
  - destruct Hnd as [Hnhead Hndrest].
    cbn [count_g]. destruct (bg_grp_eq_dec a j) as [Haj | Hanj].
    + apply (id_cong (fun n : nat => Datatypes.S n)).
      apply (not_InT_count_zero j rest
               (fun Hin : InT j rest =>
                  Hnhead (InT_transport j a rest (id_sym Haj) Hin))).
    + exact (IH Hndrest j (InT_tail_of_neq j a rest Hanj Hin)).
Qed.

(* ================= §4 主件——可判等前提的具体载体实例化通路证书 ================= *)

(* 照 S17 keep_dec 实例证书体例：前提语句逐字入证 + 实例供给 + 使用位实例化。 *)

(* ① 前提语句逐字（S15:1419 形，载体 bool）：Set 层语句 *)
Definition gqd_slot_statement : Set :=
  forall i j : bool, Or (Id i j) (Not (Id i j)).

(* ② 实例（bool 判定到 @inl/@inr 依赖消去，见 §2）：
      gqd_slot_statement 的供给项 = bg_grp_eq_dec *)

(* ③ 主件证书：可判等前提的具体载体实例化通路
      S15:1419 前提经 bg_grp_eq_dec 实例化 ⟹ GRPO 枚举节 B1（每元素恰计一次）
      在世界枚举 bg_enum 上成立。 *)
Theorem gqd_discharge_certificate :
  forall (j : bool), InT j bg_enum ->
    @Id nat (count_g j bg_enum) (Datatypes.S O).
Proof.
  exact (fun j Hin => grpo_count_one bg_enum bg_nodup_enum j Hin).
Qed.

(* ④ 使用位实例化示范：GRPO 枚举节 B2 indicator 求和恒等式（S15:1690 同型）
      —— Σ_{i∈enum} indicator(i) == 1，indicator 由实例 bg_grp_eq_dec 逐位分派。 *)
Theorem gqd_grpo_indicator_sum_one : forall (j : bool),
  InT j bg_enum ->
  Id (list_sum_g (fun i : bool => match bg_grp_eq_dec i j with
                                  | inl _ => one
                                  | inr _ => zero
                                  end) bg_enum) one.
Proof.
  intros j Hin.
  assert (Hc1 : @Id nat (count_g j bg_enum) (Datatypes.S O))
    by exact (grpo_count_one bg_enum bg_nodup_enum j Hin).
  assert (Hsplit := split_count_one_id
                      (fun i : bool => match bg_grp_eq_dec i j with
                                       | inl _ => one
                                       | inr _ => zero
                                       end) j bg_enum Hc1).
  assert (Hfj : Id (match bg_grp_eq_dec j j with
                    | inl _ => one
                    | inr _ => zero
                    end) one).
  { destruct (bg_grp_eq_dec j j) as [Hjj | Hjj].
    - apply id_refl.
    - exact (match Hjj (id_refl : Id j j) with end). }
  assert (Hrest : Id (list_sum_g (fun i : bool => match bg_grp_eq_dec i j with
                                                  | inl _ => one
                                                  | inr _ => zero
                                                  end)
                             (removeT_g j bg_enum)) zero).
  { apply list_sum_g_zero_fn.
    intro i. intro HinR.
    assert (Hne : Not (Id i j)) by exact (remove_notin_aux j i bg_enum HinR).
    destruct (bg_grp_eq_dec i j) as [Hxj | Hnxj].
    - exact (match Hne Hxj with end).
    - apply id_refl. }
  apply (id_trans Hsplit).
  apply (id_trans (id_cong2 rplus Hfj Hrest)).
  apply (plus_zero one).
Qed.

(* ⑤ 提取面对照：判定核（bg_grp_eq_dec 的计算内容投影，纯 bool 构造）
      与核↔前提实例化正确性证书（提取面 Obj.magic=0 的依据）。 *)
Definition bg_dec_core (i j : bool) : bool :=
  match i with
  | true =>
      match j with
      | true => true
      | false => false
      end
  | false =>
      match j with
      | true => false
      | false => true
      end
  end.

Lemma bg_grp_eq_dec_core_correct : forall i j : bool,
  match bg_grp_eq_dec i j with
  | inl _ => Id (bg_dec_core i j) true
  | inr _ => Id (bg_dec_core i j) false
  end.
Proof.
  intros i j.
  (* 分情形：bool 载体四支判定——inl 支判定核 bg_dec_core 归约为 true，inr 支归约为
     false，逐支以 Id 自反见证 @id_refl 连显式右端项收束。 *)
  destruct i; destruct j; cbn [bg_grp_eq_dec bg_dec_core].
  - exact (@id_refl _ true).
  - exact (@id_refl _ false).
  - exact (@id_refl _ false).
  - exact (@id_refl _ true).
Qed.

(* 该位公理依赖核验（应全为 Closed） *)
Print Assumptions bg_grp_eq_dec.
Print Assumptions grpo_count_one.
Print Assumptions gqd_discharge_certificate.
Print Assumptions gqd_grpo_indicator_sum_one.
Print Assumptions bg_grp_eq_dec_core_correct.

(* 提取面：判定核可执行性（Separate Extraction 单命令；
   提取闭包=纯 bool 构造，Obj.magic=0 核验。实例 bg_grp_eq_dec 全式与
   计数器属 Set 层证书面：其 Not 支反证消去为证明内容，提取必擦除为
   Obj.magic，故不参与本提取件。） *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_y6_grpdis_ex".
Separate Extraction bg_dec_core.
