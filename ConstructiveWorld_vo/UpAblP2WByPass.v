(* ==========================================================================)
   UpAblP2WByPass.v — 两判定接口（token_eq_dec/keep_dec 语句形）的 bool 具体载体实例件
   使命: 装配 bool 二元 Token/State 世界，供给两判定接口实例与伴生前件组，汇总为泛用封装证书 p2wb_pack，并把代表结论实例化（质量守恒恒等式复现与头位保留见证生成）；尾部含 W_dec 参数位的 Set 重述位。
   依赖: 零本库依赖（自建极小基座）；仅 Stdlib List、Extraction。
   对标: stdlib 的 bool_eq_dec 类具体判定实例与 sigT 见证形判定封装。
   构造性: Set 层承载，零承认词面、零经典逻辑；重述位见证形可提取；假设审计件尾全 Closed。
   编译配方: Rocq 9.1 直调 coqc，cpu_guard 包裹；验证编译经 -o 写临时目录，树内 .vo 不重写。
   ========================================================================== *)

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

(* ################ 第 1 部：nat 载体极小算术 ################################# *)

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

(* 右结合先行形（下游使用链锁定方向） *)
Lemma plus_assoc : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus (rplus a b) c).
Proof.
  intros a b c. induction a as [| a IH].
  - apply id_refl.
  - cbn [rplus]. apply (id_cong (fun n : nat => Datatypes.S n)). exact IH.
Qed.

Lemma plus_swap : forall a b c : nat,
  Id (rplus a (rplus b c)) (rplus b (rplus a c)).
Proof.
  intros a b c.
  exact (id_trans (plus_assoc a b c)                  (id_trans (id_cong2 rplus (plus_comm a b) (id_refl : Id c c))                            (id_sym (plus_assoc b a c)))).
Qed.

(* ################ 第 2 部：bool 二元世界与两判定接口实例 #################### *)

(* ---- 族A 判定核支件：bool 构造子冲突的空匹配消解 ---- *)

Lemma p2wb_true_ne_false : Not (Id true false).
Proof. intro h. exact (match h with end). Qed.

Lemma p2wb_false_ne_true : Not (Id false true).
Proof. intro h. exact (match h with end). Qed.

(* 族A 判定接口实例：S06 同款语句形（载体 bool），bool 判定经
   @inl/@inr 依赖消去，四支逐支构造性见证（非经典排除律）。 *)
Definition p2wb_token_eq_dec : forall a b : bool, Or (Id a b) (Not (Id a b)) :=
  fun a b =>
    match a as x return (Or (Id x b) (Not (Id x b))) with
    | true =>
        match b as y return (Or (Id true y) (Not (Id true y))) with
        | true => @inl (Id true true) (Not (Id true true)) id_refl
        | false => @inr (Id true false) (Not (Id true false)) p2wb_true_ne_false
        end
    | false =>
        match b as y return (Or (Id false y) (Not (Id false y))) with
        | true => @inr (Id false true) (Not (Id false true)) p2wb_false_ne_true
        | false => @inl (Id false false) (Not (Id false false)) id_refl
        end
    end.

(* ---- 族B 判定接口实例其一：常值形（keep 取常 unit，左支恒真） ---- *)

Definition p2wb_keep : bool -> Set := fun _ : bool => unit.

Definition p2wb_keep_dec : forall s : bool, Or (p2wb_keep s) (Not (p2wb_keep s)) :=
  fun _ : bool => @inl unit (Not unit) tt.

(* ---- 族B 判定接口实例其二：择留形（true 留 false 逐，两支俱非平凡） ---- *)

Definition p2wb_keep_sel : bool -> Set :=
  fun s => match s with
           | true => unit
           | false => Empty_set
           end.

Definition p2wb_keep_dec_sel : forall s : bool,
  Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s)) :=
  fun s =>
    match s as x return (Or (p2wb_keep_sel x) (Not (p2wb_keep_sel x))) with
    | true => @inl unit (Not unit) tt
    | false => @inr (Empty_set) (Not (Empty_set)) (fun h => match h with end)
    end.

(* ---- 伴生前件组（对应 S06 vocab 组与 K/S_enum 组） ---- *)

Definition p2wb_vocab : list bool := cons true (cons false nil).

(* vocab_nonempty 位：表构造子冲突的空匹配消解（索引取字面
   构造子形；与 p2wb_vocab 可转换） *)
Definition p2wb_vocab_nonempty : Not (Id (cons true (cons false nil)) nil) :=
  fun h => match h with end.

(* S_finite_cover 位：覆盖见证 *)
Definition p2wb_S_enum : list bool := cons true (cons false nil).

Definition p2wb_S_finite_cover : forall s : bool, InT s p2wb_S_enum :=
  fun s =>
    match s as x return (InT x (cons true (cons false nil))) with
    | true => InT_here true (cons false nil)
    | false => InT_next false true (cons false nil) (InT_here false nil)
    end.

(* ################ 第 3 部：枚举求和（SumOver 的有限世界实现面） ############# *)

Fixpoint p2wb_sum (f : bool -> nat) (l : list bool) : nat :=
  match l with
  | nil => zero
  | cons x rest => rplus (f x) (p2wb_sum f rest)
  end.

Lemma p2wb_sum_ext : forall f g l,
  (forall x, InT x l -> Id (f x) (g x)) -> Id (p2wb_sum f l) (p2wb_sum g l).
Proof.
  intros f g l H. induction l as [| x rest IH].
  - apply id_refl.
  - cbn [p2wb_sum].
    exact (id_cong2 rplus (H x (InT_here x rest))
                          (IH (fun i => fun Hi => H i (InT_next i x rest Hi)))).
Qed.

Lemma p2wb_sum_add : forall f g l,
  Id (p2wb_sum (fun x => rplus (f x) (g x)) l)
     (rplus (p2wb_sum f l) (p2wb_sum g l)).
Proof.
  intros f g l. induction l as [| x rest IH].
  - apply id_refl.
  - cbn [p2wb_sum].
    exact (id_trans (id_cong (fun t => rplus (rplus (f x) (g x)) t) IH)
                    (id_trans (id_sym (plus_assoc (f x) (g x)
                                                  (rplus (p2wb_sum f rest) (p2wb_sum g rest))))
                              (id_trans (id_cong (fun t => rplus (f x) t)
                                                 (plus_swap (g x) (p2wb_sum f rest) (p2wb_sum g rest)))
                                        (plus_assoc (f x) (p2wb_sum f rest)
                                                    (rplus (g x) (p2wb_sum g rest)))))).
Qed.

(* ################ 第 4 部：族B 实例化——KV 守恒结论逐式复现 ################# *)
(* 源文件：S06 tail_mass／evicted_partition／Z_thermo 与                    *)
(*   tail_plus_kept_full（Id (plus tail_mass evicted_partition)           *)
(*   Z_thermo）；实数轴取 nat 极小载体（实层判定面不在本件范围）。         *)

Definition p2wb_bfactor : bool -> nat :=
  fun s => match s with
           | true => rplus one one
           | false => one
           end.

Definition p2wb_tail_mass (kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s))) : nat :=
  p2wb_sum (fun s => match kd s with
                     | inl _ => zero
                     | inr _ => p2wb_bfactor s
                     end) p2wb_S_enum.

Definition p2wb_evicted_partition (kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s))) : nat :=
  p2wb_sum (fun s => match kd s with
                     | inl _ => p2wb_bfactor s
                     | inr _ => zero
                     end) p2wb_S_enum.

Definition p2wb_Z_thermo : nat := p2wb_sum p2wb_bfactor p2wb_S_enum.

(* 守恒恒等式复现（逐态配对＋p2wb_sum_add＋p2wb_sum_ext） *)
Theorem p2wb_tail_plus_kept_full :
  forall kd : forall s : bool, Or (p2wb_keep_sel s) (Not (p2wb_keep_sel s)),
    Id (rplus (p2wb_tail_mass kd) (p2wb_evicted_partition kd)) p2wb_Z_thermo.
Proof.
  intro kd.
  assert (Hpt : forall s : bool,
             Id (rplus (match kd s with
                        | inl _ => zero
                        | inr _ => p2wb_bfactor s
                        end)
                       (match kd s with
                        | inl _ => p2wb_bfactor s
                        | inr _ => zero
                        end))
                (p2wb_bfactor s)).
  { intro s. destruct (kd s) as [Hk | Hnk].
    - apply id_refl.
    - exact (plus_zero (p2wb_bfactor s)). }
  apply (id_trans (id_sym (p2wb_sum_add
                            (fun s => match kd s with
                                      | inl _ => zero
                                      | inr _ => p2wb_bfactor s
                                      end)
                            (fun s => match kd s with
                                      | inl _ => p2wb_bfactor s
                                      | inr _ => zero
                                      end)
                            p2wb_S_enum))).
  exact (p2wb_sum_ext
           (fun s => rplus (match kd s with
                            | inl _ => zero
                            | inr _ => p2wb_bfactor s
                            end)
                           (match kd s with
                            | inl _ => p2wb_bfactor s
                            | inr _ => zero
                            end))
           p2wb_bfactor p2wb_S_enum (fun s => fun _ => Hpt s)).
Qed.

(* 判定接口经择留实例消去：守恒结论以 p2wb_keep_dec_sel 实例化 *)
Theorem p2wb_tail_plus_kept_full_sel :
  Id (rplus (p2wb_tail_mass p2wb_keep_dec_sel) (p2wb_evicted_partition p2wb_keep_dec_sel))
     p2wb_Z_thermo.
Proof. exact (p2wb_tail_plus_kept_full p2wb_keep_dec_sel). Qed.

(* 实例消去的计算面：择留世界上尾质量＝1、保留质量＝2（全定义约简） *)
Theorem p2wb_sel_tail_mass_one : Id (p2wb_tail_mass p2wb_keep_dec_sel) one.
Proof. exact (@id_refl _ one). Qed.

Theorem p2wb_sel_partition_two : Id (p2wb_evicted_partition p2wb_keep_dec_sel) (rplus one one).
Proof. exact (@id_refl _ (rplus one one)). Qed.

(* ################ 第 5 部：族A 实例化——TopP 保留判定逐式复现 ############### *)
(* 源文件：S06 top_p_member（token_eq_dec x w 逐位分派，inl 支出 unit       *)
(*   元素）→ top_p_keep。阈值判定轴（抽象序可判位，族A 与 LPO 邻接，      *)
(*   不在本件范围）以 W/W_dec 参量全称化维持抽象；                       *)
(*   头位见证仅经 token_eq_dec 实例消去生成。                             *)

Section TopPMirror.

Variable W : bool -> nat -> Set.
Variable W_dec : forall (t : bool) (p : nat), Or (W t p) (Not (W t p)).

Fixpoint p2wb_top_member (p : nat) (l : list bool) : bool -> Set :=
  match l with
  | nil => fun _ : bool => Empty_set
  | cons h rest => fun x : bool =>
      match p2wb_token_eq_dec x h with
      | inl _ => unit
      | inr _ =>
          match W_dec h p with
          | inl _ => Empty_set
          | inr _ => p2wb_top_member p rest x
          end
      end
  end.

(* top_p_keep 复现：单元素枚举已序，排序轴平凡 *)
Definition p2wb_top_keep (p : nat) (l : list bool) : bool -> Set :=
  p2wb_top_member p l.

(* 经实例消去的头位保留见证：仅经 p2wb_token_eq_dec 消去，
   不使用 W_dec（阈值抽象轴零引用） *)
Theorem p2wb_top_keep_head_witness : forall (p : nat) (l : list bool),
  p2wb_top_keep p (cons true l) true.
Proof.
  intros p l.
  exact (match p2wb_token_eq_dec true true with         | inl _ => tt         | inr h => match h (id_refl : Id true true) with end         end).
Qed.

End TopPMirror.

(* ################ 第 6 部：泛用封装证书 p2wb_pack ########################### *)
(* 参数序＝S06 接口群声明序（族A：Token/vocab/vocab_nonempty/token_eq_dec；*)
(*   族B：S_enum/S_finite_cover/keep/keep_dec）。                         *)
(*                                                                      *)

Inductive p2wb_pack : Type :=
| p2wb_pack_intro :
    forall (Tok : Set) (vocab0 : list Tok)
           (vocab_nonempty : Not (Id vocab0 nil))
           (token_eq_dec : forall a b : Tok, Or (Id a b) (Not (Id a b)))
           (St : Set) (S_enum0 : list St)
           (S_finite_cover : forall s : St, InT s S_enum0)
           (keep : St -> Set)
           (keep_dec : forall s : St, Or (keep s) (Not (keep s))),
      p2wb_pack.

(* 供给其一：常值形（keep 取常 unit，keep_dec 取 @inl unit tt） *)
Theorem p2wb_supplied : p2wb_pack.
Proof.
  exact (p2wb_pack_intro bool p2wb_vocab p2wb_vocab_nonempty p2wb_token_eq_dec                         bool p2wb_S_enum p2wb_S_finite_cover                         p2wb_keep p2wb_keep_dec).
Qed.

(* 供给其二：择留形（两支俱非平凡） *)
Theorem p2wb_supplied_sel : p2wb_pack.
Proof.
  exact (p2wb_pack_intro bool p2wb_vocab p2wb_vocab_nonempty p2wb_token_eq_dec                         bool p2wb_S_enum p2wb_S_finite_cover                         p2wb_keep_sel p2wb_keep_dec_sel).
Qed.

(* ################ 第 7 部：提取面判定核与核↔接口正确性证书 ################# *)

Definition p2wb_tok_dec_core (i j : bool) : bool :=
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

Lemma p2wb_tok_dec_core_correct : forall i j : bool,
  match p2wb_token_eq_dec i j with
  | inl _ => Id (p2wb_tok_dec_core i j) true
  | inr _ => Id (p2wb_tok_dec_core i j) false
  end.
Proof.
  intros i j.
  destruct i; destruct j; cbn [p2wb_token_eq_dec p2wb_tok_dec_core]; apply id_refl.
Qed.

(* ################ 假设审计（Print Assumptions 全 Closed） ################### *)

Print Assumptions p2wb_token_eq_dec.
Print Assumptions p2wb_keep_dec.
Print Assumptions p2wb_keep_dec_sel.
Print Assumptions p2wb_tail_plus_kept_full_sel.
Print Assumptions p2wb_sel_tail_mass_one.
Print Assumptions p2wb_top_keep_head_witness.
Print Assumptions p2wb_supplied.
Print Assumptions p2wb_supplied_sel.
Print Assumptions p2wb_tok_dec_core_correct.

(* 提取面：判定核单列（纯 bool 构造）；核↔接口正确性证书为证明内容，
   不入提取集，以假设审计替代。 *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "_a2_p2w_ex".
Separate Extraction p2wb_tok_dec_core.

(* ################ 第 8 部：W_dec 位 Set 重述位与具体层供给（上游清册项，   *)
(* ################ C2 底册 #11） ########################################## *)
(* 件内先例：第 2 部 p2wb_token_eq_dec（Or 形四支构造子逐一判定）；         *)
(*   重述形同 UpReqAttnUniformLimit 文尾 alm_token_eq_dec_set 款式：       *)
(*   sigT bool 见证形——正支给 W t p 见证，负支给 W t p -> Empty_set 函数   *)
(*  （Set 层否定见证，可提取）。                                           *)

(* Set 重述形定义位（注：本位即 W_dec 参数位的 Set 重述位） *)
Definition p2wb_wdec_set (W : bool -> nat -> Set) : Set :=
  forall (t : bool) (p : nat),
    sigT (fun d : bool =>
      match d with
      | true => W t p
      | false => W t p -> Empty_set
      end).

(* 桥一：Or 形判定接口 -> sigT bool 见证形 *)
Definition p2wb_wdec_of_or (W : bool -> nat -> Set)
           (kd : forall (t : bool) (p : nat), Or (W t p) (Not (W t p))) :
  p2wb_wdec_set W :=
  fun t p =>
    match kd t p with
    | inl h => existT _ true h
    | inr h => existT _ false h
    end.

(* 桥二：sigT bool 见证形 -> Or 形判定接口（原 Or 形接口签名零改动） *)
Definition p2wb_wdec_or_of (W : bool -> nat -> Set)
           (ds : p2wb_wdec_set W) :
  forall (t : bool) (p : nat), Or (W t p) (Not (W t p)) :=
  fun t p =>
    match ds t p with
    | existT _ true h => inl h
    | existT _ false h => inr h
    end.

(* 具体层供给：W 取布尔择留族（true 恒驻 unit、false 恒空），判定由       *)
(*   构造子分派直接给出（正支 tt 见证；负支构造子分裂空匹配）。            *)
Definition p2wb_W_sel : bool -> nat -> Set :=
  fun t _ =>
    match t with
    | true => unit
    | false => Empty_set
    end.

Theorem p2wb_wdec_supply : p2wb_wdec_set p2wb_W_sel.
Proof.
  intros t p.
  destruct t as [ | ].
  - exact (existT _ true tt).
  - refine (existT _ false _).
    intro h.
    exact (match h with end).
Qed.

(* 双形往返证书：重述形经桥二回到 Or 形接口（择留实例） *)
Definition p2wb_wdec_roundtrip :
  forall (t : bool) (p : nat), Or (p2wb_W_sel t p) (Not (p2wb_W_sel t p)) :=
  p2wb_wdec_or_of p2wb_W_sel p2wb_wdec_supply.

(* ================= 重述位假设面核验（预期全 Closed） ==================== *)
Print Assumptions p2wb_wdec_of_or.
Print Assumptions p2wb_wdec_or_of.
Print Assumptions p2wb_wdec_supply.
Print Assumptions p2wb_wdec_roundtrip.
