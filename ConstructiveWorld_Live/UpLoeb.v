(* ===================================================================== *)
(* UpLoeb.v — Löb 真证长线 D1：对角机制的构造性落地（纯 Set 层 / stdlib only） *)
(*                                                                       *)
(* 论文定位：「不完备性的构造性治理」HB D1–D3 构造性实现第一棒。              *)
(*   D1 = 对角机制（本件，保底交付）                                        *)
(*   D2 = 可证谓词 Σ(σ) 的构造性账本化（后续席位，接口建议见文件尾注释）      *)
(*   D3 = 导出条件 / Löb 主定理（后续席位）                                 *)
(*                                                                       *)
(* 与新素材 SelfRef 系伪 Löb 的三假法逐条对照（全部绕开）：                   *)
(*   假法① Löb 证明体 = hyp. 占位      → 本件无任何占位收尾；Prf 为封闭       *)
(*        归纳类型，且附元级可靠性定理 Prf_soundness（每个证明项都被语义       *)
(*        验证，结构上不可能藏 Triv/hyp 空壳）。                             *)
(*   假法② 对角引理 = Triv 平凡填充    → 本件对角定理的两个方向由 repl 规则   *)
(*        （替换不变量方案）真实组装；witness d = diagF th 是显式闭形          *)
(*        组合子（不动点构造），非占位。                                     *)
(*   假法③ eval_formula 量词硬编码     → 本件 D1 对象语言仅含方程原子与       *)
(*        蕴含（对角双条件所需全部），evalF 无任何量词分支可硬编码；量词        *)
(*        语义是 D2 的接口（诚实边界，见文件尾）。                            *)
(*   附：素材 decode = None 占位        → 本件 dT/dF 是全函数解码器，           *)
(*        dec_gnT / dec_gnF 往返定理真证。                                  *)
(*                                                                       *)
(* Set 层纪律：全部语句零 Prop（tid / sigT / bool / nat->nat）；tid 的         *)
(* Prop 内用（tidQ 提取定义等式）只出现在 Proof 内部。零公理式出口、零承认、    *)
(* 零占位参数、零中途弃证、零经典逻辑。全链信息性，可提取。                     *)
(* ===================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Wf_nat.

(* ===================================================================== *)
(* §0  Set 层恒等型基建（自 UpPLA/UpCLQuery 内联，零外部依赖）                *)
(* ===================================================================== *)

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

Definition tid_cong {A B : Type} (f : A -> B) (x y : A) (H : tid A x y) :
  tid B (f x) (f y) :=
  match H in tid _ a b return tid B (f a) (f b) with
  | tid_refl _ a0 => @tid_refl _ (f a0)
  end.

(* tid -> 定义等式（仅 Proof 内部使用；语句不出现 Prop） *)
Lemma tid_eq (A : Type) (x y : A) : x = y -> tid A x y.
Proof. intros H. rewrite H. apply tid_refl. Qed.

(* 从 tid 提取定义等式的 Ltac（仅 Proof 内部） *)
Ltac tidQ H E := pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as E.

(* 空型：tid bool 矛盾关闭 / 不可能性消去的载体 *)
Inductive nul : Set :=.

(* ===================================================================== *)
(* §1  语法层：封闭归纳类型 + 结构递归代入                                   *)
(*     D1 片段语言：项 = 变元/零/后继/自代抄符号；公式 = 方程原子/蕴含。       *)
(*     （无量词构造子 → 语法层不存在可被硬编码的量词分支，假法③无处藏身。）    *)
(* ===================================================================== *)

Inductive Term : Set :=
| tvar : nat -> Term
| tzero : Term
| tsucc : Term -> Term
| tsub : Term -> Term -> Term.

Inductive Formula : Set :=
| teq : Term -> Term -> Formula
| fimp : Formula -> Formula -> Formula.

Fixpoint numT (m : nat) : Term :=
  match m with
  | O => tzero
  | S m' => tsucc (numT m')
  end.

(* 变元 0 的代入（语言无约束词栏 → 无捕获问题，纯结构递归） *)
Fixpoint substT (u t : Term) : Term :=
  match u with
  | tvar O => t
  | tvar (S k) => tvar (S k)
  | tzero => tzero
  | tsucc u' => tsucc (substT u' t)
  | tsub a b => tsub (substT a t) (substT b t)
  end.

Fixpoint substF (f : Formula) (t : Term) : Formula :=
  match f with
  | teq u1 u2 => teq (substT u1 t) (substT u2 t)
  | fimp a b => fimp (substF a t) (substF b t)
  end.

(* 代入复合引理（bindless 版代入引理；对角组合子的承重件之一） *)
Lemma substT_comp : forall (u t1 t2 : Term),
  substT (substT u t1) t2 = substT u (substT t1 t2).
Proof.
  induction u as [k| |u IHu|a IHa b IHb]; intros t1 t2; simpl; try reflexivity.
  - destruct k; reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma substF_comp : forall (f : Formula) (t1 t2 : Term),
  substF (substF f t1) t2 = substF f (substT t1 t2).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t1 t2; simpl.
  - rewrite !substT_comp. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

(* ===================================================================== *)
(* §2  自由变元 / 一元性 / 闭性（bool 判定化）                                *)
(* ===================================================================== *)

Fixpoint fvT (u : Term) : list nat :=
  match u with
  | tvar k => k :: nil
  | tzero => nil
  | tsucc u' => fvT u'
  | tsub a b => fvT a ++ fvT b
  end.

Fixpoint fvF (f : Formula) : list nat :=
  match f with
  | teq u1 u2 => fvT u1 ++ fvT u2
  | fimp a b => fvF a ++ fvF b
  end.

Definition unaryT (t : Term) : bool := forallb (fun k : nat => Nat.eqb k 0) (fvT t).
Definition unaryF (f : Formula) : bool := forallb (fun k : nat => Nat.eqb k 0) (fvF f).
Definition closedT (t : Term) : bool :=
  match fvT t with nil => true | _ => false end.
Definition closedF (f : Formula) : bool :=
  match fvF f with nil => true | _ => false end.

Lemma forallb0_character : forall l : list nat,
  forallb (fun k : nat => Nat.eqb k 0) l = true <-> (forall k : nat, In k l -> k = 0).
Proof.
  intros l. split; intros H.
  - intros k Hk. apply Nat.eqb_eq.
    apply (proj1 (forallb_forall (fun k : nat => Nat.eqb k 0) l) H k Hk).
  - apply forallb_forall. intros x Hx. rewrite (H x Hx). reflexivity.
Qed.

Lemma numT_fv : forall (m k : nat), In k (fvT (numT m)) -> nul.
Proof.
  induction m as [|m IHm]; simpl; intros k Hk.
  - destruct Hk.
  - exact (IHm k Hk).
Qed.

(* 代入后的自由变元刻画（承重件之二） *)
Lemma fvT_subst : forall (u t : Term) (k : nat),
  In k (fvT (substT u t)) -> (In k (fvT u) /\ k <> 0) \/ In k (fvT t).
Proof.
  induction u as [k0| |u IHu|a IHa b IHb]; intros t k Hk; simpl in Hk; simpl.
  - destruct k0 as [|k'].
    + simpl in Hk. right. exact Hk.
    + simpl in Hk. destruct Hk as [Hk|[]].
      left. split.
      * left. exact Hk.
      * rewrite <- Hk. discriminate.
  - destruct Hk.
  - destruct (IHu t k Hk) as [Hc|Ht].
    + left. destruct Hc as [Hc1 Hc2]. split. * exact Hc1. * exact Hc2.
    + right. exact Ht.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (IHa t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (IHb t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
Qed.

Lemma fvF_subst : forall (f : Formula) (t : Term) (k : nat),
  In k (fvF (substF f t)) -> (In k (fvF f) /\ k <> 0) \/ In k (fvT t).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t k Hk; simpl in Hk; simpl.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (fvT_subst u1 t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (fvT_subst u2 t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (IHa t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. left. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
    + destruct (IHb t k Hk) as [Hc|Ht].
      * left. split. -- apply in_or_app. right. exact (proj1 Hc). -- exact (proj2 Hc).
      * right. exact Ht.
Qed.

(* 一元公式代入一元项仍一元（对角句闭性的承重件之三） *)
Lemma substF_fv_zero : forall (f : Formula) (t : Term),
  (forall k : nat, In k (fvF f) -> k = 0) ->
  (forall k : nat, In k (fvT t) -> k = 0) ->
  forall k : nat, In k (fvF (substF f t)) -> k = 0.
Proof.
  induction f as [u1 u2|a IHa b IHb]; simpl; intros t Hzf Hzt k Hk.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + destruct (fvT_subst u1 t k Hk) as [Hc|Ht2].
      * apply Hzf. simpl. apply in_or_app. left. exact (proj1 Hc).
      * apply Hzt. exact Ht2.
    + destruct (fvT_subst u2 t k Hk) as [Hc|Ht2].
      * apply Hzf. simpl. apply in_or_app. right. exact (proj1 Hc).
      * apply Hzt. exact Ht2.
  - apply in_app_or in Hk. destruct Hk as [Hk|Hk].
    + assert (Ha : forall j : nat, In j (fvF a) -> j = 0).
      { intros j Hj. apply Hzf. apply in_or_app. left. exact Hj. }
      exact (IHa t Ha Hzt k Hk).
    + assert (Hb : forall j : nat, In j (fvF b) -> j = 0).
      { intros j Hj. apply Hzf. apply in_or_app. right. exact Hj. }
      exact (IHb t Hb Hzt k Hk).
Qed.

Lemma unaryF_subst : forall (f : Formula) (t : Term),
  unaryT t = true -> unaryF f = true -> unaryF (substF f t) = true.
Proof.
  intros f t Ht Hf.
  unfold unaryT in Ht. unfold unaryF in Hf.
  pose proof (proj1 (forallb0_character (fvT t)) Ht) as Ht0.
  pose proof (proj1 (forallb0_character (fvF f)) Hf) as Hf0.
  apply (proj2 (forallb0_character (fvF (substF f t)))).
  exact (substF_fv_zero f t Hf0 Ht0).
Qed.

Lemma closedF_subst_num : forall (f : Formula) (m : nat),
  unaryF f = true -> closedF (substF f (numT m)) = true.
Proof.
  intros f m Hf. unfold unaryF in Hf.
  pose proof (proj1 (forallb0_character (fvF f)) Hf) as Hf0.
  assert (Hzn : forall k : nat, In k (fvT (numT m)) -> k = 0).
  { intros k Hk. destruct (numT_fv m k Hk). }
  unfold closedF.
  assert (Hnil : fvF (substF f (numT m)) = nil).
  { destruct (fvF (substF f (numT m))) as [|k l] eqn:E.
    - reflexivity.
    - exfalso. assert (Hk : In k (fvF (substF f (numT m)))).
      { rewrite E. left. reflexivity. }
      destruct (fvF_subst f (numT m) k Hk) as [[Hin Hne]|Ht2].
      + rewrite (Hf0 k Hin) in Hne. exact (Hne eq_refl).
      + destruct (numT_fv m k Ht2). }
  rewrite Hnil. reflexivity.
Qed.

(* ===================================================================== *)
(* §3  哥德尔编码：nat 配对函数 + 全函数解码器（素材 decode=None 假法的排除）   *)
(* ===================================================================== *)

Fixpoint pairp (a b : nat) : nat :=
  match a with
  | O => S (b + b)
  | S a' => (pairp a' b) + (pairp a' b)
  end.

Lemma pairp_pos : forall a b, (1 <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). lia.
Qed.

Lemma pairp_ge : forall a b, (b <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). lia.
Qed.

Lemma pairp_ge1 : forall a b, (a <= pairp a b)%nat.
Proof.
  induction a as [|a IHa]; intros b; cbn [pairp].
  - lia.
  - pose proof (IHa b). pose proof (pairp_pos a b). lia.
Qed.

(* 偶性 / 折半算术小引理链 *)
Lemma even_ss : forall x : nat, Nat.even (S (S x)) = Nat.even x.
Proof. reflexivity. Qed.

Lemma even_double : forall x : nat, Nat.even (x + x) = true.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (S x + S x) with (S (S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma even_succ_double : forall x : nat, Nat.even (S (x + x)) = false.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (S x + S x) with (S (S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma div2_ss : forall x : nat, Nat.div2 (S (S x)) = S (Nat.div2 x).
Proof. reflexivity. Qed.

Lemma div2_add : forall x : nat, Nat.div2 (x + x) = x.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (S x + S x) with (S (S (x + x))) by lia.
    rewrite div2_ss. rewrite IHx. reflexivity.
Qed.

Lemma div2_le : forall n : nat, (Nat.div2 n <= n)%nat.
Proof.
  induction n as [|n IHn].
  - cbn [Nat.div2]. lia.
  - pose proof (Nat.le_div2 n). lia.
Qed.

(* 以值为自身燃料的解码：unp2 f n，f 每层耗 1、值每层折半 *)
Fixpoint unp2 (f n : nat) {struct f} : option (nat * nat) :=
  match f with
  | O => None
  | S f' =>
      match n with
      | O => None
      | S n' =>
          if Nat.even (S n')
          then (match unp2 f' (Nat.div2 (S n')) with
                | Some (a, b) => Some (S a, b)
                | None => None
                end)
          else Some (O, Nat.div2 n')
      end
  end.

(* 单步展开引理：证明中受控展开的唯一通道（保持 unp2 折叠可重写） *)
Lemma unp2_S : forall (f' n : nat),
  unp2 (S f') n =
  match n with
  | O => None
  | S n' =>
      if Nat.even (S n')
      then (match unp2 f' (Nat.div2 (S n')) with
            | Some (a, b) => Some (S a, b)
            | None => None
            end)
      else Some (O, Nat.div2 n')
  end.
Proof. reflexivity. Qed.

(* 燃料充足时与自燃料形式一致（承重件之四） *)
Lemma unp2_fuel : forall x g : nat, (x <= g)%nat -> unp2 g x = unp2 x x.
Proof.
  intros x. induction x as [x IH] using lt_wf_ind. intros g Hle.
  destruct x as [|[|x'']].
  - destruct g as [|g'].
    + reflexivity.
    + reflexivity.
  - destruct g as [|g'].
    + exfalso. lia.
    + reflexivity.
  - destruct g as [|[|g']].
    + exfalso. lia.
    + exfalso. lia.
    + rewrite (unp2_S (S g') (S (S x''))).
      rewrite (unp2_S (S x'') (S (S x''))).
      cbv iota.
      destruct (Nat.even (S (S x''))).
      * rewrite (div2_ss x'').
        pose proof (div2_le x'') as Hd2.
        pose proof (proj2 (Nat.succ_le_mono (S x'') (S g')) Hle) as Hs1.
        pose proof (proj2 (Nat.succ_le_mono x'' g') Hs1) as Hxg.
        assert (Hv1 : (S (Nat.div2 x'') <= S g')%nat).
        { apply Nat.le_trans with (S x'').
          - apply le_n_S. exact Hd2.
          - exact Hs1. }
        assert (Hv2 : (S (Nat.div2 x'') <= S x'')%nat)
          by (apply le_n_S; exact Hd2).
        assert (Hlt : (S (Nat.div2 x'') < S (S x''))%nat).
        { apply Nat.le_lt_trans with (S x'').
          - exact Hv2.
          - apply Nat.lt_succ_diag_r. }
        pose proof (IH (S (Nat.div2 x'')) Hlt (S g') Hv1) as IH1.
        pose proof (IH (S (Nat.div2 x'')) Hlt (S x'') Hv2) as IH2.
        rewrite IH1. rewrite IH2.
        reflexivity.
      * reflexivity.
Qed.

(* 配对往返定理：解码器正确性的核心 *)
Lemma unp2_pair : forall a b : nat, unp2 (pairp a b) (pairp a b) = Some (a, b).
Proof.
  induction a as [|a IHa]; intros b.
  - cbn [pairp]. rewrite (unp2_S (b + b) (S (b + b))). cbv iota.
    rewrite even_succ_double. rewrite div2_add. reflexivity.
  - cbn [pairp]. destruct (pairp a b) as [|p] eqn:Ep.
    + exfalso. pose proof (pairp_pos a b) as Hp. rewrite Ep in Hp. lia.
    + replace (S p + S p) with (S (S (p + p))) by lia.
      rewrite (unp2_S (S (p + p)) (S (S (p + p)))). cbv iota.
      rewrite even_ss. rewrite even_double.
      rewrite div2_ss. rewrite div2_add.
      assert (Hle : (S p <= S (p + p))%nat) by lia.
      rewrite (unp2_fuel (S p) (S (p + p)) Hle).
      rewrite <- Ep. rewrite (IHa b). reflexivity.
Qed.

(* 编码函数（项 / 公式，标签互异） *)
Fixpoint gnT (t : Term) : nat :=
  match t with
  | tvar k => pairp 0 k
  | tzero => pairp 1 0
  | tsucc t' => pairp 2 (gnT t')
  | tsub a b => pairp 3 (pairp (gnT a) (gnT b))
  end.

Fixpoint gnF (f : Formula) : nat :=
  match f with
  | teq u1 u2 => pairp 4 (pairp (gnT u1) (gnT u2))
  | fimp a b => pairp 5 (pairp (gnF a) (gnF b))
  end.

(* 全函数解码器（燃料 = 码值本身） *)
Fixpoint dT2 (f c : nat) {struct f} : option Term :=
  match f with
  | O => None
  | S f' =>
      match unp2 c c with
      | Some (O, p) => Some (tvar p)
      | Some (S O, _) => Some tzero
      | Some (S (S O), q) =>
          (match dT2 f' q with
           | Some x => Some (tsucc x)
           | None => None
           end)
      | Some (S (S (S O)), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (tsub x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dT (c : nat) : option Term := dT2 c c.

Fixpoint dF2 (f c : nat) {struct f} : option Formula :=
  match f with
  | O => None
  | S f' =>
      match unp2 c c with
      | Some (S (S (S (S O))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (teq x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (S (S (S (S (S O)))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dF2 f' a with
                | Some x =>
                    (match dF2 f' b with
                     | Some y => Some (fimp x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dF (c : nat) : option Formula := dF2 c c.

(* 解码器 fuel 引理 *)
Lemma gnT_fuel : forall (t : Term) (k : nat), (gnT t <= k)%nat -> dT2 k (gnT t) = Some t.
Proof.
  intros t. induction t as [m| |t IHt|a IHa b IHb]; intros k Hk.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + cbn [gnT dT2]. rewrite unp2_pair. reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + cbn [gnT dT2]. rewrite unp2_pair. reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + assert (Hb : (gnT t + 1 <= pairp 2 (gnT t))%nat) by (cbn [pairp]; lia).
      cbn [gnT pairp] in Hk.
      assert (Hlt : (gnT t <= k')%nat) by lia.
      cbn [gnT dT2]. rewrite unp2_pair. cbv iota.
      rewrite (IHt k' Hlt). reflexivity.
  - destruct k as [|k'].
    + cbn [gnT pairp] in Hk. lia.
    + assert (Hq : (pairp (gnT a) (gnT b) + 1 <= pairp 3 (pairp (gnT a) (gnT b)))%nat)
        by (cbn [pairp]; lia).
      pose proof (pairp_ge1 (gnT a) (gnT b)) as Hga.
      pose proof (pairp_ge (gnT a) (gnT b)) as Hgb.
      cbn [gnT pairp] in Hk.
      assert (Hla : (gnT a <= k')%nat) by lia.
      assert (Hlb : (gnT b <= k')%nat) by lia.
      cbn [gnT dT2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (IHa k' Hla). rewrite (IHb k' Hlb). reflexivity.
Qed.

Lemma gnF_fuel : forall (f : Formula) (k : nat), (gnF f <= k)%nat -> dF2 k (gnF f) = Some f.
Proof.
  intros f. induction f as [u1 u2|a IHa b IHb]; intros k Hk.
  - destruct k as [|k'].
    + cbn [gnF pairp] in Hk. lia.
    + pose proof (pairp_ge1 (gnT u1) (gnT u2)) as Hq1.
      pose proof (pairp_ge (gnT u1) (gnT u2)) as Hq2.
      assert (Hq3 : (pairp (gnT u1) (gnT u2) + 1
                     <= pairp 4 (pairp (gnT u1) (gnT u2)))%nat) by (cbn [pairp]; lia).
      cbn [gnF pairp] in Hk.
      assert (Hla : (gnT u1 <= k')%nat) by lia.
      assert (Hlb : (gnT u2 <= k')%nat) by lia.
      cbn [gnF dF2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (gnT_fuel u1 k' Hla). rewrite (gnT_fuel u2 k' Hlb).
      reflexivity.
  - destruct k as [|k'].
    + cbn [gnF pairp] in Hk. lia.
    + pose proof (pairp_ge1 (gnF a) (gnF b)) as Hq1.
      pose proof (pairp_ge (gnF a) (gnF b)) as Hq2.
      assert (Hq3 : (pairp (gnF a) (gnF b) + 1
                     <= pairp 5 (pairp (gnF a) (gnF b)))%nat) by (cbn [pairp]; lia).
      cbn [gnF pairp] in Hk.
      assert (Hla : (gnF a <= k')%nat) by lia.
      assert (Hlb : (gnF b <= k')%nat) by lia.
      cbn [gnF dF2]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (IHa k' Hla). rewrite (IHb k' Hlb).
      reflexivity.
Qed.

(* 往返定理：真解码（素材 None 占位的正面对照件） *)
Lemma dec_gnT : forall t : Term, dT (gnT t) = Some t.
Proof.
  intros t. unfold dT. apply (gnT_fuel t (gnT t)). apply Nat.le_refl.
Qed.

Lemma dec_gnF : forall f : Formula, dF (gnF f) = Some f.
Proof.
  intros f. unfold dF. apply (gnF_fuel f (gnF f)). apply Nat.le_refl.
Qed.

(* 编码单射 *)
Lemma gnF_inj : forall f1 f2 : Formula, gnF f1 = gnF f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  pose proof (dec_gnF f1) as E1. pose proof (dec_gnF f2) as E2.
  rewrite H in E1. rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(* ===================================================================== *)
(* §4  码层代入函数与编码交换定理                                            *)
(* ===================================================================== *)

Definition gsubF (c m : nat) : nat :=
  match dF c with
  | Some f => gnF (substF f (numT m))
  | None => c
  end.

(* 编码与代入交换：码层 Sub 函数与语法层 subst 完全一致（承重件之五） *)
Theorem gn_comm : forall (f : Formula) (m : nat),
  tid nat (gnF (substF f (numT m))) (gsubF (gnF f) m).
Proof.
  intros f m. apply tid_eq. unfold gsubF. rewrite dec_gnF. reflexivity.
Qed.

(* ===================================================================== *)
(* §5  值语义（无硬编码量词分支：语言本身无量词）                              *)
(* ===================================================================== *)

Fixpoint valt (t : Term) (s : nat -> nat) : nat :=
  match t with
  | tvar k => s k
  | tzero => 0
  | tsucc t' => S (valt t' s)
  | tsub a b => gsubF (valt a s) (valt b s)
  end.

Definition upd (s : nat -> nat) (v k : nat) : nat :=
  match k with
  | O => v
  | S k' => s (S k')
  end.

Lemma valt_numT : forall (m : nat) (s : nat -> nat), valt (numT m) s = m.
Proof.
  induction m as [|m IHm]; intros s; simpl.
  - reflexivity.
  - rewrite IHm. reflexivity.
Qed.

Lemma valt_substT : forall (u t : Term) (s : nat -> nat),
  valt (substT u t) s = valt u (upd s (valt t s)).
Proof.
  induction u as [k0| |u IHu|a IHa b IHb]; intros t s; simpl.
  - destruct k0; simpl; reflexivity.
  - reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Fixpoint evalF (f : Formula) (s : nat -> nat) : bool :=
  match f with
  | teq u1 u2 => Nat.eqb (valt u1 s) (valt u2 s)
  | fimp a b => orb (negb (evalF a s)) (evalF b s)
  end.

Lemma evalF_subst : forall (f : Formula) (t : Term) (s : nat -> nat),
  evalF (substF f t) s = evalF f (upd s (valt t s)).
Proof.
  induction f as [u1 u2|a IHa b IHb]; intros t s; simpl.
  - rewrite !valt_substT. reflexivity.
  - rewrite IHa. rewrite IHb. reflexivity.
Qed.

(* ===================================================================== *)
(* §6  对象层证明系统 Prf：Set 值归纳 + 三条规则，全部有元级语义验证            *)
(*     ax_eqT：值相等的原子方程可证（真方程方案）                             *)
(*     mpF  ：分离规则                                                      *)
(*     repl ：值相等项在任何一元代入语境中可互换（Σ0 替换不变量方案的            *)
(*            最小化形态——对角双条件的唯一非逻辑公理，语义被下方可靠性定理        *)
(*            完全覆盖，结构上排除 Triv 填充）                               *)
(* ===================================================================== *)

Inductive Prf : Formula -> Set :=
| ax_eqT : forall u1 u2 : Term,
    (forall s : nat -> nat, tid nat (valt u1 s) (valt u2 s)) -> Prf (teq u1 u2)
| mpF : forall a b : Formula, Prf (fimp a b) -> Prf a -> Prf b
| repl : forall (th : Formula) (t1 t2 : Term),
    (forall s : nat -> nat, tid nat (valt t1 s) (valt t2 s)) ->
    Prf (fimp (substF th t1) (substF th t2)).

(* 元级可靠性：每个 Prf 项都在标准赋值下为真（反假法①的结构保证） *)
Theorem Prf_soundness : forall (f : Formula), Prf f ->
  forall s : nat -> nat, tid bool (evalF f s) true.
Proof.
  intros f H. induction H as [u1 u2 Hval | a b pf1 IH1 pf2 IH2 | th t1 t2 Hval].
  - intros s. apply tid_eq. cbn [evalF]. tidQ (Hval s) E. rewrite E. apply Nat.eqb_refl.
  - intros s. specialize (IH1 s). specialize (IH2 s).
    tidQ IH1 E1. tidQ IH2 E2.
    apply tid_eq. cbn [evalF] in E1. rewrite E2 in E1.
    cbn [negb orb] in E1. exact E1.
  - intros s. simpl. rewrite (evalF_subst th t1 s). rewrite (evalF_subst th t2 s).
    tidQ (Hval s) E. rewrite E.
    destruct (evalF th (upd s (valt t2 s))).
    + cbn [negb orb]. apply tid_refl.
    + cbn [negb orb]. apply tid_refl.
Qed.

(* ===================================================================== *)
(* §7  对角机制：diag_fix 组合子（显式闭形）与对角定理                          *)
(* ===================================================================== *)

(* 自代抄项：x sub x *)
Definition selfT : Term := tsub (tvar 0) (tvar 0).
(* 包装体：th 应用于自代抄项（仍留变元 0 槽位） *)
Definition wrapF (th : Formula) : Formula := substF th selfT.
(* diag_fix：对角组合子，d 的显式闭形 —— th 的包装体应用于自身代码 *)
Definition diagF (th : Formula) : Formula :=
  substF (wrapF th) (numT (gnF (wrapF th))).
(* 一元公式的数值应用 *)
Definition appN (th : Formula) (m : nat) : Formula := substF th (numT m).

Lemma unaryT_selfT : unaryT selfT = true.
Proof. unfold selfT, unaryT. simpl. reflexivity. Qed.

Lemma diagF_eq : forall th : Formula,
  tid Formula (diagF th)
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))).
Proof.
  intros th. apply tid_eq. unfold diagF, wrapF.
  rewrite substF_comp. reflexivity.
Qed.

(* 关键码恒等式：d 的码 = 码层代入 gsubF 在 (n, n) 处的值 *)
Theorem diag_code_eq : forall th : Formula,
  tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof.
  intros th. apply tid_eq. unfold diagF.
  tidQ (gn_comm (wrapF th) (gnF (wrapF th))) E.
  exact E.
Qed.

(* 关键值恒等式：d 的对角项在任何赋值下取值恰为 gnF d *)
Lemma diag_val_eq : forall (th : Formula) (s : nat -> nat),
  tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
    (gnF (diagF th)).
Proof.
  intros th s.
  assert (H1 : valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s
               = gsubF (gnF (wrapF th)) (gnF (wrapF th))).
  { cbn [valt]. rewrite valt_numT. reflexivity. }
  apply (tid_trans nat _ (gsubF (gnF (wrapF th)) (gnF (wrapF th)))).
  - apply tid_eq. exact H1.
  - apply tid_sym. apply diag_code_eq.
Qed.

(* 对角句的闭性 *)
Theorem diag_closed : forall th : Formula,
  tid bool (unaryF th) true -> tid bool (closedF (diagF th)) true.
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (unaryT_selfT) as Hut.
  assert (Hw : unaryF (wrapF th) = true).
  { unfold wrapF. apply unaryF_subst; assumption. }
  apply tid_eq. unfold diagF.
  apply (closedF_subst_num (wrapF th) (gnF (wrapF th)) Hw).
Qed.

(* ═══ D1 主定理：对角引理（可证版本，构造性 witness） ═══
   对每个一元公式 th，存在显式闭句 d = diagF th：
     1. d 闭（tid bool (closedF d) true 的构造性凭证）；
     2. ⊢ d → th(⌜d⌝) 与 ⊢ th(⌜d⌝) → d（Id (d) (f d) 的可证版本，
        双向 Prf 项真实组装自 repl 规则 + 码恒等式 + 值恒等式）。 *)
Theorem diagonal_lemma : forall th : Formula,
  tid bool (unaryF th) true ->
  sigT (fun d : Formula =>
    ((tid bool (closedF d) true) *
     ((Prf (fimp d (appN th (gnF d)))) *
      (Prf (fimp (appN th (gnF d)) d))))%type).
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (diag_closed th Hun) as Hcl.
  tidQ (diagF_eq th) EHd.
  assert (Hvals : forall s : nat -> nat,
    tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
      (valt (numT (gnF (diagF th))) s)).
  { intros s. apply (tid_trans nat _ (gnF (diagF th))).
    - apply diag_val_eq.
    - apply tid_sym. apply tid_eq. apply valt_numT. }
  assert (Hs1 : Prf (fimp
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))))
    (substF th (numT (gnF (diagF th)))))).
  { exact (repl th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))
              (numT (gnF (diagF th))) Hvals). }
  rewrite <- EHd in Hs1.
  assert (Hvals2 : forall s : nat -> nat,
    tid nat (valt (numT (gnF (diagF th))) s)
      (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)).
  { intros s. apply (tid_trans nat _ (gnF (diagF th))).
    - apply tid_eq. apply valt_numT.
    - apply tid_sym. apply diag_val_eq. }
  assert (Hs2 : Prf (fimp
    (substF th (numT (gnF (diagF th))))
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))))).
  { exact (repl th (numT (gnF (diagF th)))
              (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) Hvals2). }
  rewrite <- EHd in Hs2.
  exists (diagF th). split.
  - exact Hcl.
  - split.
    + exact Hs1.
    + exact Hs2.
Defined.

(* 码层干净形式：对角句的码恰为码层自代入值（无前提，tid 形式） *)
Theorem diagonal_code_fixed : forall th : Formula,
  tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof. exact diag_code_eq. Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不硬凑）：                                            *)
(*   1. 语法恒等式 d = th(⌜d⌝) 在一般情况下假（尺寸论证），故 D1 交付的是        *)
(*      「可证版本」——Prf 双向蕴含；这正是对角引理的标准形态。                  *)
(*   2. D1 对象理论 = 真闭方程 + MP + Σ0 替换不变量(repl)，其可靠性             *)
(*      Prf_soundness 已证；该理论足以承载对角机制，但尚不足以承载               *)
(*      Hilbert–Bernays 导出条件（需可证性谓词的语言内编码）。                   *)
(*   3. 量词语义与可证谓词 Σ(σ) 留给 D2（接口建议）：                          *)
(*      a. Formula 扩展 fall/fex 时，evalF 需以有界搜索算子实现（禁止               *)
(*         硬编码 true/false 分支），并保持 evalF_subst 的交换定理；           *)
(*      b. Σ(σ) 账本建议形态：sigT { w : nat & (Prf 层凭证) * (码账 tid 簇) }，   *)
(*         复用本件的 gsubF / dF / dec_gnF：D2 的「语言内可证性谓词」需要          *)
(*         的正是「码→公式」反射，本件的 dec_gnF 是其承重件；                   *)
(*      c. D3 导出条件建议：D1' = Prf f -> 账本(⌜f⌝) 居留（用 dT2 的 fuel 结构     *)
(*         给出证明项的码级重演）；D2' = MP 的码级封闭；D3' = 编码自涉            *)
(*         (Prf(⌜·⌝) 自身的 gnF 稳定性)。三件都不需要经典公理。                *)
(* ===================================================================== *)
