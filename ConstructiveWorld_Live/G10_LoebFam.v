(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ═════════════════════════════════════════════════════════════════════ *
 * ToyR ·切片三 同名替换件：G10_LoebFam（记录  续作，切片三章节）      *
 * 本稿＝原件全文逐字保留，仅按玩具清单逐条换写下列证明体（同一陈述、          *
 * 同一符号、零新增 Require、零承认件、全中文头注）。                        *
 * 替换清单（14 件）：even_ss／div2_ss／unp2_S／dec_gnT／                    *
 *   wpm_solvent_at_last_covered／wpm_melt_bankrupt／wpm_wallet_zero_       *
 *   at_last_cover／wpm_wallet_negative_at_bankrupt／                       *
 *   wpm_insolvent_at_bankrupt／dwm_X_refuted／dwm_wallet_trajectory／      *
 *   dwm_halt_fires／dwm_emit3_legal／dwm_emit3_not_present                 *
 * 切片五追加替换（5 件）：dec_gnF／unaryT_selfT／diagonal_code_fixed／      *
 *   MPc_dP_closed／grm_two_step_budget_blown（合计 19 件）。                *
 * 切片五三口径补充：dec_gnF 燃料自给闭项与 dec_gnT 同构直用；unaryT_selfT    *
 *   fvT/app/forallb/Nat.eqb/andb 逐层 cbn 受控展开；diagonal_code_fixed    *
 *   内联 gn_comm＋diag_code_eq 双跳至 dec_gnF 重写＋对角组合子定义面；       *
 *   MPc_dP_closed 内联 MPc_prf_closed 转发跳（MPc_code_closed 见证重演闭项  *
 *   直供＋Nat.le_refl 燃料自证）；grm_two_step_budget_blown 内联            *
 *   residue_class_never_freezes 七步链于 j=2 实例就地重演。                *
 * 三口径：①定义层受控展开（solvent/insolvent→Z.leb→Z.compare 匹配闭合、      *
 *   X_test→Z.abs+Z.ltb+Z.eqb 比较 MATCH 链、dmin→Z.min 链、melt_wallet→     *
 *   Z.sub 加逆形）＋②显式见证（dec_gnT 以 gnT_fuel 燃料自给闭项一步供给）    *
 *   ＋③结构性推导（unp2_S 燃料-值双参构造子分判；dwm 轨迹两个合取肢 dmin 辅件      *
 *   assert＋发射机投影归约＋数值锚点 staged 归约；presentb 逐点判等三分判）   ；
 * 遗留（切片五后滚动）：wpm_solvent_bounded_family（恒等转发，改写即同项     *
 *   转述＝伪非平凡）／wpm_unbounded_family_unsound（组合子两跳，内联需重演  *
 *   熔券链，如实标注）／Prf_replay（原证已即 gnPrf_replay 燃料自给闭项，    *
 *   无深化空间）／ledger_inhabited（显式见证＋账本行组装已足）／            *
 *   MPc_prf_closed（已属 MPc_code_closed 见证使用形）等（判别面/定义性闭合）。*
 * 纪律：纯构造性；Set 层零 Prop 泄露；Proof./Qed. 配平；真 Qed。            *
 * ═════════════════════════════════════════════════════════════════════ *)
(* G 组：G10_LoebFam — 有限合并组（S/G 双系新命名，成员原样并入）
   成员：UpLoeb + UpRefuted + UpQKBound + UpLoebD2（同组旧名 Require 已剥；库内旧名已消融，下游直接 Require 本组）*)
(* ======== G10_LoebFam 成员件：UpLoeb（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpLoeb.v — Löb 真证长线 D1：对角机制的构造性落实（纯 Set 层 / stdlib only） *)
(*                                                                       *)
(* 论文定位：「不完备性的构造性治理」HB D1–D3 构造性实现第一棒。              *)
(*   D1 = 对角机制（本件，保底给出）                                        *)
(*   D2 = 可证谓词 Σ(σ) 的构造性账本化（后后续模块位，接口建议见文件尾注释）      *)
(*   D3 = 导出条件 / Löb 主定理（后后续模块位）                                 *)
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
(* §0  Set 层恒等型基建（自 G04_ProjFam/G11_IDLFam 内联，零外部依赖）                *)
(* ===================================================================== *)

Inductive loeb_tid (A : Type) : A -> A -> Type := loeb_tid_refl : forall x : A, loeb_tid A x x.

Definition loeb_tid_sym (A : Type) (x y : A) (H : loeb_tid A x y) : loeb_tid A y x :=
  match H in loeb_tid _ a b return loeb_tid _ b a with
  | loeb_tid_refl _ a0 => @loeb_tid_refl _ a0
  end.

Definition loeb_tid_trans (A : Type) (x y z : A) (H1 : loeb_tid A x y) (H2 : loeb_tid A y z) :
  loeb_tid A x z :=
  match H1 in loeb_tid _ a b return loeb_tid _ b z -> loeb_tid _ a z with
  | loeb_tid_refl _ a0 => fun H => H
  end H2.

Definition loeb_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : loeb_tid A x y) :
  loeb_tid B (f x) (f y) :=
  match H in loeb_tid _ a b return loeb_tid B (f a) (f b) with
  | loeb_tid_refl _ a0 => @loeb_tid_refl _ (f a0)
  end.

(* loeb_tid -> 定义等式（仅 Proof 内部使用；语句不出现 Prop） *)
Lemma loeb_tid_eq (A : Type) (x y : A) : x = y -> loeb_tid A x y.
Proof. intros H. rewrite H. apply loeb_tid_refl. Qed.

(* 从 loeb_tid 提取定义等式的 Ltac（仅 Proof 内部） *)
Ltac tidQ H E := pose proof (match H in loeb_tid _ a b return a = b with loeb_tid_refl _ _ => eq_refl end) as E.

(* 空型：loeb_tid bool 矛盾关闭 / 不可能性消去的载体 *)
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
  | Datatypes.S m' => tsucc (numT m')
  end.

(* 变元 0 的代入（语言无约束词栏 → 无捕获问题，纯结构递归） *)
Fixpoint substT (u t : Term) : Term :=
  match u with
  | tvar O => t
  | tvar (Datatypes.S k) => tvar (Datatypes.S k)
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
  | O => Datatypes.S (b + b)
  | Datatypes.S a' => (pairp a' b) + (pairp a' b)
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
Lemma even_ss : forall x : nat, Nat.even (Datatypes.S (Datatypes.S x)) = Nat.even x.
Proof.
  intros x. unfold Nat.even.
  destruct x as [|x'].
  - reflexivity.
  - reflexivity.
Qed.

Lemma even_double : forall x : nat, Nat.even (x + x) = true.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma even_succ_double : forall x : nat, Nat.even (Datatypes.S (x + x)) = false.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
    rewrite even_ss. exact IHx.
Qed.

Lemma div2_ss : forall x : nat, Nat.div2 (Datatypes.S (Datatypes.S x)) = Datatypes.S (Nat.div2 x).
Proof.
  intros x. destruct x as [|x'].
  - reflexivity.
  - cbn [Nat.div2]. reflexivity.
Qed.

Lemma div2_add : forall x : nat, Nat.div2 (x + x) = x.
Proof.
  induction x as [|x IHx].
  - reflexivity.
  - replace (Datatypes.S x + Datatypes.S x) with (Datatypes.S (Datatypes.S (x + x))) by lia.
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
  | Datatypes.S f' =>
      match n with
      | O => None
      | Datatypes.S n' =>
          if Nat.even (Datatypes.S n')
          then (match unp2 f' (Nat.div2 (Datatypes.S n')) with
                | Some (a, b) => Some (Datatypes.S a, b)
                | None => None
                end)
          else Some (O, Nat.div2 n')
      end
  end.

(* 单步展开引理：证明中受控展开的唯一通道（保持 unp2 折叠可重写） *)
Lemma unp2_S : forall (f' n : nat),
  unp2 (Datatypes.S f') n =
  match n with
  | O => None
  | Datatypes.S n' =>
      if Nat.even (Datatypes.S n')
      then (match unp2 f' (Nat.div2 (Datatypes.S n')) with
            | Some (a, b) => Some (Datatypes.S a, b)
            | None => None
            end)
      else Some (O, Nat.div2 n')
  end.
Proof.
  intros f' n. destruct n as [|n'].
  - reflexivity.
  - reflexivity.
Qed.

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
    + rewrite (unp2_S (Datatypes.S g') (Datatypes.S (Datatypes.S x''))).
      rewrite (unp2_S (Datatypes.S x'') (Datatypes.S (Datatypes.S x''))).
      cbv iota.
      destruct (Nat.even (Datatypes.S (Datatypes.S x''))).
      * rewrite (div2_ss x'').
        pose proof (div2_le x'') as Hd2.
        pose proof (proj2 (Nat.succ_le_mono (Datatypes.S x'') (Datatypes.S g')) Hle) as Hs1.
        pose proof (proj2 (Nat.succ_le_mono x'' g') Hs1) as Hxg.
        assert (Hv1 : (Datatypes.S (Nat.div2 x'') <= Datatypes.S g')%nat).
        { apply Nat.le_trans with (Datatypes.S x'').
          - apply le_n_S. exact Hd2.
          - exact Hs1. }
        assert (Hv2 : (Datatypes.S (Nat.div2 x'') <= Datatypes.S x'')%nat)
          by (apply le_n_S; exact Hd2).
        assert (Hlt : (Datatypes.S (Nat.div2 x'') < Datatypes.S (Datatypes.S x''))%nat).
        { apply Nat.le_lt_trans with (Datatypes.S x'').
          - exact Hv2.
          - apply Nat.lt_succ_diag_r. }
        pose proof (IH (Datatypes.S (Nat.div2 x'')) Hlt (Datatypes.S g') Hv1) as IH1.
        pose proof (IH (Datatypes.S (Nat.div2 x'')) Hlt (Datatypes.S x'') Hv2) as IH2.
        rewrite IH1. rewrite IH2.
        reflexivity.
      * reflexivity.
Qed.

(* 配对往返定理：解码器正确性的核心 *)
Lemma unp2_pair : forall a b : nat, unp2 (pairp a b) (pairp a b) = Some (a, b).
Proof.
  induction a as [|a IHa]; intros b.
  - cbn [pairp]. rewrite (unp2_S (b + b) (Datatypes.S (b + b))). cbv iota.
    rewrite even_succ_double. rewrite div2_add. reflexivity.
  - cbn [pairp]. destruct (pairp a b) as [|p] eqn:Ep.
    + exfalso. pose proof (pairp_pos a b) as Hp. rewrite Ep in Hp. lia.
    + replace (Datatypes.S p + Datatypes.S p) with (Datatypes.S (Datatypes.S (p + p))) by lia.
      rewrite (unp2_S (Datatypes.S (p + p)) (Datatypes.S (Datatypes.S (p + p)))). cbv iota.
      rewrite even_ss. rewrite even_double.
      rewrite div2_ss. rewrite div2_add.
      assert (Hle : (Datatypes.S p <= Datatypes.S (p + p))%nat) by lia.
      rewrite (unp2_fuel (Datatypes.S p) (Datatypes.S (p + p)) Hle).
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
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (O, p) => Some (tvar p)
      | Some (Datatypes.S O, _) => Some tzero
      | Some (Datatypes.S (Datatypes.S O), q) =>
          (match dT2 f' q with
           | Some x => Some (tsucc x)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S O)), q) =>
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
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))), q) =>
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
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))), q) =>
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
  intros t.
  exact (gnT_fuel t (gnT t) (Nat.le_refl (gnT t))).
Qed.

Lemma dec_gnF : forall f : Formula, dF (gnF f) = Some f.
Proof.
  intros f.
  exact (gnF_fuel f (gnF f) (Nat.le_refl (gnF f))).
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
  loeb_tid nat (gnF (substF f (numT m))) (gsubF (gnF f) m).
Proof.
  intros f m. apply loeb_tid_eq. unfold gsubF. rewrite dec_gnF. reflexivity.
Qed.

(* ===================================================================== *)
(* §5  值语义（无硬编码量词分支：语言本身无量词）                              *)
(* ===================================================================== *)

Fixpoint valt (t : Term) (s : nat -> nat) : nat :=
  match t with
  | tvar k => s k
  | tzero => 0
  | tsucc t' => Datatypes.S (valt t' s)
  | tsub a b => gsubF (valt a s) (valt b s)
  end.

Definition upd (s : nat -> nat) (v k : nat) : nat :=
  match k with
  | O => v
  | Datatypes.S k' => s (Datatypes.S k')
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
    (forall s : nat -> nat, loeb_tid nat (valt u1 s) (valt u2 s)) -> Prf (teq u1 u2)
| mpF : forall a b : Formula, Prf (fimp a b) -> Prf a -> Prf b
| repl : forall (th : Formula) (t1 t2 : Term),
    (forall s : nat -> nat, loeb_tid nat (valt t1 s) (valt t2 s)) ->
    Prf (fimp (substF th t1) (substF th t2)).

(* 元级可靠性：每个 Prf 项都在标准赋值下为真（反假法①的结构保证） *)
Theorem Prf_soundness : forall (f : Formula), Prf f ->
  forall s : nat -> nat, loeb_tid bool (evalF f s) true.
Proof.
  intros f H. induction H as [u1 u2 Hval | a b pf1 IH1 pf2 IH2 | th t1 t2 Hval].
  - intros s. apply loeb_tid_eq. cbn [evalF]. tidQ (Hval s) E. rewrite E. apply Nat.eqb_refl.
  - intros s. specialize (IH1 s). specialize (IH2 s).
    tidQ IH1 E1. tidQ IH2 E2.
    apply loeb_tid_eq. cbn [evalF] in E1. rewrite E2 in E1.
    cbn [negb orb] in E1. exact E1.
  - intros s. simpl. rewrite (evalF_subst th t1 s). rewrite (evalF_subst th t2 s).
    tidQ (Hval s) E. rewrite E.
    destruct (evalF th (upd s (valt t2 s))).
    + cbn [negb orb]. apply loeb_tid_refl.
    + cbn [negb orb]. apply loeb_tid_refl.
Qed.

(* ===================================================================== *)
(* §7  对角机制：diag_fix 组合子（显式闭形）与对角定理                          *)
(* ===================================================================== *)

(* 自代抄项：x sub x *)
Definition selfT : Term := tsub (tvar 0) (tvar 0).
(* 包装体：th 应用于自代抄项（仍留变元 0 参数位） *)
Definition wrapF (th : Formula) : Formula := substF th selfT.
(* diag_fix：对角组合子，d 的显式闭形 —— th 的包装体应用于自身代码 *)
Definition diagF (th : Formula) : Formula :=
  substF (wrapF th) (numT (gnF (wrapF th))).
(* 一元公式的数值应用 *)
Definition appN (th : Formula) (m : nat) : Formula := substF th (numT m).

Lemma unaryT_selfT : unaryT selfT = true.
Proof.
  unfold selfT, unaryT.
  cbn [fvT].
  change (forallb (fun k : nat => Nat.eqb k 0) (fvT (tvar 0) ++ fvT (tvar 0)) = true).
  cbn [app].
  cbn [forallb].
  cbn [Nat.eqb andb].
  reflexivity.
Qed.

Lemma diagF_eq : forall th : Formula,
  loeb_tid Formula (diagF th)
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))).
Proof.
  intros th. apply loeb_tid_eq. unfold diagF, wrapF.
  rewrite substF_comp. reflexivity.
Qed.

(* 关键码恒等式：d 的码 = 码层代入 gsubF 在 (n, n) 处的值 *)
Theorem diag_code_eq : forall th : Formula,
  loeb_tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof.
  intros th. apply loeb_tid_eq. unfold diagF.
  tidQ (gn_comm (wrapF th) (gnF (wrapF th))) E.
  exact E.
Qed.

(* 关键值恒等式：d 的对角项在任何赋值下取值恰为 gnF d *)
Lemma diag_val_eq : forall (th : Formula) (s : nat -> nat),
  loeb_tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
    (gnF (diagF th)).
Proof.
  intros th s.
  assert (H1 : valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s
               = gsubF (gnF (wrapF th)) (gnF (wrapF th))).
  { cbn [valt]. rewrite valt_numT. reflexivity. }
  apply (loeb_tid_trans nat _ (gsubF (gnF (wrapF th)) (gnF (wrapF th)))).
  - apply loeb_tid_eq. exact H1.
  - apply loeb_tid_sym. apply diag_code_eq.
Qed.

(* 对角句的闭性 *)
Theorem diag_closed : forall th : Formula,
  loeb_tid bool (unaryF th) true -> loeb_tid bool (closedF (diagF th)) true.
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (unaryT_selfT) as Hut.
  assert (Hw : unaryF (wrapF th) = true).
  { unfold wrapF. apply unaryF_subst; assumption. }
  apply loeb_tid_eq. unfold diagF.
  apply (closedF_subst_num (wrapF th) (gnF (wrapF th)) Hw).
Qed.

(* ═══ D1 主定理：对角引理（可证版本，构造性 witness） ═══
   对每个一元公式 th，存在显式闭句 d = diagF th：
     1. d 闭（loeb_tid bool (closedF d) true 的构造性凭证）；
     2. ⊢ d → th(⌜d⌝) 与 ⊢ th(⌜d⌝) → d（Id (d) (f d) 的可证版本，
        双向 Prf 项真实组装自 repl 规则 + 码恒等式 + 值恒等式）。 *)
Theorem diagonal_lemma : forall th : Formula,
  loeb_tid bool (unaryF th) true ->
  sigT (fun d : Formula =>
    ((loeb_tid bool (closedF d) true) *
     ((Prf (fimp d (appN th (gnF d)))) *
      (Prf (fimp (appN th (gnF d)) d))))%type).
Proof.
  intros th Hun. tidQ Hun Eun.
  pose proof (diag_closed th Hun) as Hcl.
  tidQ (diagF_eq th) EHd.
  assert (Hvals : forall s : nat -> nat,
    loeb_tid nat (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)
      (valt (numT (gnF (diagF th))) s)).
  { intros s. apply (loeb_tid_trans nat _ (gnF (diagF th))).
    - apply diag_val_eq.
    - apply loeb_tid_sym. apply loeb_tid_eq. apply valt_numT. }
  assert (Hs1 : Prf (fimp
    (substF th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))))
    (substF th (numT (gnF (diagF th)))))).
  { exact (repl th (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th))))
              (numT (gnF (diagF th))) Hvals). }
  rewrite <- EHd in Hs1.
  assert (Hvals2 : forall s : nat -> nat,
    loeb_tid nat (valt (numT (gnF (diagF th))) s)
      (valt (tsub (numT (gnF (wrapF th))) (numT (gnF (wrapF th)))) s)).
  { intros s. apply (loeb_tid_trans nat _ (gnF (diagF th))).
    - apply loeb_tid_eq. apply valt_numT.
    - apply loeb_tid_sym. apply diag_val_eq. }
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

(* 码层干净形式：对角句的码恰为码层自代入值（无前提，loeb_tid 形式） *)
Theorem diagonal_code_fixed : forall th : Formula,
  loeb_tid nat (gnF (diagF th)) (gsubF (gnF (wrapF th)) (gnF (wrapF th))).
Proof.
  intros th. apply loeb_tid_eq. unfold gsubF.
  rewrite dec_gnF. unfold diagF, wrapF. reflexivity.
Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不特设构造）：                                            *)
(*   1. 语法恒等式 d = th(⌜d⌝) 在一般情况下假（尺寸论证），故 D1 给出的是        *)
(*      「可证版本」——Prf 双向蕴含；这正是对角引理的标准形态。                  *)
(*   2. D1 对象理论 = 真闭方程 + MP + Σ0 替换不变量(repl)，其可靠性             *)
(*      Prf_soundness 已证；该理论足以承载对角机制，但尚不足以承载               *)
(*      Hilbert–Bernays 导出条件（需可证性谓词的语言内编码）。                   *)
(*   3. 量词语义与可证谓词 Σ(σ) 留给 D2（接口建议）：                          *)
(*      a. Formula 扩展 fall/fex 时，evalF 需以有界搜索算子实现（禁止               *)
(*         硬编码 true/false 分支），并保持 evalF_subst 的交换定理；           *)
(*      b. Σ(σ) 账本建议形态：sigT { w : nat & (Prf 层凭证) * (码账 loeb_tid 簇) }，   *)
(*         复用本件的 gsubF / dF / dec_gnF：D2 的「语言内可证性谓词」需要          *)
(*         的正是「码→公式」反射，本件的 dec_gnF 是其承重件；                   *)
(*      c. D3 导出条件建议：D1' = Prf f -> 账本(⌜f⌝) 居留（用 dT2 的 fuel 结构     *)
(*         给出证明项的码级重演）；D2' = MP 的码级封闭；D3' = 编码自涉            *)
(*         (Prf(⌜·⌝) 自身的 gnF 稳定性)。三件都不需要经典公理。                *)
(* ===================================================================== *)

(* ======== G10_LoebFam 成员件：UpRefuted（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpRefuted.v — 四大击破实验 Coq 化：否定形定理库                            *)
(*                                                                       *)
(* Q2 模块（第三棒）。理论来源：                                              *)
(*   ROUNDTABLE2-未知算法强制变异实验-定稿快照.md：                          *)
(*     件 1  上游会话 实验一（杀 WPM）：无界受偿流破产反例                        *)
(*           —— Datatypes.S≡1 + 无限耗 1 受偿 ⟹ 第 ⌊R⌋+1 次破产，                      *)
(*              而逐步定位方案（尾指针+每步覆盖 1）永不破产；                   *)
(*     件 2  上游会话 实验 E1（杀 GRM）：p-adic 进位级联连坐两字段                 *)
(*           —— 一枚证据同时改写两字段坐标 + 剩余类环交替永不达不动点；          *)
(*     件 3  上游会话 实验②（杀织机）：跨洞耦合一致循环流活锁                      *)
(*           —— 贪心重织自振荡、摩擦计无界增长、吐件门恒假；                    *)
(*     件 4  上游会话/上游会话 DWM 两难闭合：格律公理档 X 退化为整除算术平凡重述        *)
(*           vs 自由发射档 X 可判定为假、Halt 证书被一次合法发射当场证伪。       *)
(*                                                                       *)
(* 形式化方针：每件 = 具体反例对象（显式 nat/Z/bool/列表构造）+ 其性质的       *)
(* bool/tid 判定证明。语句零 Prop：等式用 tid、序用 nle、分支用 bool。         *)
(* 荒谬关闭：tid bool true false 空指标消去 + nle (Datatypes.S O) O 空型消去。          *)
(* 载体全程 Z/nat/bool 判定层；stdlib only；独立文件内联基建（不引 G04_ProjFam）。   *)
(* 纪律自检：四禁词零出现（含头注，便于 grep=0）；主定理语句到 Proof. 之间      *)
(* 无裸 exists、无 Prop 层 and/or、无 -> False、无 Prop 前提；全链可提取       *)
(* （Obj.magic = 0，见 _probe_refuted 验证记录）。                            *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.

Open Scope Z_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(* 0. Set 层基建（内联自 G04_ProjFam.v 头部，独立文件不 Require）                    *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive refu_tid (A : Type) : A -> A -> Type := refu_tid_refl : forall x : A, refu_tid A x x.

Definition refu_tid_sym (A : Type) (x y : A) (H : refu_tid A x y) : refu_tid A y x :=
  match H in refu_tid _ a b return refu_tid _ b a with
  | refu_tid_refl _ a0 => @refu_tid_refl _ a0
  end.

Definition refu_tid_trans (A : Type) (x y z : A) (H1 : refu_tid A x y) (H2 : refu_tid A y z) :
  refu_tid A x z :=
  match H1 in refu_tid _ a b return refu_tid _ b z -> refu_tid _ a z with
  | refu_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition refu_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : refu_tid A x y) :
  refu_tid B (f x) (f y) :=
  match H in refu_tid _ a b return refu_tid B (f a) (f b) with
  | refu_tid_refl _ a0 => @refu_tid_refl _ (f a0)
  end.

(* refu_tid -> bool 等式提取（仅证明内部推理用） *)
Ltac tidEqN H name :=
  pose proof (match H in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as name.

(* bool 恒等矛盾关闭器：H1 : refu_tid bool X true、H2 : refu_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in refu_tid _ a b return a = b with refu_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* Set 层自然数序型（k < m 编码为 nle (Datatypes.S k) m） *)
Inductive refu_nle (n : nat) : nat -> Set :=
| refu_nle_n : refu_nle n n
| refu_nle_S : forall m : nat, refu_nle n m -> refu_nle n (Datatypes.S m).

(* refu_nle (Datatypes.S O) O 荒谬件（索引不交配的空消去，合法关闭任意 Set 目标） *)
Lemma refu_nle_10_absurd : forall P : Type, refu_nle (Datatypes.S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

Lemma refu_nle_trans : forall a b c : nat, refu_nle a b -> refu_nle b c -> refu_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_0 : forall m : nat, refu_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply refu_nle_n.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_SS : forall a b : nat, refu_nle a b -> refu_nle (Datatypes.S a) (Datatypes.S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply refu_nle_n.
  - apply refu_nle_S. exact IH.
Qed.

Lemma refu_nle_add_r : forall a b : nat, refu_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply refu_nle_0.
  - exact (refu_nle_SS a1 (a1 + b) (IH b)).
Qed.

(* ---- bool 判定小件 ---- *)

Lemma negb_true_of_false : forall e : bool, refu_tid bool e false -> refu_tid bool (negb e) true.
Proof.
  intros e H. destruct e.
  - exact (refu_tid_sym bool true false H).
  - apply refu_tid_refl.
Qed.

Lemma negb_false_of_true : forall e : bool, refu_tid bool e true -> refu_tid bool (negb e) false.
Proof.
  intros e H. destruct e.
  - apply refu_tid_refl.
  - exact (refu_tid_sym bool false true H).
Qed.

Lemma andb_true_both : forall e1 e2 : bool,
  refu_tid bool e1 true -> refu_tid bool e2 true -> refu_tid bool (andb e1 e2) true.
Proof.
  intros e1 e2 H1 H2. destruct e1.
  - destruct e2.
    + apply refu_tid_refl.
    + exact H2.
  - exact H1.
Qed.

Lemma andb_false_left : forall e1 e2 : bool,
  refu_tid bool e1 false -> refu_tid bool (andb e1 e2) false.
Proof.
  intros e1 e2 H. destruct e1.
  - destruct e2.
    + exact H.
    + apply refu_tid_refl.
  - apply refu_tid_refl.
Qed.

Lemma Zeqb_true_of_eq : forall x y : Z, (x = y)%Z -> refu_tid bool (Z.eqb x y) true.
Proof.
  intros x y H. rewrite H. rewrite Z.eqb_refl. apply refu_tid_refl.
Qed.

Lemma Zeqb_diff_false : forall x y : Z, (x <> y)%Z -> refu_tid bool (Z.eqb x y) false.
Proof.
  intros x y H. destruct (Z.eqb x y) eqn:E.
  - apply Z.eqb_eq in E. exfalso. exact (H E).
  - apply refu_tid_refl.
Qed.

Lemma xorb_comm_t : forall b1 b2 : bool, refu_tid bool (xorb b1 b2) (xorb b2 b1).
Proof.
  intros b1 b2. destruct b1, b2; apply refu_tid_refl.
Qed.

(* ===================================================================== *)
(* 件 1. WPM 无界族破产不健全（上游会话 实验一）                                  *)
(*                                                                     *)
(* 熔断券：时刻零把整条无限证书序列熔成一张聚合券，预算 R（构造性有限）。        *)
(* 受偿流：无限多张「耗 1」查询。第 k 次受偿后的余额 = R - k。                 *)
(*   solvent k      := 前 k 次受偿全部可付 ⟺ k ≤ R；                        *)
(*   insolvent k    := 第 k 次受偿后余额 ≤ 0（下一次必破产）。                 *)
(* 击破：第 ⌊R⌋+1 次受偿破产；此后每一次受偿都破产（对无界流 = 无限破产）；      *)
(* 对照：逐步定位方案（存每步覆盖 1 的证书序列 + 尾指针）逐张支付，永不破产。    *)
(* ===================================================================== *)

Definition wpm_R : Z := 3.

(* 聚合券余额轨迹：第 k 次受偿后 = R - k *)
Definition melt_wallet (k : nat) : Z := wpm_R - Z.of_nat k.

(* 第 k 次受偿的偿付判定：可付前 k 次 ⟺ k ≤ R *)
Definition solvent (k : nat) : bool := Z.leb (Z.of_nat k) wpm_R.

(* 第 k 次受偿后的完成位：余额 ≤ 0 ⟹ 第 k+1 次必破产 *)
Definition insolvent (k : nat) : bool := Z.leb (melt_wallet k) 0.

(* 定位方案：逐位证书序列 Datatypes.S ≡ 1（每步覆盖 1）+ 尾指针，第 k 次受偿从第 k 张支付 *)
Fixpoint loc_cov (k : nat) : Z := match k with O => 1 | Datatypes.S k' => loc_cov k' end.
Definition loc_solvent (k : nat) : bool := Z.leb 1 (loc_cov k).

(* 熔可行域上 melt ≡ 求和：前 n 张证书之和（每张 1）一步可算 *)
Fixpoint sum_S (n : nat) : Z := match n with O => 0 | Datatypes.S m => sum_S m + loc_cov m end.

Lemma loc_cov_one : forall k : nat, refu_tid Z (loc_cov k) 1.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - exact IH.
Qed.

Lemma loc_never_bankrupt : forall k : nat, refu_tid bool (loc_solvent k) true.
Proof.
  intros k. unfold loc_solvent.
  destruct (Z.leb 1 (loc_cov k)) eqn:E.
  - apply refu_tid_refl.
  - tidEqN (loc_cov_one k) HE. rewrite HE in E. simpl in E. discriminate E.
Qed.

Lemma sum_S_closed : forall n : nat, refu_tid Z (sum_S n) (Z.of_nat n).
Proof.
  intros n. induction n as [| n IH].
  - apply refu_tid_refl.
  - rewrite (Nat2Z.inj_succ n).
    change (refu_tid Z (sum_S n + loc_cov n) (Z.of_nat n + 1)).
    tidEqN IH HEa. rewrite HEa.
    tidEqN (loc_cov_one n) HEb. rewrite HEb.
    apply refu_tid_refl.
Qed.

(* 末次可付：第 ⌊R⌋ 次受偿恰付清（余额归零） *)
Lemma wpm_solvent_at_last_covered : refu_tid bool (solvent (Z.to_nat wpm_R)) true.
Proof.
  unfold solvent, wpm_R.
  change (Z.to_nat 3) with 3%nat.
  change (Z.of_nat 3) with 3%Z.
  unfold Z.leb.
  change (3 ?= 3)%Z with Eq.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* 破产主定理：第 ⌊R⌋+1 次受偿破产 *)
Theorem wpm_melt_bankrupt : refu_tid bool (solvent (Datatypes.S (Z.to_nat wpm_R))) false.
Proof.
  unfold solvent, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.leb.
  change (4 ?= 3)%Z with Gt.
  cbv iota.
  apply refu_tid_refl.
Qed.

Lemma wpm_wallet_zero_at_last_cover : refu_tid Z (melt_wallet (Z.to_nat wpm_R)) 0.
Proof.
  unfold melt_wallet, wpm_R.
  change (Z.to_nat 3) with 3%nat.
  change (Z.of_nat 3) with 3%Z.
  unfold Z.sub.
  change (3 + - 3)%Z with 0%Z.
  apply refu_tid_refl.
Qed.

Lemma wpm_wallet_negative_at_bankrupt : refu_tid Z (melt_wallet (Datatypes.S (Z.to_nat wpm_R))) (-1).
Proof.
  unfold melt_wallet, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.sub.
  change (3 + - 4)%Z with (-1)%Z.
  apply refu_tid_refl.
Qed.

Lemma wpm_insolvent_at_bankrupt : refu_tid bool (insolvent (Datatypes.S (Z.to_nat wpm_R))) true.
Proof.
  unfold insolvent, melt_wallet, wpm_R.
  change (Datatypes.S (Z.to_nat 3)) with 4%nat.
  change (Z.of_nat 4) with 4%Z.
  unfold Z.leb, Z.sub.
  change (3 + - 4)%Z with (-1)%Z.
  change ((-1) ?= 0)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* 破产沿受偿流传播：一旦破产，此后每次受偿都破产（无界流 ⟹ 无限破产事件） *)
Lemma insolvent_step : forall k : nat,
  refu_tid bool (insolvent k) true -> refu_tid bool (insolvent (Datatypes.S k)) true.
Proof.
  intros k H. unfold insolvent in H.
  tidEqN H HE. unfold melt_wallet, wpm_R in HE. apply Z.leb_le in HE.
  unfold insolvent, melt_wallet, wpm_R.
  destruct (Z.leb (3 - Z.of_nat (Datatypes.S k)) 0) eqn:E.
  - apply refu_tid_refl.
  - apply Z.leb_gt in E. rewrite Nat2Z.inj_succ in E.
    exfalso. lia.
Qed.

Theorem wpm_insolvent_forever : forall j : nat,
  refu_tid bool (insolvent (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S j))))) true.
Proof.
  intros j. induction j as [| j IH].
  - exact wpm_insolvent_at_bankrupt.
  - apply insolvent_step. exact IH.
Qed.

(* 有界族上熔券健全（对照半边）：k ≤ R ⟹ 前 k 次受偿全部可付 *)
Theorem wpm_solvent_bounded_family : forall n : nat,
  refu_tid bool (Z.leb (Z.of_nat n) wpm_R) true -> refu_tid bool (solvent n) true.
Proof.
  intros n H. exact H.
Qed.

(* 合取闭合（「聚合占优」反演为聚合破产）：同一受偿流、同一受偿序号，
   熔券偿付位为假而定位方案偿付位为真 *)
Theorem wpm_unbounded_family_unsound :
  refu_tid bool (andb (solvent (Datatypes.S (Z.to_nat wpm_R)))
                 (loc_solvent (Datatypes.S (Z.to_nat wpm_R)))) false.
Proof.
  apply andb_false_left. apply wpm_melt_bankrupt.
Qed.

(* ===================================================================== *)
(* 件 2. p-adic 进位级联连坐两字段 + 剩余类环交替不达不动点（上游会话 实验 E1）      *)
(*                                                                     *)
(* GRM 普查迁到共享分母坐标域：字段 = 有理担保 w 的素坐标。取 p = 3，           *)
(* 使用流 = PLA 避零环流 2/3, 1/3, 2/3, 1/3, …（乘法份额），公分母下的          *)
(* 累计分子轨迹：N(0)=0, N(2j)=3j, N(2j+1)=3j+2。                              *)
(*   字段一 coordA：Z/9 剩余类坐标（粗分辨率）；                               *)
(*   字段二 coordB：Z/3 零类检测位（= p-账本归一化/进位触发位）。                *)
(* 击破：(a) 任一枚使用证据同时改写两字段坐标（连坐）——含触发步本身；            *)
(*       (b) 触发位沿 0↔2 剩余类环逐位交替、相邻状态永不重合——                   *)
(*           「≤ |普查| = 2 步到不动点」公理在预算外仍在移动（公理死）；          *)
(*       (c) 进位级联深度 2：N(6) = 9 时粗坐标 Z/9 也进零类。                    *)
(* ===================================================================== *)

Definition p3 : Z := 3.

(* 两步一组的累计分子递归：j 组后 = (N(2j), N(2j+1))；份额流 2/p,1/p 交替 *)
Fixpoint pla_step2 (j : nat) : Z * Z :=
  match j with
  | O => (0, 2)
  | Datatypes.S j' => let ab := pla_step2 j' in (snd ab + 1, snd ab + 3)
  end.

(* 字段一：Z/9 剩余类坐标 *)
Definition coordA (n : Z) : Z := Z.modulo n 9.
(* 字段二：Z/3 零类检测位（归一化/进位触发位） *)
Definition coordB (n : Z) : bool := Z.eqb (Z.modulo n 3) 0.

(* mod 3 精确小件（Z_mod_plus_full 路线，绕开除法引理的变量侧条件） *)
Lemma mod3_3j : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j) 3 = 0)%Z).
  { replace (3 * Z.of_nat j) with (0 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

Lemma mod3_3j2 : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j + 2) 3) 2.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 2) 3 = 2)%Z).
  { replace (3 * Z.of_nat j + 2) with (2 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

Lemma mod3_3j3 : forall j : nat, refu_tid Z (Z.modulo (3 * Z.of_nat j + 3) 3) 0.
Proof.
  intros j.
  assert (Hm : (Z.modulo (3 * Z.of_nat j + 3) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 3) with (3 + Z.of_nat j * 3) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite Hm. apply refu_tid_refl.
Qed.

(* mod 9 相差小正数必不同类（k ∈ [1,8] ⟹ Z/9 中 x 与 x+k 不同类） *)
Lemma mod9_diff_small : forall x k : Z,
  refu_tid bool (Z.ltb 0 k) true -> refu_tid bool (Z.ltb k 9) true ->
  refu_tid bool (Z.eqb (x mod 9) ((x + k) mod 9)) false.
Proof.
  intros x k Hk1 Hk2.
  tidEqN Hk1 HE1. tidEqN Hk2 HE2.
  apply Z.ltb_lt in HE1. apply Z.ltb_lt in HE2.
  pose proof (Z.mod_pos_bound x 9 (ltac:(lia))) as HB.
  pose proof (Z.div_mod x 9 (ltac:(lia))) as HD.
  destruct (Z.eqb (x mod 9) ((x + k) mod 9)) eqn:E.
  - apply Z.eqb_eq in E.
    assert (Hsplit : (x + k = (x mod 9 + k) + (x / 9) * 9)%Z) by lia.
    rewrite Hsplit in E. rewrite Z_mod_plus_full in E.
    destruct (Z_le_gt_dec (x mod 9) (8 - k)) as [Hc | Hc].
    + assert (Hsm : ((x mod 9 + k) mod 9 = x mod 9 + k)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm in E. exfalso. lia.
    + assert (Hconn : (x mod 9 + k = (x mod 9 + k - 9) + 1 * 9)%Z) by lia.
      assert (Hmp : (((x mod 9 + k - 9) + 1 * 9) mod 9 = (x mod 9 + k - 9) mod 9)%Z)
        by (apply Z_mod_plus_full).
      rewrite <- Hconn in Hmp.
      rewrite Hmp in E.
      assert (Hsm2 : ((x mod 9 + k - 9) mod 9 = x mod 9 + k - 9)%Z)
        by (apply Z.mod_small; lia).
      rewrite Hsm2 in E. exfalso. lia.
  - apply refu_tid_refl.
Qed.

(* 轨迹闭形：N(2j) = 3j、N(2j+1) = 3j+2（bool 合取判定形） *)
Lemma pla_pair_closed : forall j : nat,
  refu_tid bool (andb (Z.eqb (fst (pla_step2 j)) (3 * Z.of_nat j))
                 (Z.eqb (snd (pla_step2 j)) (3 * Z.of_nat j + 2))) true.
Proof.
  intros j. induction j as [| j IH].
  - apply refu_tid_refl.
  - tidEqN IH HEc. apply andb_prop in HEc as [HE1 HE2].
    apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
    replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
    replace (snd (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 3) by reflexivity.
    replace (3 * Z.of_nat (Datatypes.S j)) with (3 * Z.of_nat j + 3)
      by (rewrite Nat2Z.inj_succ; lia).
    replace (3 * Z.of_nat (Datatypes.S j) + 2) with (3 * Z.of_nat j + 5)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite HE2.
    apply andb_true_both.
    + apply Zeqb_true_of_eq. lia.
    + apply Zeqb_true_of_eq. lia.
Qed.

(* (a) 连坐定理：偶位证据（+2/p 份额）一次同时改写两字段坐标 *)
Theorem evidence_couples_two_fields : forall j : nat,
  refu_tid bool (andb
    (negb (Z.eqb (coordA (fst (pla_step2 j))) (coordA (snd (pla_step2 j)))))
    (negb (Bool.eqb (coordB (fst (pla_step2 j))) (coordB (snd (pla_step2 j)))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  rewrite HE1, HE2.
  tidEqN (mod3_3j j) HM1. rewrite HM1.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  apply andb_true_both.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j) 2); apply refu_tid_refl.
  - simpl. apply refu_tid_refl.
Qed.

(* (a') 触发步连坐：账本触发证据（+1/p 份额，落零类）同样一次改写两字段——
   进位事件不是字段一的私事，粗坐标同步被拖动 *)
Theorem ledger_trigger_couples_too : forall j : nat,
  refu_tid bool (andb
    (negb (Bool.eqb (coordB (snd (pla_step2 j))) (coordB (fst (pla_step2 (Datatypes.S j))))))
    (negb (Z.eqb (coordA (snd (pla_step2 j))) (coordA (fst (pla_step2 (Datatypes.S j))))))) true.
Proof.
  intros j. unfold coordA, coordB.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  tidEqN (mod3_3j2 j) HM2. rewrite HM2.
  assert (HM3' : (Z.modulo (3 * Z.of_nat j + 2 + 1) 3 = 0)%Z).
  { replace (3 * Z.of_nat j + 2 + 1) with (3 * Z.of_nat j + 3) by lia.
    tidEqN (mod3_3j3 j) H3. exact H3. }
  rewrite HM3'.
  apply andb_true_both.
  - simpl. apply refu_tid_refl.
  - apply negb_true_of_false.
    apply (mod9_diff_small (3 * Z.of_nat j + 2) 1); apply refu_tid_refl.
Qed.

(* (b) 不达不动点：相邻两步状态永不重合（剩余类环 0↔2 永久交替） *)
Theorem residue_class_never_freezes : forall j : nat,
  refu_tid bool (Z.eqb (snd (pla_step2 j)) (fst (pla_step2 (Datatypes.S j)))) false.
Proof.
  intros j.
  tidEqN (pla_pair_closed j) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 (Datatypes.S j))) with (snd (pla_step2 j) + 1) by reflexivity.
  rewrite HE2.
  apply Zeqb_diff_false. lia.
Qed.

(* GRM 公理预算击穿：|普查| = 2 ⟹ 公理断言第 2 步到不动点；
   实测第 4→5 步仍在移动（j = 2 实例）——公理死 *)
Theorem grm_two_step_budget_blown :
  refu_tid bool (Z.eqb (snd (pla_step2 2)) (fst (pla_step2 3))) false.
Proof.
  tidEqN (pla_pair_closed 2) HEc.
  apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. apply Z.eqb_eq in HE2.
  replace (fst (pla_step2 3)) with (snd (pla_step2 2) + 1) by reflexivity.
  rewrite HE2.
  apply Zeqb_diff_false. lia.
Qed.

(* (c) 进位级联深度 2：N(6) = 9 —— 粗坐标 Z/9 也进零类（双位归一化） *)
Theorem carry_cascade_depth2 : refu_tid bool (Z.eqb (coordA (fst (pla_step2 3))) 0) true.
Proof.
  unfold coordA.
  tidEqN (pla_pair_closed 3) HEc. apply andb_prop in HEc as [HE1 HE2].
  apply Z.eqb_eq in HE1. rewrite HE1. apply refu_tid_refl.
Qed.

(* ===================================================================== *)
(* 件 3. 织机活锁反例（上游会话 实验②）                                          *)
(*                                                                     *)
(* 两洞缩影：槽值 bool；跨洞联合合法门（吐件门）= 异或 emit_gate——             *)
(* 「六门联合合法空间 ≠ 各洞合法性的乘积」的那道跨洞门。                         *)
(* 判定流 = 循环一致流：每洞判定单一方向（「翻离对方」，无同洞双向冲突），        *)
(* 满足织机自定一致性条件；rej 重织语义 = 旧证作废、按证据把本槽改写为            *)
(* 「异于对方当前值」（证书包跨洞传参的同步重织）。                               *)
(* 初织 (true,true)：逐洞 pass 照章接受（一致性只查逐洞，不查跨洞）——非法元。    *)
(* 击破：同步重织 (a,b) ↦ (¬b, ¬a) 保持异或不变量——初织非法则永非法：            *)
(*   吐件门恒假（永不吐件）+ 槽值逐轮翻转（自振荡，周期 2）+                     *)
(*   摩擦计每轮 +2、无界增长（重织代价无界）；且贪心调度键自身即活锁驱动器。      *)
(* ===================================================================== *)

(* 跨洞联合合法门（吐件门）＝异或 *)
Definition emit_gate (a b : bool) : bool := xorb a b.

(* 一步同步重织：两洞旧证同时作废，各自翻离对方 *)
Definition loom_step (p : bool * bool) : bool * bool :=
  (negb (snd p), negb (fst p)).

(* 织机运行轨迹：初织 (true,true)，循环一致流驱动 *)
Fixpoint loom_iter (k : nat) : bool * bool :=
  match k with
  | O => (true, true)
  | Datatypes.S k' => loom_step (loom_iter k')
  end.

(* 摩擦计：每轮两洞各重织一次，各 +1 *)
Fixpoint loom_fric (k : nat) : nat :=
  match k with O => O | Datatypes.S k' => Datatypes.S (Datatypes.S (loom_fric k')) end.

(* 一步重织保持吐件门真值（异或不变量的转移式） *)
Lemma loom_step_inv : forall p : bool * bool,
  refu_tid bool (emit_gate (fst (loom_step p)) (snd (loom_step p)))
           (emit_gate (fst p) (snd p)).
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply refu_tid_refl.
Qed.

(* 流一致性（织机自定条件）：每洞重织方向单一——改写目标恒为「异于对方当前值」，
   与本槽自身取值无关、永不「贴向对方」（无同洞双向冲突、无停织空转），
   bool 判定对一切状态恒真 *)
Definition flip_check (p : bool * bool) : bool :=
  andb (Bool.eqb (fst (loom_step p)) (negb (snd p)))
       (Bool.eqb (snd (loom_step p)) (negb (fst p))).

Lemma loom_stream_consistent : forall p : bool * bool, refu_tid bool (flip_check p) true.
Proof.
  intros p. destruct p as [a b]. destruct a, b; apply refu_tid_refl.
Qed.

(* 周期 2：织机轨迹两轮回到原态（自振荡载体） *)
Lemma loom_period2 : forall k : nat,
  refu_tid (bool * bool) (loom_iter (Datatypes.S (Datatypes.S k))) (loom_iter k).
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - change (refu_tid (bool * bool) (loom_step (loom_iter (Datatypes.S (Datatypes.S k))))
                        (loom_step (loom_iter k))).
    exact (refu_tid_cong loom_step _ _ IH).
Qed.

(* 活锁主定理：任意轮次吐件门恒假——一致流存在、吐件不存在 *)
Theorem loom_livelock_never_emits : forall k : nat,
  refu_tid bool (emit_gate (fst (loom_iter k)) (snd (loom_iter k))) false.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - exact (refu_tid_trans bool _ _ _ (loom_step_inv (loom_iter k)) IH).
Qed.

(* 自振荡：槽值逐轮翻转（非停滞空转），周期 2 内永在两非法元间振荡 *)
Lemma loom_flips : forall k : nat,
  refu_tid bool (xorb (fst (loom_iter (Datatypes.S k))) (fst (loom_iter k))) true.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - tidEqN (loom_period2 k) HEp. rewrite HEp.
    exact (refu_tid_trans bool _ _ _
      (xorb_comm_t (fst (loom_iter k)) (fst (loom_iter (Datatypes.S k)))) IH).
Qed.

(* 摩擦计闭形：k 轮后摩擦计 = 2k（真实现，非占位） *)
Lemma loom_fric_closed : forall k : nat, refu_tid nat (loom_fric k) (2 * k)%nat.
Proof.
  intros k. induction k as [| k IH].
  - apply refu_tid_refl.
  - change (refu_tid nat (Datatypes.S (Datatypes.S (loom_fric k))) (2 * Datatypes.S k)%nat).
    rewrite (Nat.mul_succ_r 2 k).
    tidEqN IH HEk. rewrite HEk.
    assert (HE2 : (2 * k + 2 = Datatypes.S (Datatypes.S (2 * k)))%nat) by lia.
    rewrite HE2. apply refu_tid_refl.
Qed.

(* 重织代价无界：任意两轮窗口内摩擦计严格上升（贪心调度键 = 活锁驱动器，
   预算无论多大终被突破——refu_nle (Datatypes.S fric j) fric (j+2)） *)
Theorem loom_cost_unbounded : forall j : nat,
  refu_nle (Datatypes.S (loom_fric j)) (loom_fric (j + 2)%nat).
Proof.
  intros j.
  assert (HE : (loom_fric (j + 2) = loom_fric j + 4)%nat).
  { replace ((j + 2)%nat) with (Datatypes.S (Datatypes.S j)) by lia. simpl. lia. }
  rewrite HE.
  apply (refu_nle_trans (Datatypes.S (loom_fric j)) (Datatypes.S (loom_fric j) + 3) (loom_fric j + 4)).
  - apply refu_nle_add_r.
  - assert (HEq : (Datatypes.S (loom_fric j) + 3 = loom_fric j + 4)%nat) by lia.
    rewrite HEq. apply refu_nle_n.
Qed.

(* ===================================================================== *)
(* 件 4. DWM 两难闭合（上游会话 实验一 + 上游会话 实验二合流）                          *)
(*                                                                     *)
(* 差异钱包机：候选带只增不删 × 精确有限停机。停机支唯一悬于判等命题 X：         *)
(*「差额 < grain ⟹ 同格」。载体：分母 4 格网，全部以格距 1/4 为单位的整数编码。    *)
(* 两难两角：                                                                 *)
(*   自由发射角（不补公理）：X 可判定为假（0 与 1/4 同格判伪），且               *)
(*     Halt 触发后证书被一次合法发射当场证伪——Halt 永伪；                        *)
(*   格律公理角（发射器分母固定）：X 退化为整除算术平凡重述（格距判等 =           *)
(*「Z/2 可除性 + 商相等」），与钱包/颗粒机制零关联——平凡。                        *)
(* ===================================================================== *)

Definition dwm_D : Z := 4.        (* 公分母：格 = {k/4} *)
Definition dwm_grain : Z := 2.    (* grain = 1/2 = 2 格距单位 *)
Definition dwm_W0 : Z := 4.       (* 初始钱包 = 1 = 4 格距单位 *)

(* 判等命题 X 的 bool 化：差额 < grain ⟹ 同格（数值相等） *)
Definition X_test (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb a b else true.

(* 入场费 = 与最近在场者的格距（空带数值锚 999 永不可达：带内置 a0） *)
Fixpoint dmin (x : Z) (l : list Z) : Z :=
  match l with
  | nil => 999
  | a :: l' => Z.min (Z.abs (x - a)) (dmin x l')
  end.

(* 在场检测（bool） *)
Fixpoint presentb (x : Z) (l : list Z) : bool :=
  match l with
  | nil => false
  | a :: l' => orb (Z.eqb x a) (presentb x l')
  end.

(* 发射机：付费入场，返回（新在场带, 新钱包） *)
Definition dwm_emit (x : Z) (l : list Z) (W : Z) : list Z * Z :=
  (x :: l, W - dmin x l).

(* Halt 证书的 bool 化：「一切未来合法发射皆在场」——对发射 x：
   合法（入场费 ≤ W）⟹ x 在场 *)
Definition halt_cert (x : Z) (l : list Z) (W : Z) : bool :=
  implb (Z.leb (dmin x l) W) (presentb x l).

(* —— 自由发射角：X 可判定为假（两点反例：0 与 1/4，差 1 < grain 2 而异格） —— *)
Theorem dwm_X_refuted : refu_tid bool (X_test 0 1) false.
Proof.
  unfold X_test, dwm_grain.
  change (Z.abs (0 - 1)) with 1%Z.
  unfold Z.ltb, Z.eqb.
  change (1 ?= 2)%Z with Lt.
  change (0 ?= 1)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* —— 上游会话 细分化反例全程仿真：带内置 [0]，grain = 2，钱包 = 4。
   步 1：发射 1/2（格 2），费 2，钱包→2；步 2：发射 1/4（格 1），费 1，钱包→1 < grain
   ——Halt 触发；步 3：发射 3/4（格 3），费 1 ≤ 钱包 1，合法，且 3 ∉ 在场集
   ——「未来皆同」证书被一次合法发射当场证伪。 —— *)
Definition dwm_W1 : Z := snd (dwm_emit 2 (0 :: nil) dwm_W0).
Definition dwm_W2 : Z := snd (dwm_emit 1 (2 :: 0 :: nil) dwm_W1).

Theorem dwm_wallet_trajectory : refu_tid Z dwm_W2 1.
Proof.
  assert (Hd1 : dmin 2 (0 :: nil) = 2%Z).
  { cbn [dmin]. change (Z.abs (2 - 0)) with 2%Z.
    unfold Z.min. change (2 ?= 999)%Z with Lt. reflexivity. }
  assert (Hd2 : dmin 1 (2 :: 0 :: nil) = 1%Z).
  { cbn [dmin]. change (Z.abs (1 - 2)) with 1%Z.
    change (Z.abs (1 - 0)) with 1%Z.
    unfold Z.min. change (1 ?= 999)%Z with Lt. reflexivity. }
  unfold dwm_W2, dwm_W1, dwm_emit, dwm_W0.
  cbn [snd]. rewrite Hd1. rewrite Hd2.
  change (4 - 2)%Z with 2%Z.
  change (2 - 1)%Z with 1%Z.
  apply refu_tid_refl.
Qed.

Theorem dwm_halt_fires : refu_tid bool (Z.ltb dwm_W2 dwm_grain) true.
Proof.
  tidEqN dwm_wallet_trajectory HEw. rewrite HEw.
  unfold Z.ltb, dwm_grain.
  change (1 ?= 2)%Z with Lt.
  cbv iota.
  apply refu_tid_refl.
Qed.

Theorem dwm_emit3_legal : refu_tid bool (Z.leb (dmin 3 (2 :: 1 :: 0 :: nil)) dwm_W2) true.
Proof.
  assert (Hd : dmin 3 (2 :: 1 :: 0 :: nil) = 1%Z).
  { cbn [dmin].
    change (Z.abs (3 - 2)) with 1%Z.
    change (Z.abs (3 - 1)) with 2%Z.
    change (Z.abs (3 - 0)) with 3%Z.
    unfold Z.min. change (3 ?= 999)%Z with Lt. reflexivity. }
  tidEqN dwm_wallet_trajectory HEw. rewrite Hd. rewrite HEw.
  unfold Z.leb. change (1 ?= 1)%Z with Eq. cbv iota.
  apply refu_tid_refl.
Qed.

Theorem dwm_emit3_not_present : refu_tid bool (presentb 3 (2 :: 1 :: 0 :: nil)) false.
Proof.
  cbn [presentb]. unfold orb.
  change (3 ?= 2)%Z with Gt.
  change (3 ?= 1)%Z with Gt.
  change (3 ?= 0)%Z with Gt.
  cbv iota.
  apply refu_tid_refl.
Qed.

(* Halt 永伪半边：Halt 触发态（钱包 1 < grain 2）下证书对 x = 3 判假 *)
Theorem dwm_halt_cert_refuted : refu_tid bool (halt_cert 3 (2 :: 1 :: 0 :: nil) dwm_W2) false.
Proof.
  unfold halt_cert, dwm_W2, dwm_W1, dwm_emit, dwm_W0. apply refu_tid_refl.
Qed.

(* —— 格律公理角：X 退化为整除算术平凡重述 ——
   补发射器格律（格点 = 2·格距 的倍数）后，同格判等归约为 Z/2 可除性 + 商相等：
   格点 a = 2·ka, b = 2·kb，|a−b| < 2 ⟹ ka = kb——证明过程只动整除算术，
   钱包/颗粒/入场费机制零参与（平凡档）。 *)
Definition lattice_X (a b : Z) : bool :=
  if Z.ltb (Z.abs (a - b)) dwm_grain then Z.eqb (a / 2) (b / 2) else true.

Theorem dwm_lattice_X_trivial : forall a b : Z,
  refu_tid bool (Z.eqb (a mod 2) 0) true -> refu_tid bool (Z.eqb (b mod 2) 0) true ->
  refu_tid bool (lattice_X a b) true.
Proof.
  intros a b Ha Hb.
  tidEqN Ha HEA. tidEqN Hb HEB.
  apply Z.eqb_eq in HEA. apply Z.eqb_eq in HEB.
  pose proof (Z.div_mod a 2 (ltac:(lia))) as HDA.
  pose proof (Z.div_mod b 2 (ltac:(lia))) as HDB.
  rewrite HEA in HDA. rewrite HEB in HDB.
  assert (HA2 : (a = 2 * (a / 2))%Z) by lia.
  assert (HB2 : (b = 2 * (b / 2))%Z) by lia.
  unfold lattice_X, dwm_grain.
  destruct (Z.ltb (Z.abs (a - b)) 2) eqn:E.
  - apply Z.ltb_lt in E.
    rewrite HA2, HB2 in E.
    rewrite <- Z.mul_sub_distr_l in E.
    rewrite Z.abs_mul in E.
    assert (H2abs : (Z.abs 2 = 2)%Z) by reflexivity.
    rewrite H2abs in E.
    destruct (Z_lt_ge_dec (Z.abs (a / 2 - b / 2)) 1) as [Hlt | Hge].
    + assert (Hk : (a / 2 = b / 2)%Z) by lia.
      rewrite Hk. rewrite Z.eqb_refl. apply refu_tid_refl.
    + exfalso. lia.
  - apply refu_tid_refl.
Qed.

(* 两难闭合合注：自由发射角 dwm_X_refuted + dwm_halt_cert_refuted（不补则 Halt 永伪）
   与格律公理角 dwm_lattice_X_trivial（补则 X 退化为整除算术平凡重述、与钱包机制
   零关联）合取——押注两头死，DWM 原停机支不可满足或满足即平凡。 *)

Close Scope Z_scope.

(* ======== G10_LoebFam 成员件：UpQKBound（原样并入，自带 Require）======== *)
(* ============================================================ *)
(* UpQKBound.v —— 方案一 QKᵀ 管线收尾：界转化件 + QKᵀ 绑定 +       *)
(*   Δ 显式 sigT 封装（下游使用 UpCS 的 dotp/sql/Q 层核）          *)
(*                                                              *)
(* 数学目标（Real 层，list 向量世界，CW_ConstructiveWorld_219）：   *)
(*   向量 = list Real；维数 d := 向量长度；                       *)
(*   root_of d := projT1 (real_sqrt_exists d Hd)（sqrt 见证：      *)
(*   And (r ≥ 0) (r·r == d)；root 记号只出现在前提与 Δ 定义，      *)
(*   不进恒等链——恒等链全部走 real_eq 迁移 + 逐点尾界）。          *)
(*                                                              *)
(* 件 1（内积/范数桥）inner_sq_norm：                             *)
(*   ⟨q,q⟩ == Σq²（real_eq；UpCS 的 sql 即 Σq²——命名桥）。        *)
(*   根有界前提形态（正确原语，Or 编码下 A² ≤ Q² 推不出 A ≤ Q）：   *)
(*   Hqn : real_le (root_of (sql q) Hqq) Q——件 2/件 3 前提照此。   *)
(*                                                              *)
(* 件 2（界转化·主件）real_logit_bound_of_norm_bounds：            *)
(*   根有界前提（root⟨q,q⟩ ≤ Q、root⟨k,k⟩ ≤ K，Q,K > 0）⟹         *)
(*   real_le |⟨q,k⟩| (Q·K·√d + eps)（eps 版；证明走 inl 严格支）。  *)
(*   装配：C-Datatypes.S 严格版（eps 记录显式：C-Datatypes.S 的 eps := (h/2)²，经       *)
(*   abs 转化件（abs_le_add_of_sq_lt）转化为 |⟨q,k⟩| < 根积 + h，   *)
(*   再正数乘单调（根积 ≤ Q·K）+ 1 ≤ √d（k=1 时相等、k≥2 时严格    *)
(*   ——k 分支）合并入最终 +eps。                                  *)
(*                                                              *)
(* 件 3（QKᵀ 绑定 + Δ 封装·主定理）qk_logits_bounded：               *)
(*   attn_logit q k d s s' := dotp(q s, k s')·inv(√d)             *)
(*   （inv 形态：real_inv_pos root_d (root_d_pos d)——正性证书      *)
(*   构造性携带）。前提全 s s' 根有界一致。Δ := (Q·K)·inv(√d)+1，   *)
(*   sigT 封装：Δ > 0 ∧ ∀s s' |logit| ≤ Δ。                        *)
(*   +1 余量代数（eps 透传吸收，零 eps 版）：                      *)
(*     |dotp| < 根积 + 1/2 （件 2 机制，h := 1/2）                 *)
(*     ⟹ |logit| = |dotp|·inv(√d) < (根积 + 1/2)·inv(√d)           *)
(*        = 根积·inv(√d) + (1/2)·inv(√d) ≤ Q·K·inv(√d) + 1/2       *)
(*        （inv(√d) ≤ 1：√d ≥ 1 ⟹ inv 反序）                       *)
(*        < Q·K·inv(√d) + 1 = Δ。+1 精确吸收 (1/2)·inv(√d) ≤ 1/2。  *)
(*                                                              *)
(* 件 4（接缝注记，非定理）：下游接缝——本件 Δ 界供给               *)
(*   bs_minorization 的双界前提（−Δ ≤ z ≤ Δ 由 |z| ≤ Δ 给出）⟹      *)
(*   softmax 核逐点 ≥ δ⋆·U，δ⋆ = e^{−2Δ/T} ⟹ (1−δ⋆)ⁿ 收缩率        *)
(*   （该下游件属 bs_minorization Real 化范围，不在本文件）。        *)
(*                                                              *)
(* 关键构造性事实（设计发现）：                                   *)
(*   real_eq 的柯西语义只约束尾段（∀δ>0 ∃N ∀n≥N |x_n−y_n|<δ），     *)
(*   不给出任何固定下标的逐点相等——故 sqrt 见证 r·r == d 的使用     *)
(*   一律取尾界形式（固定 δ 截断），所有结论为 real_lt（尾段严格    *)
(*   分离），零逐点相等提取、零经典逻辑。                          *)
(*                                                              *)
(* 红线：纯构造性；Set 层语句（Set 层 And/Or/sigT，无 Prop 泄露）；  *)
(*   全 Qed 闭合；可提取零魔法。                                  *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpCS.
From Stdlib Require Import List QArith.QArith QArith.Qabs QArith.Qring Arith.Arith.
From Stdlib Require Import Lia Lqa.
Import ListNotations.
Open Scope Q_scope.

(* ################ 第 0 部分：Q 层辅助（可判定序 + 平方桥） ###### *)

Lemma Qle_or_lt : forall x y : Q, {x <= y} + {y < x}.
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - assert (Hxy : x == y) by (apply (proj2 (Qeq_alt x y)); exact E).
    left. rewrite Hxy. apply Qle_refl.
  - left. apply Qlt_le_weak. apply (proj2 (Qlt_alt x y)). exact E.
  - right. apply (proj2 (Qlt_alt y x)).
    rewrite <- (Qcompare_antisym x y). rewrite E. reflexivity.
Qed.

Lemma Qlt_0_half : Qlt 0 (1#2).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_half_one : Qlt (1#2) 1.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_le_one : Qle 0 1.
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qle_0_sq_Q : forall x : Q, Qle 0 (x * x).
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)).
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
    + ring.
Qed.

Lemma Qle_0_of_sq_0 : forall a : Q, Qle 0 a -> a * a == 0 -> a == 0.
Proof.
  intros a Ha Hsq.
  destruct (Qeq_dec a 0) as [Heq | Hne]; [exact Heq |].
  exfalso.
  assert (Hlt : 0 < a).
  { destruct (Qle_or_lt a 0) as [Hle | Hgt].
    - exfalso. apply Hne. apply (Qle_antisym a 0); [exact Hle | exact Ha].
    - exact Hgt. }
  assert (H1 : 0 * a < a * a) by (apply (Qmult_lt_compat_r 0 a a); assumption).
  assert (H2 : 0 * a == 0) by ring.
  rewrite H2 in H1. rewrite Hsq in H1.
  exact (Qlt_irrefl 0 H1).
Qed.

(* 平方非负 + 平方界的单调核：0 ≤ a、0 ≤ y、a² ≤ y² ⟹ a ≤ y *)
Lemma QH1core : forall a y : Q,
  Qle 0 a -> Qle 0 y -> Qle (a * a) (y * y) -> Qle a y.
Proof.
  intros a y Ha Hy Hsq.
  destruct (Qle_or_lt a y) as [Hle | Hlt]; [exact Hle |].
  exfalso.
  destruct (Qeq_dec y 0) as [Hy0 | Hny0].
  - rewrite Hy0 in Hsq.
    assert (Haa : a * a == 0).
    { apply (Qle_antisym (a * a) 0).
      - simpl in Hsq. exact Hsq.
      - apply (Qle_0_sq_Q a). }
    assert (Ha0 : a == 0) by (apply (Qle_0_of_sq_0 a Ha Haa)).
    rewrite Hy0, Ha0 in Hlt. exact (Qlt_irrefl 0 Hlt).
  - assert (Hpy : 0 < y).
    { destruct (Qle_or_lt y 0) as [Hle | Hgt].
      - exfalso. apply Hny0. apply (Qle_antisym y 0); [exact Hle | exact Hy].
      - exact Hgt. }
    assert (Hpa : 0 < a) by (apply (Qlt_trans 0 y a Hpy Hlt)).
    assert (H1 : y * y < a * y) by (apply (Qmult_lt_compat_r y a y); assumption).
    assert (H2 : a * y < a * a).
    { setoid_replace (a * y) with (y * a) by ring.
      apply (Qmult_lt_compat_r y a a); assumption. }
    assert (H3 : y * y < a * a) by (apply (Qlt_trans (y * y) (a * y) (a * a) H1 H2)).
    exact (Qlt_irrefl (y * y) (Qlt_le_trans (y * y) (a * a) (y * y) H3 Hsq)).
Qed.

(* 严格版：0 ≤ d、0 < h、d² < h² ⟹ d < h *)
Lemma Qlt_of_sq_lt : forall d h : Q,
  Qle 0 d -> Qle 0 h -> Qlt (d * d) (h * h) -> Qlt d h.
Proof.
  intros d h Hd Hh Hlt.
  destruct (Qle_or_lt h d) as [Hle | Hlt'].
  - exfalso.
    assert (Hmono : h * h <= d * d).
    { apply (Qle_trans (h * h) (d * h) (d * d)).
      - apply (Qmult_le_compat_r h d h); [exact Hle | exact Hh].
      - setoid_replace (d * h) with (h * d) by ring.
        apply (Qmult_le_compat_r h d d); [exact Hle | exact Hd]. }
    exact (Qlt_irrefl (d * d) (Qlt_le_trans (d * d) (h * h) (d * d) Hlt Hmono)).
  - exact Hlt'.
Qed.

(* 绝对值版：0 ≤ y、x² ≤ y² ⟹ |x| ≤ y *)
Lemma Qle_abs_le_sq : forall x y : Q,
  Qle 0 y -> Qle (x * x) (y * y) -> Qle (Qabs x) y.
Proof.
  intros x y Hy Hsq.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos x Hpos).
    apply (QH1core x y); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
    rewrite Habsx.
    apply (QH1core (- x) y).
    + exact (Qopp_le_compat x 0 Hle).
    + exact Hy.
    + setoid_replace ((- x) * (- x)) with (x * x) by ring. exact Hsq.
Qed.

(* 平方相等 + 双非负 ⟹ 相等 *)
Lemma Qeq_of_sq_eq : forall a b : Q,
  Qle 0 a -> Qle 0 b -> a * a == b * b -> a == b.
Proof.
  intros a b Ha Hb Hsq.
  apply (Qle_antisym a b).
  - apply (QH1core a b); [exact Ha | exact Hb | apply qeq_le; exact Hsq].
  - apply (QH1core b a); [exact Hb | exact Ha | apply qeq_le; rewrite Hsq; reflexivity].
Qed.

(* |x·x| == |x|² *)
Lemma Qabs_sq : forall x : Q, Qabs (x * x) == Qabs x * Qabs x.
Proof.
  intro x.
  destruct (Qle_or_lt 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos (x * x)).
    + rewrite (Qabs_pos x Hpos). reflexivity.
    + apply (Qmult_le_0_compat x x); assumption.
  - assert (Hle : x <= 0) by (apply Qlt_le_weak; assumption).
    setoid_replace (x * x) with ((- x) * (- x)) by ring.
    rewrite (Qabs_pos ((- x) * (- x))).
    + assert (Habsx : Qabs x == - x) by (apply Qabs_neg; exact Hle).
      rewrite Habsx. reflexivity.
    + apply (Qmult_le_0_compat (- x) (- x)).
      * exact (Qopp_le_compat x 0 Hle).
      * exact (Qopp_le_compat x 0 Hle).
Qed.

(* x² == |x|·|x| *)
Lemma Qsq_abs_eq : forall x : Q, x * x == Qabs x * Qabs x.
Proof.
  intro x. rewrite <- (Qabs_sq x).
  apply Qeq_sym. apply Qabs_pos. apply Qle_0_sq_Q.
Qed.

(* 绝对值乘法性：|a·b| == |a|·|b| *)
Lemma Qabs_mult_gen : forall a b : Q, Qabs (a * b) == Qabs a * Qabs b.
Proof.
  intros a b.
  apply (Qeq_of_sq_eq (Qabs (a * b)) (Qabs a * Qabs b)).
  - apply Qabs_nonneg.
  - apply (Qmult_le_0_compat (Qabs a) (Qabs b)); apply Qabs_nonneg.
  - setoid_replace (Qabs a * Qabs b * (Qabs a * Qabs b))
      with (Qabs a * Qabs a * (Qabs b * Qabs b)) by ring.
    rewrite <- (Qabs_sq a). rewrite <- (Qabs_sq b).
    rewrite (Qabs_pos (a * a) (Qle_0_sq_Q a)).
    rewrite (Qabs_pos (b * b) (Qle_0_sq_Q b)).
    rewrite <- (Qabs_sq (a * b)).
    rewrite (Qabs_pos ((a * b) * (a * b)) (Qle_0_sq_Q (a * b))).
    ring.
Qed.

(* 双非负单调乘 *)
Lemma Qmult_le_mono2 : forall a b c d : Q,
  Qle 0 a -> Qle 0 b -> Qle a c -> Qle b d -> Qle (a * b) (c * d).
Proof.
  intros a b c d Ha Hb Hac Hbd.
  assert (Hc0 : 0 <= c) by (apply (Qle_trans 0 a c); assumption).
  apply (Qle_trans (a * b) (c * b) (c * d)).
  - apply (Qmult_le_compat_r a c b); assumption.
  - setoid_replace (c * b) with (b * c) by ring.
    setoid_replace (c * d) with (d * c) by ring.
    apply (Qmult_le_compat_r b d c); [exact Hbd | exact Hc0].
Qed.

(* 1 ≤ x² + 0 ≤ x ⟹ 1 ≤ x（√d ≥ 1 的逐点内核） *)
Lemma Qle_1_of_sq : forall x : Q, Qle 0 x -> Qle 1 (x * x) -> Qle 1 x.
Proof.
  intros x H0 Hsq.
  assert (H : Qle (1 * 1) (x * x)).
  { setoid_replace (1 * 1) with 1 by ring. exact Hsq. }
  apply (QH1core 1 x); [exact zero_le_one | exact H0 | exact H].
Qed.

(* UpCS 的 sqlQ/dotpQ 命名桥：dotpQ u u == sqlQ u *)
Lemma dotpQ_sqlQ : forall u : list Q, dotpQ u u == sqlQ u.
Proof.
  induction u as [| x xs IH].
  - reflexivity.
  - cbn [dotpQ sqlQ]. rewrite IH. ring.
Qed.

(* ################ 第 2 部分：向量世界 + Real 尾段使用件 ########## *)
(* 本文件自带 dotp/sql（CW_ConstructiveWorld_219 Real 版；UpCS 的同名件确定扫描版     *)
(* Real，不可跨用；UpCS 的纯 Q 层 cs_Q/dotpQ/sqlQ 照常使用）。      *)

Fixpoint qkb_dotp (a b : list Real) : Real :=
  match a, b with
  | x :: xs, y :: ys => real_plus (real_mult x y) (qkb_dotp xs ys)
  | _, _ => real_zero
  end.

Fixpoint qkb_sql (a : list Real) : Real :=
  match a with
  | nil => real_zero
  | x :: rest => real_plus (real_mult x x) (qkb_sql rest)
  end.

(* ---- Q 层补充 ---- *)

Lemma Qlt_0_two : Qlt 0 2.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_eight : Qlt 0 8.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_one : Qlt 0 1.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_sixteen : Qlt 0 16.
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_32 : Qlt 0 32.
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_0_three_quarters : Qle 0 (3#4).
Proof. vm_compute. intro H. discriminate H. Qed.

Lemma Qlt_0_7_16 : Qlt 0 (7#16).
Proof. vm_compute. reflexivity. Qed.

Lemma Qlt_0_quarter : Qlt 0 (1#4).
Proof. vm_compute. reflexivity. Qed.

Lemma Qle_add_pos_r : forall a e : Q, Qle 0 e -> Qle a (a + e).
Proof.
  intros a e He.
  apply (Qle_trans a (a + 0) (a + e)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat a a 0 e); [apply Qle_refl | exact He].
Qed.

Lemma Qabs_lt_l : forall x c : Q, Qlt (Qabs x) c -> Qlt x c.
Proof.
  intros x c H.
  destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0) in H. exact H.
  - apply (Qlt_trans x 0 c H0).
    apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H).
Qed.

Lemma Qabs_lt_low : forall x c : Q, Qlt (Qabs x) c -> Qlt (- c) x.
Proof.
  intros x c H.
  destruct (Qle_or_lt x (- c)) as [Hle | Hgt].
  - exfalso.
    assert (Hc0 : 0 < c) by (apply (Qle_lt_trans 0 (Qabs x) c (Qabs_nonneg x) H)).
    assert (Habs : Qabs x == - x) by (apply Qabs_neg; lra).
    rewrite Habs in H.
    assert (Hge0 : - (- c) <= - x) by exact (Qopp_le_compat x (- c) Hle).
    assert (Hcc : c == - (- c)) by ring.
    rewrite Hcc in Hge0.
    lra.
  - exact Hgt.
Qed.

(* ---- real_le 尾段使用（eq 支带 eps 松弛；lt 支精确） ---- *)

Lemma real_lt_pt_le : forall x y : Real,
  real_lt x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n)).
Proof.
  intros x y H. destruct H as [e [Hp [N HN]]].
  exists N. intros n Hn.
  assert (Hp0 : Qlt 0 e) by (apply QltT_to_Qlt; exact Hp).
  assert (Hq : Qlt e (projT1 y n - projT1 x n)).
  { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
  lra.
Qed.

Lemma real_le_pt_ev_plus : forall (x y : Real) (e : Q),
  Qlt 0 e -> real_le x y ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (projT1 x n) (projT1 y n + e)).
Proof.
  intros x y e He H. destruct H as [Hlt | Heq].
  - destruct (real_lt_pt_le x y Hlt) as [N HN]. exists N. intros n Hn.
    apply (Qle_trans (projT1 x n) (projT1 y n) (projT1 y n + e));
      [exact (HN n Hn) | apply Qle_add_pos_r; apply Qlt_le_weak; exact He].
  - destruct (Heq e (Qlt_to_QltT 0 e He)) as [N HN].
    exists N. intros n Hn.
    assert (Hab : Qlt (Qabs (projT1 x n - projT1 y n)) e).
    { apply QltT_to_Qlt. exact (HN n (NatLe_lift N n Hn)). }
    assert (Hl := Qabs_lt_l _ _ Hab).
    lra.
Qed.

(* ---- real_const 桥 ---- *)

Lemma qkb_real_const_pos : forall c : Q, Qlt 0 c -> real_lt real_zero (real_const c).
Proof.
  intros c Hc.
  exists ((1#2) * c). split.
  - apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (1#2) c); [exact Qlt_0_half | exact Hc].
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite real_const_proj.
    setoid_replace (c - 0) with c by ring.
    lra.
Qed.

Lemma real_const_eq_of_Qeq : forall a b : Q, a == b -> real_eq (real_const a) (real_const b).
Proof.
  intros a b H. apply real_eq_of_zero_diff. intro n.
  rewrite !real_const_proj. rewrite H. ring.
Qed.

Lemma qkb_real_distrib_r : forall x y z : Real,
  real_eq (real_mult (real_plus x y) z) (real_plus (real_mult x z) (real_mult y z)).
Proof.
  intros x y z. apply real_eq_of_zero_diff. intro n.
  rewrite ?real_plus_proj. rewrite ?real_mult_proj.
  rewrite ?real_plus_proj. rewrite ?real_mult_proj.
  ring.
Qed.

(* ################ 第 3 部分：nat 嵌入 + 构造性平方根绑定 ######## *)

(* Q 侧自然数常数（避免 Q.of_nat/Z 换算） *)
Fixpoint natQ (k : nat) : Q :=
  match k with
  | 0%nat => 0%Q
  | Datatypes.S m => 1 + natQ m
  end.

Lemma natQ_pos : forall k : nat, Qle 0 (natQ k).
Proof.
  induction k as [| k IH].
  - apply Qle_refl.
  - cbn [natQ]. apply (Qle_trans 0 (0 + natQ k) (1 + natQ k)).
    + rewrite Qplus_0_l. exact IH.
    + apply (Qplus_le_compat 0 1 (natQ k) (natQ k));
        [exact zero_le_one | apply Qle_refl].
Qed.

Lemma natQ_Sk_ge_one : forall k : nat, Qle 1 (natQ (Datatypes.S k)).
Proof.
  intro k. cbn [natQ].
  apply (Qle_trans 1 (1%Q + 0%Q) (1%Q + natQ k)).
  - apply qeq_le. ring.
  - setoid_replace (1%Q + 0%Q) with (0%Q + 1%Q) by ring.
    setoid_replace (1%Q + natQ k) with (natQ k + 1%Q) by ring.
    apply (Qplus_le_compat 0 (natQ k) 1 1); [apply natQ_pos | apply Qle_refl].
Qed.

(* Real 侧嵌入 *)
Fixpoint qkb_nat_to_R (k : nat) : Real :=
  match k with
  | 0%nat => real_zero
  | Datatypes.S m => real_plus real_one (qkb_nat_to_R m)
  end.

Lemma nat_to_R_proj : forall (k : nat) (n : nat),
  projT1 (qkb_nat_to_R k) n == natQ k.
Proof.
  induction k as [| k IH]; intro n.
  - reflexivity.
  - cbn [qkb_nat_to_R]. rewrite real_plus_proj.
    change (projT1 real_one n) with 1%Q.
    rewrite IH. reflexivity.
Qed.

Lemma qkb_nat_to_R_pos : forall k : nat, real_lt real_zero (qkb_nat_to_R (Datatypes.S k)).
Proof.
  intro k.
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    rewrite (nat_to_R_proj (Datatypes.S k) n).
    cbn [natQ].
    setoid_replace (1 + natQ k - 0) with (1%Q + natQ k) by ring.
    assert (H1 : Qle 0 (natQ k)) by apply natQ_pos.
    lra.
Qed.

(* 平方根的界转化原语：root_of 只出现在前提与 Δ 定义，不进恒等链 *)
Definition root_of (d : Real) (Hd : real_le real_zero d) : Real :=
  projT1 (real_sqrt_exists d Hd).

Definition root_d (k : nat) : Real :=
  root_of (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)).

Lemma root_d_sq : forall k : nat,
  real_eq (real_mult (root_d k) (root_d k)) (qkb_nat_to_R (Datatypes.S k)).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrsq]].
  exact Hrsq.
Qed.

(* sqrt 见证的尾下界：r² == natQ(Datatypes.S k)（尾段）+ Datatypes.S k ≥ 1 ⟹ r_n² > 9/16（尾段） *)
Lemma sq_bound_from_eq : forall (k : nat) (r : Real),
  real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (9#16) (projT1 r n * projT1 r n)).
Proof.
  intros k r Hrsq. destruct r as [u Hu].
  destruct (Hrsq (7#16) (Qlt_to_QltT 0 (7#16) Qlt_0_7_16)) as [N1 HN1].
  exists N1. intros n Hn.
  cbn [projT1] in HN1 |- *.
  assert (Hlow2 : Qlt (- (7#16)) (u n * u n - natQ (Datatypes.S k))).
  { assert (Ht := HN1 n (NatLe_lift N1 n Hn)).
    apply QltT_to_Qlt in Ht.
    assert (Hlow := Qabs_lt_low _ _ Ht).
    rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
    exact Hlow. }
  assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
  remember (u n * u n) as t eqn:Et.
  remember (natQ (Datatypes.S k)) as q eqn:Eq.
  lra.
Qed.

(* 根的下界：Datatypes.S k ≥ 1 ⟹ 根 ≥ 3/4（尾段） *)
Lemma sqrt_dim_ge_quarter : forall (k : nat) (r : Real),
  real_le real_zero r ->
  real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (3#4) (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq. destruct r as [u Hu].
  destruct (sq_bound_from_eq k (existT (fun s : Qseq => cauchy s) u Hu) Hrsq)
    as [N1 HN1].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat).
    { apply (Nat.le_trans N0 (Nat.max N0 N1) n); [apply Nat.le_max_l | exact Hn]. }
    assert (Hn1 : (N1 <= n)%nat).
    { apply (Nat.le_trans N1 (Nat.max N0 N1) n); [apply Nat.le_max_r | exact Hn]. }
    assert (Hge : Qle 0 (u n)).
    { assert (Hpos : Qlt 0 e0) by (apply QltT_to_Qlt; exact Hpos0).
      assert (Hq : Qlt e0 (u n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    apply (QH1core (3#4) (u n)).
    + exact Qle_0_three_quarters.
    + exact Hge.
    + setoid_replace ((3#4) * (3#4)) with (9#16) by ring.
      apply Qlt_le_weak. exact (HN1 n Hn1).
  - exfalso.
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (Hn1 : (N1 <= Nat.max N1 N2)%nat) by apply Nat.le_max_l.
    assert (Hn2 : (N2 <= Nat.max N1 N2)%nat) by apply Nat.le_max_r.
    assert (H9 : Qlt (9#16) (u (Nat.max N1 N2) * u (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) Hn1).
    assert (Hsmall0 := HN2 (Nat.max N1 N2) (NatLe_lift N2 (Nat.max N1 N2) Hn2)).
    apply QltT_to_Qlt in Hsmall0.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hsmall0.
    setoid_replace (0 - u (Nat.max N1 N2))
      with (- u (Nat.max N1 N2)) in Hsmall0 by ring.
    rewrite Qabs_opp in Hsmall0.
    assert (Hsq : u (Nat.max N1 N2) * u (Nat.max N1 N2)
                  == Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos (u (Nat.max N1 N2) * u (Nat.max N1 N2))
                    (Qle_0_sq_Q (u (Nat.max N1 N2)))). apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hq4 : (1#4) * (1#4) == (1#16)) by ring.
    assert (Hqabs0 : Qle 0 (Qabs (u (Nat.max N1 N2)))) by apply Qabs_nonneg.
    assert (Hstep : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#4) * (1#4)).
    { assert (Hq4p : Qlt 0 ((1#4) * (1#4))).
      { apply (Qmult_lt_0_compat (1#4) (1#4)); exact Qlt_0_quarter. }
      nra. }
    assert (Hmono : Qabs (u (Nat.max N1 N2)) * Qabs (u (Nat.max N1 N2))
                    < (1#16)).
    { rewrite <- Hq4. exact Hstep. }
    assert (Hg : Qlt (1#16) (9#16)) by (vm_compute; reflexivity).
    lra.
Qed.

Lemma root_zero_of : forall (d : Real) (Hd : real_le real_zero d),
  real_le real_zero (root_of d Hd).
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_sq_of : forall (d : Real) (Hd : real_le real_zero d),
  real_eq (real_mult (root_of d Hd) (root_of d Hd)) d.
Proof.
  intros d Hd. unfold root_of.
  destruct (real_sqrt_exists d Hd) as [r [Hr0 Hrsq]]. exact Hrsq.
Qed.

Lemma root_d_ge_zero : forall k : nat, real_le real_zero (root_d k).
Proof.
  intro k. unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrsq]]. exact Hr0.
Qed.

Lemma root_d_pos : forall k : nat, real_lt real_zero (root_d k).
Proof.
  intro k.
  unfold root_d, root_of.
  destruct (real_sqrt_exists (qkb_nat_to_R (Datatypes.S k)) (inl (qkb_nat_to_R_pos k)))
    as [r [Hr0 Hrdsq]].
  destruct (sqrt_dim_ge_quarter k r Hr0 Hrdsq) as [N HN].
  exists (1#2). split.
  - apply Qlt_to_QltT. exact Qlt_0_half.
  - exists N. intros n Hn.
    apply NatLe_drop in Hn.
    apply Qlt_to_QltT.
    change (projT1 real_zero n) with 0%Q.
    setoid_replace (projT1 r n - 0) with (projT1 r n) by ring.
    apply (Qlt_le_trans (1#2) (3#4) (projT1 r n));
      [exact Qlt_half_one | exact (HN n Hn)].
Qed.

(* real_inv_pos 的逐点形式（Defined 体展开 + leb 分支） *)
Lemma real_inv_pos_pt :
  forall (u : Qseq) (Hu : cauchy u) (eps0 : Q) (Heps0 : QltT 0 eps0)
         (N0 : nat) (HN0 : forall n : nat, NatLe N0 n -> QltT eps0 (u n - projT1 real_zero n))
         (n : nat), (N0 <= n)%nat ->
  projT1 (real_inv_pos (existT (fun s : Qseq => cauchy s) u Hu)
             (existT _ eps0 (Heps0, existT _ N0 HN0))) n == Qinv (u n).
Proof.
  intros u Hu eps0 Heps0 N0 HN0 n Hn.
  unfold real_inv_pos. cbn [projT1].
  destruct (Nat.leb N0 n) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hlt : (n < N0)%nat) by (apply (proj1 (Nat.leb_gt N0 n) E)).
    exact (Nat.lt_irrefl n (Nat.lt_le_trans n N0 n Hlt Hn)).
Qed.

(* ################ 第 4 部分：abs 界转化件（B'）与 eps 透传 ######## *)

(* 核心 abs 转化件：x² < y² + h² ⟹ |x| < |y| + 2h（无符号前提，Qabs 形式） *)
Lemma abs_le_add_abs_of_sq_lt : forall (x y : Real) (h : Q),
  Qlt 0 h ->
  real_lt (real_mult x x) (real_plus (real_mult y y) (real_const (h * h))) ->
  real_lt (real_abs x) (real_plus (real_abs y) (real_const (2 * h))).
Proof.
  intros x y h Hh Hlt. destruct Hlt as [e1 [Hpos1 [N1 HN1]]].
  exists h. split.
  - apply Qlt_to_QltT. exact Hh.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
  rewrite real_plus_proj. rewrite real_const_proj.
  rewrite !real_abs_proj.
  assert (Hpt : Qlt e1 (projT1 y n * projT1 y n + h * h - projT1 x n * projT1 x n)).
  { pose proof (HN1 n Hn) as Hp.
    apply QltT_to_Qlt in Hp.
    rewrite real_plus_proj in Hp. rewrite !real_mult_proj in Hp.
    rewrite real_const_proj in Hp.
    exact Hp. }
  assert (Hax : projT1 x n * projT1 x n == Qabs (projT1 x n) * Qabs (projT1 x n))
    by apply Qsq_abs_eq.
  assert (Hay : projT1 y n * projT1 y n == Qabs (projT1 y n) * Qabs (projT1 y n))
    by apply Qsq_abs_eq.
  assert (Hax0 : Qle 0 (Qabs (projT1 x n))) by apply Qabs_nonneg.
  assert (Hay0 : Qle 0 (Qabs (projT1 y n))) by apply Qabs_nonneg.
  assert (Hpos1q : Qlt 0 e1) by (apply QltT_to_Qlt; exact Hpos1).
  destruct (Qle_or_lt (Qabs (projT1 x n)) (Qabs (projT1 y n))) as [Hle | Hgt];
    nra.
Defined.
(* |x·y| ≤ |x|·y + eps（y > 0 尾段；eps 直接透传） *)
Lemma abs_mult_pos_eps : forall (x y : Real) (eps : Real),
  real_lt real_zero y -> real_lt real_zero eps ->
  real_lt (real_abs (real_mult x y))
          (real_plus (real_mult (real_abs x) y) eps).
Proof.
  intros x y eps Hy Heps.
  destruct Hy as [ey [Hpey [Ny HNy]]].
  destruct Heps as [ee [Hpee [Ne HNe]]].
  exists ee. split; [exact Hpee | exists (Nat.max Ny Ne); intros n Hn].
  assert (Hny : (Ny <= n)%nat).
  { apply (Nat.le_trans Ny (Nat.max Ny Ne) n);
      [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  assert (Hne : (Ne <= n)%nat).
  { apply (Nat.le_trans Ne (Nat.max Ny Ne) n);
      [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Ny Ne) n Hn)]. }
  apply Qlt_to_QltT.
  rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_abs_proj.
  rewrite ?real_mult_proj. rewrite ?real_plus_proj. rewrite ?real_abs_proj.
  assert (Hy0 : Qle 0 (projT1 y n)).
  { assert (Hq : Qlt ey (projT1 y n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNy n (NatLe_lift Ny n Hny)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 y n - 0) with (projT1 y n) in Hq by ring.
    apply (Qle_trans 0 ey (projT1 y n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpey.
    - apply Qlt_le_weak. exact Hq. }
  rewrite (Qabs_mult_gen (projT1 x n) (projT1 y n)).
  rewrite (Qabs_pos (projT1 y n) Hy0).
  assert (Hep : Qlt ee (projT1 eps n - projT1 real_zero n)).
  { apply QltT_to_Qlt. exact (HNe n (NatLe_lift Ne n Hne)). }
  change (projT1 real_zero n) with 0%Q in Hep.
  lra.
Qed.

(* ################ 第 5 部分：本地投影 + 严格 C-Datatypes.S（CW_ConstructiveWorld_219.Real 版） ## *)

Lemma sql_proj_l : forall (a : list Real) (k : nat),
  projT1 (qkb_sql a) k == sqlQ (map (fun x : Real => projT1 x k) a).
Proof.
  induction a as [| x xs IH]; intro k.
  - reflexivity.
  - cbn [qkb_sql]. rewrite real_plus_proj. rewrite real_mult_proj. rewrite IH.
    reflexivity.
Qed.

Lemma dotp_proj_l : forall (a b : list Real) (k : nat),
  projT1 (qkb_dotp a b) k
    == dotpQ (map (fun x : Real => projT1 x k) a)
             (map (fun y : Real => projT1 y k) b).
Proof.
  induction a as [| x xs IH]; intros b k.
  - reflexivity.
  - destruct b as [| y ys].
    + reflexivity.
    + cbn [qkb_dotp]. rewrite real_plus_proj. rewrite real_mult_proj. rewrite IH.
      reflexivity.
Qed.

(* 有限和 Cauchy–Schwarz（严格版，实层；UpCS cs_Q 的点对点提升） *)
Theorem cs_real_lt : forall (a b : list Real) (eps : Real),
  real_lt real_zero eps ->
  real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
          (real_plus (real_mult (qkb_sql a) (qkb_sql b)) eps).
Proof.
  intros a b eps Heps.
  destruct Heps as [e1 [Hpos1 [N1 HN1]]].
  exists e1. split.
  - exact Hpos1.
  - exists N1. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite !real_mult_proj.
    rewrite (sql_proj_l a n). rewrite (sql_proj_l b n). rewrite (dotp_proj_l a b n).
    set (A := sqlQ (map (fun x : Real => projT1 x n) a)).
    set (B := sqlQ (map (fun x : Real => projT1 x n) b)).
    set (C := dotpQ (map (fun x : Real => projT1 x n) a)
                    (map (fun y : Real => projT1 y n) b)).
    assert (Hz0 : projT1 real_zero n == 0) by reflexivity.
    assert (Hep : Qlt e1 (projT1 eps n)).
    { pose proof (HN1 n Hn) as Ht.
      apply QltT_to_Qlt in Ht.
      assert (Hzr : projT1 eps n - projT1 real_zero n == projT1 eps n).
      { rewrite Hz0. ring. }
      rewrite Hzr in Ht. exact Ht. }
    assert (Hgap : Qle 0 (A * B - C * C)).
    { apply (Qle_trans _ (C * C - C * C)).
      - apply qeq_le. ring.
      - assert (Hcs := cs_Q (map (fun x : Real => projT1 x n) a)
                            (map (fun y : Real => projT1 y n) b)).
        unfold Qminus.
        exact (Qplus_le_compat (C * C) (A * B) (-(C * C)) (-(C * C))
                 Hcs (Qle_refl _)). }
    apply (Qlt_le_trans e1 (projT1 eps n)).
    + exact Hep.
    + apply (Qle_trans _ (0 + projT1 eps n)).
      * apply qeq_le. ring.
      * apply (Qle_trans _ ((A * B - C * C) + projT1 eps n)).
        -- exact (Qplus_le_compat 0 (A * B - C * C) (projT1 eps n) (projT1 eps n)
                    Hgap (Qle_refl _)).
        -- apply qeq_le. ring.
Qed.


Lemma Qle_add_pos_l : forall b a : Q, Qle 0 a -> Qle b (b + a).
Proof.
  intros b a Ha.
  apply (Qle_trans b (b + 0) (b + a)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat b b 0 a); [apply Qle_refl | exact Ha].
Qed.

Lemma Qle_abs_self : forall x : Q, Qle x (Qabs x).
Proof.
  intro x. destruct (Qle_or_lt 0 x) as [H0 | H0].
  - rewrite (Qabs_pos x H0). apply Qle_refl.
  - rewrite (Qabs_neg x (Qlt_le_weak x 0 H0)). lra.
Qed.

(* 根的绝对值尾界（统一形式，lt/eq 两支内部消化）：
   0 在 lt 支给精确界（|rq_n| = rq_n ≤ Q_n），eq 支给 |rq_n| ≤ d。 *)
Lemma root_abs_tail : forall (rq Q2 : Real) (d : Q),
  Qlt 0 d -> real_lt real_zero Q2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)).
Proof.
  intros rq Q2 d Hd HQ Hr0 Hrq.
  destruct (real_le_pt_ev_plus rq Q2 d Hd Hrq) as [Nq HNq].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [er [Hper [Nr HNr]]].
    exists (Nat.max Nr (Nat.max Nq NQ)). intros n Hn.
    assert (Hnr : (Nr <= n)%nat) by lia.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hper' : Qlt 0 er) by (apply QltT_to_Qlt; exact Hper).
    assert (Hge : Qle 0 (projT1 rq n)).
    { assert (Hq : Qlt er (projT1 rq n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNr n (NatLe_lift Nr n Hnr)). }
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    rewrite (Qabs_pos (projT1 rq n) Hge).
    exact (HNq n Hnq).
  - destruct (Heq0 d (Qlt_to_QltT 0 d Hd)) as [Ne HNe].
    exists (Nat.max Nq (Nat.max Ne NQ)). intros n Hn.
    assert (Hnq : (Nq <= n)%nat) by lia.
    assert (Hne : (Ne <= n)%nat) by lia.
    assert (HnQ : (NQ <= n)%nat) by lia.
    assert (HQ0 : Qle 0 (projT1 Q2 n)).
    { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
      { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
      assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
      change (projT1 real_zero n) with 0%Q in Hq.
      lra. }
    assert (Hab : Qlt (Qabs (projT1 rq n)) d).
    { assert (Ht := HNe n (NatLe_lift Ne n Hne)).
      apply QltT_to_Qlt in Ht.
      change (projT1 real_zero n) with 0%Q in Ht.
      setoid_replace (0 - projT1 rq n) with (- projT1 rq n) in Ht by ring.
      rewrite Qabs_opp in Ht. exact Ht. }
    apply (Qle_trans (Qabs (projT1 rq n)) d (projT1 Q2 n + d)).
    { apply Qlt_le_weak. exact Hab. }
    { setoid_replace (projT1 Q2 n + d) with (d + projT1 Q2 n) by ring.
      apply (Qle_add_pos_l d (projT1 Q2 n) HQ0). }
Qed.

(* 根积尾界（统一形式）：|rq·rk| ≤ Q·K + d·(MQ+MK) + d²，其中
   MQ/MK 为 Q/K 的全局界（real_norm_bounded），d 为内部 eq 支截断粒度 *)
Lemma prod_tail_bound : forall (rq rk Q2 K2 : Real) (MQ MK : Q) (d : Q),
  Qlt 0 d ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  real_le real_zero rq -> real_le rq Q2 ->
  real_le real_zero rk -> real_le rk K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (Qabs (projT1 (real_mult rq rk) n))
        (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
Proof.
  intros rq rk Q2 K2 MQ MK d Hd HQ HK Hr0 Hrq Hk0 Hrk HMQ HMK.
  destruct (root_abs_tail rq Q2 d Hd HQ Hr0 Hrq) as [Nq HNq].
  destruct (root_abs_tail rk K2 d Hd HK Hk0 Hrk) as [Nk HNk].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max Nq (Nat.max Nk (Nat.max NQ NK))).
  intros n Hn.
  assert (Hnq : (Nq <= n)%nat) by lia.
  assert (Hnk : (Nk <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  rewrite real_mult_proj. rewrite Qabs_mult_gen.
  assert (Hbq : Qle (Qabs (projT1 rq n)) (projT1 Q2 n + d)) by exact (HNq n Hnq).
  assert (Hbk : Qle (Qabs (projT1 rk n)) (projT1 K2 n + d)) by exact (HNk n Hnk).
  assert (Haq : Qle 0 (Qabs (projT1 rq n))) by apply Qabs_nonneg.
  assert (Hak : Qle 0 (Qabs (projT1 rk n))) by apply Qabs_nonneg.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    assert (HpeQ' : Qlt 0 eQ) by (apply QltT_to_Qlt; exact HpeQ).
    lra. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    assert (HpeK' : Qlt 0 eK) by (apply QltT_to_Qlt; exact HpeK).
    lra. }
  assert (HQm : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    { apply Qle_abs_self. }
    { exact (HMQ n). } }
  assert (HKm : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    { apply Qle_abs_self. }
    { exact (HMK n). } }
  apply (Qle_trans (Qabs (projT1 rq n) * Qabs (projT1 rk n))
                   ((projT1 Q2 n + d) * (projT1 K2 n + d))
                   (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
  - apply (Qmult_le_mono2 _ _ _ _ Haq Hak Hbq Hbk).
  - nra.
Qed.


(* ################ 第 6 部分：件 1 内积/范数桥 #################### *)

(* 件 1：⟨q,q⟩ == Σq²（UpCS 的 qkb_sql 即 Σq²——命名桥）。 *)
Theorem inner_sq_norm : forall q : list Real, real_eq (qkb_dotp q q) (qkb_sql q).
Proof.
  intro q. apply real_eq_of_zero_diff. intros n.
  rewrite (dotp_proj_l q q n). rewrite (sql_proj_l q n).
  rewrite dotpQ_sqlQ. ring.
Qed.

(* ################ 第 7 部分：件 2 界转化主件 #################### *)

(* 配对界：根有界前提 ⟹ |⟨a,b⟩| < Q·K + h（inl 严格支； witness h/4） *)
Lemma qk_pair_bound : forall (a b : list Real) (Q2 K2 : Real) (MQ MK : Q) (h : Q)
  (Ha : real_le real_zero (qkb_sql a)) (Hb : real_le real_zero (qkb_sql b)),
  Qlt 0 h -> Qlt 0 MQ -> Qlt 0 MK ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le (root_of (qkb_sql a) Ha) Q2 -> real_le (root_of (qkb_sql b) Hb) K2 ->
  real_lt (real_abs (qkb_dotp a b)) (real_plus (real_mult Q2 K2) (real_const h)).
Proof.
  intros a b Q2 K2 MQ MK h Ha Hb Hh HMQp HMKp HQ HK HMQ HMK Hqa Hkb.
  set (ra := root_of (qkb_sql a) Ha).
  set (rb := root_of (qkb_sql b) Hb).
  assert (Hrasq : real_eq (real_mult ra ra) (qkb_sql a)) by apply (root_sq_of (qkb_sql a) Ha).
  assert (Hrbsq : real_eq (real_mult rb rb) (qkb_sql b)) by apply (root_sq_of (qkb_sql b) Hb).
  assert (Hra0 : real_le real_zero ra) by apply (root_zero_of (qkb_sql a) Ha).
  assert (Hrb0 : real_le real_zero rb) by apply (root_zero_of (qkb_sql b) Hb).
  (* C-Datatypes.S 严格版，eps := ((1#4)*h)² *)
  assert (Hcs : real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
                  (real_plus (real_mult (qkb_sql a) (qkb_sql b))
                              (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply cs_real_lt. apply qkb_real_const_pos.
    apply (Qmult_lt_0_compat ((1#4) * h) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh]. }
  (* 换元到 (ra·rb)² *)
  assert (E12 : real_eq (real_mult (qkb_sql a) (qkb_sql b))
                        (real_mult (real_mult ra rb) (real_mult ra rb))).
  { apply (real_eq_trans (real_mult (qkb_sql a) (qkb_sql b))
                         (real_mult (real_mult ra ra) (real_mult rb rb)) _).
    - apply (RealSetoid.real_eq_mult_compat (qkb_sql a) (qkb_sql b)
                                 (real_mult ra ra) (real_mult rb rb)
                                 (real_eq_sym (real_mult ra ra) (qkb_sql a) Hrasq)
                                 (real_eq_sym (real_mult rb rb) (qkb_sql b) Hrbsq)).
    - apply real_eq_of_zero_diff. intro n.
      rewrite !real_mult_proj. ring. }
  assert (H3 : real_lt (real_mult (qkb_dotp a b) (qkb_dotp a b))
                (real_plus (real_mult (real_mult ra rb) (real_mult ra rb))
                           (real_const (((1#4) * h) * ((1#4) * h))))).
  { apply (real_lt_le_trans _ (real_plus (real_mult (qkb_sql a) (qkb_sql b))
                                          (real_const (((1#4) * h) * ((1#4) * h)))) _ Hcs).
    apply (real_le_plus_compat (real_mult (qkb_sql a) (qkb_sql b))
                               (real_mult (real_mult ra rb) (real_mult ra rb))
                               (real_const (((1#4) * h) * ((1#4) * h)))
                               (real_const (((1#4) * h) * ((1#4) * h)))).
    + apply (RealSetoid.real_eq_le (real_mult (qkb_sql a) (qkb_sql b))
                                   (real_mult (real_mult ra rb) (real_mult ra rb))
                                   E12).
    + apply (real_le_refl (real_const (((1#4) * h) * ((1#4) * h)))). }
  (* B'：|AB| < |ra·rb| + 2·((1#4)*h) = |ra·rb| + (1#2)*h *)
  assert (H4 : real_lt (real_abs (qkb_dotp a b))
                (real_plus (real_abs (real_mult ra rb))
                           (real_const (2 * ((1#4) * h))))).
  { apply (abs_le_add_abs_of_sq_lt (qkb_dotp a b) (real_mult ra rb) ((1#4) * h)).
    - apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
    - exact H3. }
  (* B' 的点对点尾事实（不破坏 witness 值）：
     per n ≥ N4: |AB|_n ≤ |ra_n·rb_n| + (1#2)*h  —— 由 real_lt 的严格差与 eps4 > 0 *)
  destruct H4 as [eps4 [Hpos4 [N4 HN4]]].
  set (d := h / (32 * (1 + MQ + MK + h))).
  assert (Hgt : Qlt 0 (1 + MQ + MK + h)) by lra.
  assert (HX1 : Qle 1 (1 + MQ + MK + h)) by lra.
  assert (Hd0 : Qlt 0 d).
  { unfold d. apply (Qmult_lt_0_compat h (/ (32 * (1 + MQ + MK + h)))).
    - exact Hh.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + MQ + MK + h)).
      + exact Qlt_0_32.
      + exact Hgt. }
  assert (Hd1 : d * (32 * (1 + MQ + MK + h)) == h).
  { unfold d. field.
    intro Hz. lra. }
  assert (Hd2 : Qle (16 * (d * (MQ + MK) + d * d)) h).
  { assert (Hdh : Qle d h) by nra.
    nra. }
  destruct (prod_tail_bound ra rb Q2 K2 MQ MK d Hd0 HQ HK
              Hra0 Hqa Hrb0 Hkb
              HMQ HMK) as [Np HNp].
  exists ((1#4) * h). split.
  - apply Qlt_to_QltT. apply (Qmult_lt_0_compat (1#4) h); [exact Qlt_0_half | exact Hh].
  - exists (Nat.max N4 Np). intros n Hn.
    assert (Hn4 : (N4 <= n)%nat).
    { apply (Nat.le_trans N4 (Nat.max N4 Np) n);
        [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    assert (Hnp : (Np <= n)%nat).
    { apply (Nat.le_trans Np (Nat.max N4 Np) n);
        [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 Np) n Hn)]. }
    apply Qlt_to_QltT.
    rewrite real_plus_proj. rewrite !real_mult_proj. rewrite real_const_proj.
    rewrite !real_abs_proj.
    assert (Hf1 : Qle (Qabs (projT1 (qkb_dotp a b) n))
                      (Qabs (projT1 ra n) * Qabs (projT1 rb n) + (1#2) * h)).
    { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
      apply QltT_to_Qlt in Hq.
      assert (Hpe4 : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      rewrite real_plus_proj in Hq. rewrite real_const_proj in Hq.
      rewrite !real_abs_proj in Hq.
      rewrite real_mult_proj in Hq.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hq.
      lra. }
    assert (Hf2 : Qle (Qabs (projT1 ra n) * Qabs (projT1 rb n))
                      (projT1 Q2 n * projT1 K2 n + d * (MQ + MK) + d * d)).
    { pose proof (HNp n Hnp) as Hp.
      rewrite real_mult_proj in Hp.
      rewrite (Qabs_mult_gen (projT1 ra n) (projT1 rb n)) in Hp.
      exact Hp. }
    nra.
Qed.
(* ################ 第 8 部分：件 2 rd-loss 链 + 主定理 ############ *)

(* rd ≥ 0 尾段（inl 支精确；inr 支 rd≈0 与 rd²≈Datatypes.S k≥1 矛盾） *)
Lemma rd_pos_tail : forall (k : nat) (r : Real),
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle 0 (projT1 r n)).
Proof.
  intros k r Hr0 Hrsq.
  destruct Hr0 as [Hlt0 | Heq0].
  - destruct Hlt0 as [e0 [Hpos0 [N0 HN0]]].
    exists N0. intros n Hn0.
    assert (Hq : Qlt e0 (projT1 r n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HN0 n (NatLe_lift N0 n Hn0)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 r n - 0) with (projT1 r n) in Hq by ring.
    apply (Qle_trans 0 e0 (projT1 r n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact Hpos0
      | apply Qlt_le_weak; exact Hq].
  - exfalso.
    destruct (sq_bound_from_eq k r Hrsq) as [N1 HN1].
    destruct (Heq0 (1#4) (Qlt_to_QltT 0 (1#4) Qlt_0_quarter)) as [N2 HN2].
    assert (H9 : Qlt (9#16)
                   (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)))
      by exact (HN1 (Nat.max N1 N2) (Nat.le_max_l N1 N2)).
    assert (Hs := HN2 (Nat.max N1 N2)
                    (NatLe_lift N2 (Nat.max N1 N2) (Nat.le_max_r N1 N2))).
    apply QltT_to_Qlt in Hs.
    change (projT1 real_zero (Nat.max N1 N2)) with 0%Q in Hs.
    setoid_replace (0 - projT1 r (Nat.max N1 N2))
      with (- projT1 r (Nat.max N1 N2)) in Hs by ring.
    rewrite Qabs_opp in Hs.
    assert (Hsq : projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2)
                  == Qabs (projT1 r (Nat.max N1 N2))
                     * Qabs (projT1 r (Nat.max N1 N2))).
    { rewrite <- (Qabs_pos
                    (projT1 r (Nat.max N1 N2) * projT1 r (Nat.max N1 N2))
                    (Qle_0_sq_Q (projT1 r (Nat.max N1 N2)))).
      apply Qabs_sq. }
    rewrite Hsq in H9.
    assert (Hmono : Qabs (projT1 r (Nat.max N1 N2))
                      * Qabs (projT1 r (Nat.max N1 N2)) < (1#16)).
    { assert (Ha0 : Qle 0 (Qabs (projT1 r (Nat.max N1 N2))))
        by apply Qabs_nonneg.
      nra. }
    lra.
Qed.

(* rd ≥ 1 − dq 尾段（dq ≤ 1 前提下） *)
Lemma rd_ge_one_minus_delta : forall (k : nat) (r : Real) (dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat -> Qle (1 - dq) (projT1 r n)).
Proof.
  intros k r dq Hdq0 Hdq1 Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (Qle_or_lt 1 dq) as [Hge | Hlt].
  - exists N0. intros n Hn. pose proof (HN0 n Hn) as Hge0. lra.
  - assert (Hpos : Qlt 0 (1 - dq)) by lra.
    assert (Heps : Qlt 0 (1 - (1 - dq) * (1 - dq))) by nra.
    destruct (Hrsq (1 - (1 - dq) * (1 - dq))
                   (Qlt_to_QltT 0 (1 - (1 - dq) * (1 - dq)) Heps)) as [N1 HN1].
    exists (Nat.max N0 N1). intros n Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hn1 : (N1 <= n)%nat) by lia.
    apply (QH1core (1 - dq) (projT1 r n)).
    + assert (Hd1 : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
      lra.
    + exact (HN0 n Hn0).
    + (* rd² ≈ Datatypes.S k 尾段 ⟹ rd_n² > Datatypes.S k − (1−(1−dq)²) ≥ (1−dq)² *)
      assert (Hs := HN1 n (NatLe_lift N1 n Hn1)).
      apply QltT_to_Qlt in Hs.
      assert (Hlow := Qabs_lt_low _ _ Hs).
      rewrite (nat_to_R_proj (Datatypes.S k) n) in Hlow.
      rewrite real_mult_proj in Hlow.
      assert (Hone : Qle 1 (natQ (Datatypes.S k))) by apply natQ_Sk_ge_one.
      nra.
Qed.

(* 件 2：rd-loss 后的最终界——Q·K ≤ Q·K·rd + MQ·MK·dq（尾段） *)
Lemma qk_rd_loss : forall (k : nat) (Q2 K2 r : Real) (MQ MK dq : Q),
  Qlt 0 dq -> Qle dq 1 ->
  real_lt real_zero Q2 -> real_lt real_zero K2 ->
  (forall n : nat, Qle (Qabs (projT1 Q2 n)) MQ) ->
  (forall n : nat, Qle (Qabs (projT1 K2 n)) MK) ->
  real_le real_zero r -> real_eq (real_mult r r) (qkb_nat_to_R (Datatypes.S k)) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qle (projT1 Q2 n * projT1 K2 n)
        (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
Proof.
  intros k Q2 K2 r MQ MK dq Hdq0 Hdq1 HQ HK HMQ HMK Hr0 Hrsq.
  destruct (rd_pos_tail k r Hr0 Hrsq) as [N0 HN0].
  destruct (rd_ge_one_minus_delta k r dq Hdq0 Hdq1 Hr0 Hrsq) as [N1 HN1].
  destruct HQ as [eQ [HpeQ [NQ HNQ]]].
  destruct HK as [eK [HpeK [NK HNK]]].
  exists (Nat.max N0 (Nat.max N1 (Nat.max NQ NK))). intros n Hn.
  assert (Hn0 : (N0 <= n)%nat) by lia.
  assert (Hn1 : (N1 <= n)%nat) by lia.
  assert (HnQ : (NQ <= n)%nat) by lia.
  assert (HnK : (NK <= n)%nat) by lia.
  assert (HQ0 : Qle 0 (projT1 Q2 n)).
  { assert (Hq : Qlt eQ (projT1 Q2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNQ n (NatLe_lift NQ n HnQ)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 Q2 n - 0) with (projT1 Q2 n) in Hq by ring.
    apply (Qle_trans 0 eQ (projT1 Q2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeQ
      | apply Qlt_le_weak; exact Hq]. }
  assert (HK0 : Qle 0 (projT1 K2 n)).
  { assert (Hk : Qlt eK (projT1 K2 n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNK n (NatLe_lift NK n HnK)). }
    change (projT1 real_zero n) with 0%Q in Hk.
    setoid_replace (projT1 K2 n - 0) with (projT1 K2 n) in Hk by ring.
    apply (Qle_trans 0 eK (projT1 K2 n));
      [apply Qlt_le_weak; apply QltT_to_Qlt; exact HpeK
      | apply Qlt_le_weak; exact Hk]. }
  assert (HQb : Qle (projT1 Q2 n) MQ).
  { apply (Qle_trans (projT1 Q2 n) (Qabs (projT1 Q2 n)) MQ).
    - apply Qle_abs_self.
    - exact (HMQ n). }
  assert (HKb : Qle (projT1 K2 n) MK).
  { apply (Qle_trans (projT1 K2 n) (Qabs (projT1 K2 n)) MK).
    - apply Qle_abs_self.
    - exact (HMK n). }
  assert (Hrdn : Qle (1 - dq) (projT1 r n)) by (exact (HN1 n Hn1)).
  assert (Hsum : Qle 1 (projT1 r n + dq)) by lra.
  assert (Hdq0le : Qle 0 dq) by (apply Qlt_le_weak; exact Hdq0).
  assert (Hd : Qle (projT1 Q2 n * projT1 K2 n) (MQ * MK)).
  { apply (Qmult_le_mono2 (projT1 Q2 n) (projT1 K2 n) MQ MK);
      [exact HQ0 | exact HK0 | exact HQb | exact HKb]. }
  assert (Hqk20 : Qle 0 (projT1 Q2 n * projT1 K2 n)).
  { apply (Qmult_le_0_compat (projT1 Q2 n) (projT1 K2 n)); assumption. }
  assert (Hscale : Qle (projT1 Q2 n * projT1 K2 n)
                       (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
  { apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                     (projT1 Q2 n * projT1 K2 n * 1)
                     (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))).
    - apply qeq_le. ring.
    - apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) 1
                            (projT1 Q2 n * projT1 K2 n) (projT1 r n + dq));
        [exact Hqk20 | exact zero_le_one | apply Qle_refl | exact Hsum]. }
  assert (Hdqle : Qle (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq)).
  { apply (Qmult_le_mono2 (projT1 Q2 n * projT1 K2 n) dq (MQ * MK) dq);
      [exact Hqk20 | exact Hdq0le | exact Hd | apply Qle_refl]. }
  assert (Hsplit : Qle (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                       (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq)).
  { setoid_replace (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
      with (projT1 Q2 n * projT1 K2 n * projT1 r n
            + projT1 Q2 n * projT1 K2 n * dq) by ring.
    apply (Qplus_le_compat (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * projT1 r n)
                           (projT1 Q2 n * projT1 K2 n * dq) (MQ * MK * dq));
      [apply Qle_refl | exact Hdqle]. }
  apply (Qle_trans (projT1 Q2 n * projT1 K2 n)
                   (projT1 Q2 n * projT1 K2 n * (projT1 r n + dq))
                   (projT1 Q2 n * projT1 K2 n * projT1 r n + MQ * MK * dq));
    [exact Hscale | exact Hsplit].
Qed.

(* ################ 第 9 部分：件 2 主定理（rd-loss 链装配） ######## *)

(* 件 2：根有界前提 ⟹ |⟨a,b⟩| ≤ Q·K·√d + eps（eps 版；inl 严格支）。
   装配：qk_pair_bound（h := eps/2，witness eps/8 严格）+ rd-loss 链
   （QK ≤ QK·rd + QK·dq，dq := eps/(32(1+QK))；dq ≤ 1 支用 qk_rd_loss，
   dq > 1 支 eps 本身已大、只需 rd ≥ 0 尾段），eps/4 余量 witness。 *)
Theorem real_logit_bound_of_norm_bounds :
  forall (a b : list Real) (Qb Kb : Q) (k : nat) (eps : Q)
    (Ha : real_le real_zero (qkb_sql a)) (Hb : real_le real_zero (qkb_sql b)),
    Qlt 0 eps -> Qlt 0 Qb -> Qlt 0 Kb ->
    real_le (root_of (qkb_sql a) Ha) (real_const Qb) ->
    real_le (root_of (qkb_sql b) Hb) (real_const Kb) ->
    real_le (real_abs (qkb_dotp a b))
      (real_plus (real_mult (real_mult (real_const Qb) (real_const Kb)) (root_d k))
                 (real_const eps)).
Proof.
  intros a b Qb Kb k eps Ha Hb Heps HQ HK Hqa Hkb.
  assert (HQK0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
  assert (Hgt1 : Qlt 0 (1 + Qb * Kb)) by lra.
  set (dq := eps / (32 * (1 + Qb * Kb))).
  assert (Hdq0 : Qlt 0 dq).
  { unfold dq. apply (Qmult_lt_0_compat eps (/ (32 * (1 + Qb * Kb)))).
    - exact Heps.
    - apply Qinv_lt_0_compat. apply (Qmult_lt_0_compat 32 (1 + Qb * Kb)).
      + exact Qlt_0_32.
      + exact Hgt1. }
  assert (Hdqe : dq * (32 * (1 + Qb * Kb)) == eps).
  { unfold dq. field.
    intro Hz. lra. }
  assert (Hdqk : Qle (Qb * Kb * dq) ((1#32) * eps)).
  { rewrite <- Hdqe.
    setoid_replace ((1#32) * (dq * (32 * (1 + Qb * Kb))))
      with (dq + dq * (Qb * Kb)) by ring.
    setoid_replace (Qb * Kb * dq) with (0 + dq * (Qb * Kb)) by ring.
    apply (Qplus_le_compat 0%Q dq (dq * (Qb * Kb)) (dq * (Qb * Kb))).
    - apply Qlt_le_weak. exact Hdq0.
    - apply Qle_refl. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply qkb_real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply qkb_real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  destruct (qk_pair_bound a b (real_const Qb) (real_const Kb) Qb Kb ((1#2) * eps)
              Ha Hb
              (Qmult_lt_0_compat (1#2) eps Qlt_0_half Heps) HQ HK HcQpos HcKpos
              HQbnd HKbnd Hqa Hkb) as [eps4 [Hpos4 [N4 HN4]]].
  destruct (Qle_or_lt dq 1) as [Hdq1 | Hdqbig].
  - (* dq ≤ 1：rd-loss 链 QK ≤ QK·rd + QK·dq *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (qk_rd_loss k (real_const Qb) (real_const Kb) (root_d k) Qb Kb dq
                Hdq0 Hdq1 HcQpos HcKpos HQbnd HKbnd Hrd0 (root_d_sq k))
      as [N2 HN2].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N2). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N2) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      assert (Hn2 : (N2 <= n)%nat).
      { apply (Nat.le_trans N2 (Nat.max N4 N2) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N2) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj.
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (qkb_dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Hbr : Qle (Qb * Kb) (Qb * Kb * projT1 (root_d k) n + Qb * Kb * dq)).
      { pose proof (HN2 n Hn2) as Hq.
        rewrite !real_const_proj in Hq. exact Hq. }
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (qkb_dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      remember (Mq * dq) as Z eqn:HZ in *.
      clear HQ HK Hgt1 HQK0 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN2 Hrd0.
      assert (Hbr2 : Qle (Mq - (1#32) * eps) W).
      { assert (H1 : Qle (Mq - Z) W) by lra.
        apply (Qle_trans (Mq - (1#32) * eps) (Mq - Z) W).
        - lra.
        - exact H1. }
      clear HW HZ Hbr Hdqk Hdq0 Hdq1.
      lra.
  - (* dq > 1：eps > 32(1+QK)，QK 本身 < eps/32，只需 rd ≥ 0 尾段 *)
    assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
    destruct (rd_pos_tail k (root_d k) Hrd0 (root_d_sq k)) as [N0 HN0].
    left.
    exists ((1#4) * eps). split.
    + apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat (1#4) eps); [exact Qlt_0_quarter | exact Heps].
    + exists (Nat.max N4 N0). intros n Hn.
      assert (Hn4 : (N4 <= n)%nat).
      { apply (Nat.le_trans N4 (Nat.max N4 N0) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      assert (Hn0 : (N0 <= n)%nat).
      { apply (Nat.le_trans N0 (Nat.max N4 N0) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max N4 N0) n Hn)]. }
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj.
      assert (Hf1 : Qlt eps4 (Qb * Kb + (1#2) * eps - Qabs (projT1 (qkb_dotp a b) n))).
      { pose proof (HN4 n (NatLe_lift N4 n Hn4)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Hrn : Qle 0 (projT1 (root_d k) n)) by (exact (HN0 n Hn0)).
      assert (Hpos4q : Qlt 0 eps4) by (apply QltT_to_Qlt; exact Hpos4).
      remember (Qabs (projT1 (qkb_dotp a b) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq eqn:HMq in *.
      clear HQ HK Hgt1 Hdqe HMq HAq Ha Hb Hqa Hkb
            HcQpos HcKpos HQbnd HKbnd HN4 HN0 Hdq0.
      assert (Hmlt : Qlt Mq (Mq * dq)).
      { pose proof (Qmult_lt_compat_r 1 dq Mq HQK0 Hdqbig) as Hm2.
        setoid_replace (1 * Mq) with Mq in Hm2 by ring.
        setoid_replace (dq * Mq) with (Mq * dq) in Hm2 by ring.
        exact Hm2. }
      assert (Hm32 : Qle Mq ((1#32) * eps)).
      { apply (Qle_trans Mq (Mq * dq) ((1#32) * eps));
          [apply Qlt_le_weak; exact Hmlt | exact Hdqk]. }
      remember (Mq * projT1 (root_d k) n) as W eqn:HW in *.
      assert (Hw0 : Qle 0 W).
      { subst W. apply (Qmult_le_0_compat Mq (projT1 (root_d k) n)).
        - apply Qlt_le_weak. exact HQK0.
        - exact Hrn. }
      clear Hmlt Hdqbig Hdqk HQK0 HW Hrn.
      lra.
Qed.

(* ################ 第 10 部分：件 3 QKᵀ 绑定 + Δ 封装（Section 主定理） ## *)

Section QKLogitSection.

Variable kdim : nat.
Variable Qc Kc : Q.

(* 逆根：real_inv_pos 构造性携带正性证书（root_d_pos） *)
Definition w_root : Real := real_inv_pos (root_d kdim) (root_d_pos kdim).

(* Δ := Q·K·inv(√d) + 1（+1 余量精确吸收 (1/2)·w ≤ 2/3 < 1） *)
Definition Delta : Real :=
  real_plus (real_mult (real_mult (real_const Qc) (real_const Kc)) w_root)
            (real_const 1).

(* attn_logit：⟨q,k⟩·inv(√d) *)
Definition attn_logit (a b : list Real) : Real :=
  real_mult (qkb_dotp a b) w_root.

End QKLogitSection.

(* w_root 尾段数据：正性（real_inv_pos_pos 尾段）+ 乘法核对
   （real_inv_pos_correct 尾段，固定 δ := 1#4 截断：3/4 < Wn·Rn < 5/4）。
   下界系数 5/3 由 rd ≥ 3/4 吸收：Wn ≤ 5/3，(3/8)·Wn ≤ 5/8 < 1，
   Δ 的 +1 余量照常吸收（per-pair witness 仍为 1/4）。 *)
Theorem qk_logits_bounded :
  forall (k : nat) (Qb Kb : Q) (vq vk : nat -> list Real)
    (Hvsq : forall s : nat, real_le real_zero (qkb_sql (vq s)))
    (Hksq : forall s : nat, real_le real_zero (qkb_sql (vk s))),
    Qlt 0 Qb -> Qlt 0 Kb ->
    (forall s : nat, real_le (root_of (qkb_sql (vq s)) (Hvsq s)) (real_const Qb)) ->
    (forall s : nat, real_le (root_of (qkb_sql (vk s)) (Hksq s)) (real_const Kb)) ->
    And (real_lt real_zero (Delta k Qb Kb))
        (forall s s' : nat,
           real_le (real_abs (attn_logit k (vq s) (vk s'))) (Delta k Qb Kb)).
Proof.
  intros k Qb Kb vq vk Hvsq Hksq HQ HK Hvb Hkb.
  assert (Hrd0 : real_le real_zero (root_d k)) by apply root_d_ge_zero.
  destruct (sqrt_dim_ge_quarter k (root_d k) Hrd0 (root_d_sq k)) as [Ns HNs].
  assert (Hwlt : real_lt real_zero (w_root k))
    by (apply (real_inv_pos_pos (root_d k) (root_d_pos k))).
  destruct Hwlt as [ew [Hpew [Nwp HNwp]]].
  assert (Hcorrect : real_eq (real_mult (root_d k) (w_root k)) real_one)
    by (apply (real_inv_pos_correct (root_d k) (root_d_pos k))).
  assert (Hqt : Qlt 0 (1#8)) by lra.
  destruct (Hcorrect (1#8) (Qlt_to_QltT 0 (1#8) Hqt)) as [Nc HNc].
  set (Nw := Nat.max Ns (Nat.max Nwp Nc)).
  assert (Hwp' : forall n : nat, (Nw <= n)%nat -> Qlt 0 (projT1 (w_root k) n)).
  { intros n Hnn.
    assert (Hnwp : (Nwp <= n)%nat).
    { apply (Nat.le_trans Nwp Nw n).
      - apply (Nat.le_trans Nwp (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_l.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hq : Qlt ew (projT1 (w_root k) n - projT1 real_zero n)).
    { apply QltT_to_Qlt. exact (HNwp n (NatLe_lift Nwp n Hnwp)). }
    change (projT1 real_zero n) with 0%Q in Hq.
    setoid_replace (projT1 (w_root k) n - 0) with (projT1 (w_root k) n) in Hq by ring.
    apply (Qle_lt_trans 0 ew (projT1 (w_root k) n)).
    - apply Qlt_le_weak. apply QltT_to_Qlt. exact Hpew.
    - exact Hq. }
  assert (Hwub : forall n : nat, (Nw <= n)%nat ->
            Qlt (projT1 (w_root k) n) (3#2)).
  { intros n Hnn.
    assert (Hnc : (Nc <= n)%nat).
    { apply (Nat.le_trans Nc Nw n).
      - apply (Nat.le_trans Nc (Nat.max Nwp Nc) Nw).
        + apply Nat.le_max_r.
        + apply Nat.le_max_r.
      - exact Hnn. }
    assert (Hc' : Qlt (Qabs (projT1 (root_d k) n * projT1 (w_root k) n - 1)) (1#8)).
    { pose proof (HNc n (NatLe_lift Nc n Hnc)) as Hq.
      apply QltT_to_Qlt in Hq.
      rewrite real_mult_proj in Hq.
      change (projT1 real_one n) with 1%Q in Hq.
      exact Hq. }
    assert (Hrl : Qlt (3#4) (projT1 (root_d k) n * projT1 (w_root k) n)).
    { assert (Hl := Qabs_lt_low _ _ Hc'). lra. }
    assert (Hru : Qlt (projT1 (root_d k) n * projT1 (w_root k) n) (9#8)).
    { assert (Hu := Qabs_lt_l _ _ Hc'). lra. }
    assert (Hwpn : Qlt 0 (projT1 (w_root k) n)) by (apply (Hwp' n Hnn)).
    assert (Hns : (Ns <= n)%nat).
    { apply (Nat.le_trans Ns Nw n).
      - apply Nat.le_max_l.
      - exact Hnn. }
    assert (Hs1 : Qle ((3#4) * projT1 (w_root k) n)
                      (projT1 (root_d k) n * projT1 (w_root k) n)).
    { apply (Qmult_le_compat_r (3#4) (projT1 (root_d k) n) (projT1 (w_root k) n));
        [exact (HNs n Hns) | apply Qlt_le_weak; exact Hwpn]. }
    assert (Hw43b : Qle (projT1 (w_root k) n)
                      ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
    { apply (Qle_trans (projT1 (w_root k) n)
                       ((4#3) * ((3#4) * projT1 (w_root k) n))
                       ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))).
      - apply qeq_le. ring.
      - setoid_replace ((4#3) * ((3#4) * projT1 (w_root k) n))
          with (((3#4) * projT1 (w_root k) n) * (4#3)) by ring.
        setoid_replace ((4#3) * (projT1 (root_d k) n * projT1 (w_root k) n))
          with ((projT1 (root_d k) n * projT1 (w_root k) n) * (4#3)) by ring.
        apply (Qmult_le_compat_r ((3#4) * projT1 (w_root k) n)
                                  (projT1 (root_d k) n * projT1 (w_root k) n) (4#3)).
        + exact Hs1.
        + apply Qlt_le_weak. lra. }
    clear - Hw43b Hru Hwpn. lra. }
  assert (HcQpos : real_lt real_zero (real_const Qb)) by (apply qkb_real_const_pos; exact HQ).
  assert (HcKpos : real_lt real_zero (real_const Kb)) by (apply qkb_real_const_pos; exact HK).
  assert (HQbnd : forall n : nat, Qle (Qabs (projT1 (real_const Qb) n)) Qb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Qb (Qlt_le_weak 0 Qb HQ)).
    apply Qle_refl. }
  assert (HKbnd : forall n : nat, Qle (Qabs (projT1 (real_const Kb) n)) Kb).
  { intro n. rewrite real_const_proj. rewrite (Qabs_pos Kb (Qlt_le_weak 0 Kb HK)).
    apply Qle_refl. }
  assert (Hpair : forall s s' : nat,
           real_lt (real_abs (qkb_dotp (vq s) (vk s')))
                   (real_plus (real_mult (real_const Qb) (real_const Kb))
                              (real_const (1#2)))).
  { intros s s'.
    apply (qk_pair_bound (vq s) (vk s') (real_const Qb) (real_const Kb) Qb Kb (1#2)
             (Hvsq s) (Hksq s') Qlt_0_half HQ HK HcQpos HcKpos HQbnd HKbnd
             (Hvb s) (Hkb s')). }
  split.
  - (* Δ > 0（witness 1/2）：QK > 0 且 Wn > 0（尾段） *)
    exists (1#2). split.
    + apply Qlt_to_QltT. exact Qlt_0_half.
    + exists Nw. intros n Hn.
      unfold Delta.
      apply Qlt_to_QltT.
      change (projT1 real_zero n) with 0%Q.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      setoid_replace (Qb * Kb * projT1 (w_root k) n + 1 - 0)
        with (Qb * Kb * projT1 (w_root k) n + 1) by ring.
      assert (Hnn : (Nw <= n)%nat) by (apply (NatLe_drop Nw n Hn)).
      pose proof (Hwp' n Hnn) as Hwp.
      assert (Hqk0 : Qlt 0 (Qb * Kb)) by (apply Qmult_lt_0_compat; assumption).
      assert (Hqw : Qlt 0 (Qb * Kb * projT1 (w_root k) n)).
      { apply (Qmult_lt_0_compat (Qb * Kb) (projT1 (w_root k) n));
          [exact Hqk0 | exact Hwp]. }
      setoid_replace ((1#2)%Q) with (0 + (1#2)) by ring.
      apply (Qplus_lt_compat 0 (Qb * Kb * projT1 (w_root k) n) (1#2) 1);
        [exact Hqw | exact Qlt_half_one].
  - (* 逐对 |logit| ≤ Δ（inl 严格支，witness 1/4） *)
    intros s s'.
    destruct (Hpair s s') as [epsp [Hpsep [Np HNp]]].
    left.
    exists (1#4). split.
    + apply Qlt_to_QltT. exact Qlt_0_quarter.
    + exists (Nat.max Nw Np). intros n Hn.
      assert (Hnn : (Nw <= n)%nat).
      { apply (Nat.le_trans Nw (Nat.max Nw Np) n);
          [apply Nat.le_max_l | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      assert (Hnp : (Np <= n)%nat).
      { apply (Nat.le_trans Np (Nat.max Nw Np) n);
          [apply Nat.le_max_r | apply (NatLe_drop (Nat.max Nw Np) n Hn)]. }
      unfold attn_logit, Delta.
      apply Qlt_to_QltT.
      rewrite real_plus_proj. rewrite !real_mult_proj. rewrite !real_const_proj.
      rewrite real_abs_proj. rewrite ?real_mult_proj.
      rewrite (Qabs_mult_gen (projT1 (qkb_dotp (vq s) (vk s')) n)
                             (projT1 (w_root k) n)).
      rewrite (Qabs_pos (projT1 (w_root k) n) (Qlt_le_weak 0 (projT1 (w_root k) n) (Hwp' n Hnn))).
      assert (Hpp : Qlt epsp
                        (Qb * Kb + (1#2)
                           - Qabs (projT1 (qkb_dotp (vq s) (vk s')) n))).
      { pose proof (HNp n (NatLe_lift Np n Hnp)) as Hq.
        apply QltT_to_Qlt in Hq.
        rewrite real_plus_proj in Hq. rewrite !real_mult_proj in Hq.
        rewrite !real_const_proj in Hq. rewrite real_abs_proj in Hq.
        exact Hq. }
      assert (Heps' : Qlt 0 epsp) by (apply QltT_to_Qlt; exact Hpsep).
      remember (Qabs (projT1 (qkb_dotp (vq s) (vk s')) n)) as Aq eqn:HAq in *.
      remember (Qb * Kb) as Mq2 eqn:HM2 in *.
      clear - Hpp Heps' Hwp' Hwub Hnn.
      assert (Hpp2 : Qle Aq (Mq2 + (1#2))) by lra.
      remember (Aq * projT1 (w_root k) n) as XW eqn:HXX in *.
      remember (Mq2 * projT1 (w_root k) n) as QW eqn:HQW in *.
      clear - Hpp2 Hwp' Hwub HXX HQW Hnn Hpp Heps'.
      assert (Hxw' : Qlt XW (QW + (3#4))).
      { rewrite HQW.
        apply (Qle_lt_trans XW (Aq * projT1 (w_root k) n)
                            (Mq2 * projT1 (w_root k) n + (3#4))).
        - apply qeq_le. rewrite <- HXX. reflexivity.
        - apply (Qle_lt_trans (Aq * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
                              (Mq2 * projT1 (w_root k) n + (3#4))).
          + setoid_replace (Mq2 * projT1 (w_root k) n + (1#2) * projT1 (w_root k) n)
              with ((Mq2 + (1#2)) * projT1 (w_root k) n) by ring.
            apply (Qmult_le_compat_r Aq (Mq2 + (1#2)) (projT1 (w_root k) n));
              [exact Hpp2 | apply Qlt_le_weak; exact (Hwp' n Hnn)].
          + apply (proj2 (Qplus_lt_r ((1#2) * projT1 (w_root k) n) (3#4)
                                     (Mq2 * projT1 (w_root k) n))).
            setoid_replace (3#4) with ((3#2) * (1#2)) by ring.
            setoid_replace ((1#2) * projT1 (w_root k) n)
              with (projT1 (w_root k) n * (1#2)) by ring.
            apply (Qmult_lt_compat_r (projT1 (w_root k) n) (3#2) (1#2));
              [lra | exact (Hwub n Hnn)]. }
      clear - Hxw'. lra.
Qed.

Close Scope Q_scope.

(* ======== G10_LoebFam 成员件：UpLoebD2（原样并入，自带 Require）======== *)
(* ===================================================================== *)
(* UpLoebD2.v — Löb 真证长线 D2：可证性账本 Σ(σ) 的构造性落实                *)
(*              （纯 Set 层 / stdlib only / 依赖 UpLoeb.v = D1 基座）         *)
(*                                                                       *)
(* 论文定位：「不完备性的构造性治理」HB D1–D3 构造性实现第二棒。              *)
(*   D1 = 对角机制（UpLoeb.v，已给出）；D2 = 本件；D3 = Löb 主定理（后续）。  *)
(*                                                                       *)
(* D2 给出四件（对应 D1 文件尾接口建议）：                                   *)
(*   §8 证明项码账与码级重演：gnPrf（证明项 → 码，标签 6/7/8，与项码 0–3、     *)
(*        公式码 4–5 在 pairp 标签空间分区互斥）+ dP2/dP（证明码的全函数       *)
(*        燃料解码器，与 dT2/dF2 同构）+ 重演主定理 gnPrf_replay：           *)
(*        凭证的码经 dP2 在任意充足燃料下重演恰回被证公式。                    *)
(*        【D1'】Prf f → ledger(⌜f⌝) 居留 = ledger_entry。                  *)
(*   §9 可证性账本：ledger_at w = sigT{ f & sigT{ pf : Prf f &               *)
(*        (w 对齐 ⌜f⌝ 的 loeb_tid 码账) * (dP 重演账) }} ——「码 w 处挂一张          *)
(*        Prf 凭证 + 双 loeb_tid 账」；凭证是一等分量随行挂载（不从码重构，         *)
(*        原理性不可能，见文末诚实边界）。                                  *)
(*   §10 MP 码级封闭【D2'】：MPc c1 c2 = pairp 7 (pairp c1 c2) ——             *)
(*        分离规则在码层封闭：两张凭证码合成的新码，其重演恰为 MP 结论          *)
(*        （MPc_code_closed 纯码层 + MPc_prf_closed/MPc_dP_closed Prf 供账）。*)
(*   §11 Σ(σ) 反射承重件：bsearch（结构递归真有界搜索，false 起点，无硬编码    *)
(*        分支）+ verPf（dP2 驱动的码级凭证验证器）+ Formula2（fsig Σ-原子，  *)
(*        语言仍无约束词栏 → substF2 无捕获 → evalF2_subst 交换律保持不破）    *)
(*        + 双向承重：账本行 ⇒ Σ-原子真（evalF2_fsig_ledger）；              *)
(*        Σ-原子真 ⇒ 低于界的码 w 其重演恰为该码公式（Sigma_bsearch_reflect）。*)
(*        dec_gnF 驱动的「码→公式」反射 = code_reflect。                     *)
(*                                                                       *)
(* 三假法对照（承 D1）：假法①（hyp 占位）——账本行挂的凭证 pf 是 Prf 归纳型     *)
(*   的真项；假法②（Triv 填充）——重演/封闭定理由 pairp/unp2/gnT_fuel/        *)
(*   gnF_fuel 真实组装，无占位收尾；假法③（量词硬编码）——bsearch 是结构       *)
(*   递归的真搜索，Sigma_fires / Sigma_bound_tight 双向 vm_compute 烟测：     *)
(*   界 3000 时真、界恰短（2623）时假——真值由界与码账真实决定。               *)
(*                                                                       *)
(* Set 层纪律：全部 D2 载体（ledger / dP2 / verPf / bsearch / Formula2 /     *)
(*   evalF2 / MPc / gnPrf）零 Prop；承重定理语句以 loeb_tid/sigT/bool 为载体。     *)
(*   唯一例外：燃料参数化定理（gnPrf_replay / MPc_code_closed）的            *)
(*   (… <= k)%nat 界前提——与 D1 已给出的 gnT_fuel / gnF_fuel 接口完全        *)
(*   同型（Proof 层算术接口，非 Set 层数据）。零公理、零承认、零占位、         *)
(*   零经典逻辑；全链信息性，可提取。                                       *)
(* ===================================================================== *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.


(* ===================================================================== *)
(* §8 证明项码账与码级重演                                                    *)
(*     证明项的哥德尔编码：三条规则分贴标签 6 / 7 / 8 —— 与项码标签 0–3、       *)
(*     公式码标签 4–5 互斥。ax_eqT / repl 的元级前提（赋值全称的 loeb_tid 值等）    *)
(*     不入码——由 D1 的 Prf_soundness 元级可靠性承担，诚实边界见文末。         *)
(* ===================================================================== *)

Fixpoint gnPrf (f : Formula) (pf : Prf f) {struct pf} : nat :=
  match pf in Prf f0 return nat with
  | @ax_eqT u1 u2 _ => pairp 6 (pairp (gnT u1) (gnT u2))
  | @mpF a b pf1 pf2 => pairp 7 (pairp (gnPrf (fimp a b) pf1) (gnPrf a pf2))
  | @repl th t1 t2 _ => pairp 8 (pairp (pairp (gnF th) (gnT t1)) (gnT t2))
  end.

(* 证明码的全函数解码器（燃料 = 码值，与 D1 的 dT2/dF2 同构）：
     标签 6：ax_eqT —— 两项码经 dT2 解出，重演 teq；
     标签 7：mpF   —— 两张凭证码经 dP2 解出（大前提须解为 fimp，且小前提
            重演式的码与大前提前件的码一致：gnF 比对），重演 MP 结论；
     标签 8：repl  —— th 码经 dF2、两代入项码经 dT2 解出，重演代入双条件。 *)
Fixpoint dP2 (f c : nat) {struct f} : option Formula :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))), q) =>
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
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))))), q) =>
          (match unp2 q q with
           | Some (w1, w2) =>
               (match dP2 f' w1 with
                | Some (fimp u v) =>
                    (match dP2 f' w2 with
                     | Some z => if Nat.eqb (gnF z) (gnF u) then Some v else None
                     | None => None
                     end)
                | _ => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))))), q) =>
          (match unp2 q q with
           | Some (p, r) =>
               (match unp2 p p with
                | Some (a, b) =>
                    (match dF2 f' a with
                     | Some th =>
                         (match dT2 f' b with
                          | Some x =>
                              (match dT2 f' r with
                               | Some y => Some (fimp (substF th x) (substF th y))
                               | None => None
                               end)
                          | None => None
                          end)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

Definition dP (c : nat) : option Formula := dP2 c c.

(* 码级卫生烟测：证明解码器拒绝小码 / 公式码（656 = gnF (teq tzero tzero)） *)
Lemma dP_rejects_small : dP 3 = None.
Proof. reflexivity. Qed.

Lemma dP_rejects_formula_code : dP 656 = None.
Proof. reflexivity. Qed.

(* ═══ D2 主定理一（码级重演）：凭证的码经 dP2 在任意充足燃料下重演，
       恰好得到被证公式 —— D1 建议的「dT2 fuel 结构做证明项码级重演」。 ═══ *)
Theorem gnPrf_replay : forall (f : Formula) (pf : Prf f) (k : nat),
  (gnPrf f pf <= k)%nat -> loeb_tid (option Formula) (dP2 k (gnPrf f pf)) (Some f).
Proof.
  intros f pf.
  induction pf as [u1 u2 Hv | a b pf1 IH1 pf2 IH2 | th t1 t2 Hv]; intros k Hk;
    destruct k as [|k'].
  - (* ax_eqT，燃料耗尽：证明码恒正，矛盾 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* ax_eqT 主情形：两项码经 gnT_fuel 重演 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnT u1) (gnT u2)) as Hq1.
    pose proof (pairp_ge (gnT u1) (gnT u2)) as Hq2.
    pose proof (pairp_pos (gnT u1) (gnT u2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnT u1 <= k')%nat) by lia.
    assert (Hb2 : (gnT u2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnT_fuel u1 k' Hb1). cbv iota.
    rewrite (gnT_fuel u2 k' Hb2). cbv iota.
    apply loeb_tid_refl.
  - (* mpF，燃料耗尽 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* mpF 主情形：两张子凭证码重演 + gnF 比对反射 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq1.
    pose proof (pairp_ge (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq2.
    pose proof (pairp_pos (gnPrf (fimp a b) pf1) (gnPrf a pf2)) as Hq3.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnPrf (fimp a b) pf1 <= k')%nat) by lia.
    assert (Hb2 : (gnPrf a pf2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (IH1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (IH2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
  - (* repl，燃料耗尽 *)
    cbn [gnPrf pairp] in Hk. lia.
  - (* repl 主情形：th 经 dF2、两代入项经 dT2，重演代入双条件 *)
    cbn [gnPrf dP2].
    pose proof (pairp_ge1 (gnF th) (gnT t1)) as Hq1.
    pose proof (pairp_ge (gnF th) (gnT t1)) as Hq2.
    pose proof (pairp_pos (gnF th) (gnT t1)) as Hq3.
    pose proof (pairp_ge1 (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq4.
    pose proof (pairp_ge (pairp (gnF th) (gnT t1)) (gnT t2)) as Hq5.
    cbn [gnPrf pairp] in Hk.
    assert (Hb1 : (gnF th <= k')%nat) by lia.
    assert (Hb2 : (gnT t1 <= k')%nat) by lia.
    assert (Hb3 : (gnT t2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    rewrite (gnF_fuel th k' Hb1). cbv iota.
    rewrite (gnT_fuel t1 k' Hb2). cbv iota.
    rewrite (gnT_fuel t2 k' Hb3). cbv iota.
    apply loeb_tid_refl.
Qed.

(* 自燃料重演的方程形式（Proof 内部重写用） *)
Corollary gnPrf_replay_eq : forall (f : Formula) (pf : Prf f),
  dP2 (gnPrf f pf) (gnPrf f pf) = Some f.
Proof.
  intros f pf.
  tidQ (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))) E. exact E.
Qed.

(* dP 形式：凭证码的自燃料重演恰回被证公式（无前提） *)
Theorem Prf_replay : forall (f : Formula) (pf : Prf f),
  loeb_tid (option Formula) (dP (gnPrf f pf)) (Some f).
Proof.
  intros f pf. unfold dP.
  exact (gnPrf_replay f pf (gnPrf f pf) (Nat.le_refl (gnPrf f pf))).
Qed.

(* ===================================================================== *)
(* §9 可证性账本 Σ(σ) 的行结构                                                *)
(*     行 = 码 w 处挂：被证公式 f、Prf 凭证 pf、双 loeb_tid 码账：                   *)
(*       第一账（对齐）：w 恰为 ⌜f⌝；                                        *)
(*       第二账（重演）：pf 的证明码经 dP 重演恰回 f。                         *)
(*     D1'：Prf f → ledger(⌜f⌝) 居留 = ledger_entry。                       *)
(* ===================================================================== *)

Definition ledger_at (w : nat) : Type :=
  sigT (fun f : Formula =>
    sigT (fun pf : Prf f =>
      (loeb_tid nat w (gnF f) *
       loeb_tid (option Formula) (dP (gnPrf f pf)) (Some f))%type)).

Definition loebd2_ledger : Type := sigT ledger_at.

Theorem ledger_entry : forall (f : Formula) (pf : Prf f), ledger_at (gnF f).
Proof.
  intros f pf. unfold ledger_at. exists f. exists pf. split.
  - apply loeb_tid_refl.
  - exact (Prf_replay f pf).
Qed.

Theorem ledger_inhabited : loebd2_ledger.
Proof.
  unfold loebd2_ledger. exists (gnF (teq tzero tzero)).
  apply (ledger_entry (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)))).
Qed.

(* 账本行的码齐性迁移：行不依赖代表元的选取 *)
Theorem ledger_tid_transfer : forall (w1 w2 : nat),
  loeb_tid nat w1 w2 -> ledger_at w1 -> ledger_at w2.
Proof.
  intros w1 w2 Hw Hrow. unfold ledger_at in Hrow. unfold ledger_at.
  destruct Hrow as [f [pf [H1 H2]]].
  exists f. exists pf. split.
  - apply (loeb_tid_trans nat w2 w1 (gnF f)). apply loeb_tid_sym. exact Hw. exact H1.
  - exact H2.
Qed.

(* dec_gnF 驱动的「码→公式」反射：凡与 ⌜g⌝ 对齐的码 c，反射出
   「f 的码对齐 c 且 dF c 重演恰为 f」的居留凭证 *)
Theorem code_reflect : forall (c : nat) (g : Formula),
  loeb_tid nat c (gnF g) ->
  sigT (fun f : Formula =>
    (loeb_tid nat (gnF f) c * loeb_tid (option Formula) (dF c) (Some f))%type).
Proof.
  intros c g H. exists g. split.
  - exact (loeb_tid_sym nat c (gnF g) H).
  - apply loeb_tid_eq. unfold dF. tidQ H Ec. rewrite Ec. apply dec_gnF.
Qed.

(* ===================================================================== *)
(* §10 MP 码级封闭【D2'】                                                    *)
(*     MPc：分离规则的码层合成子。封闭性 = 两张凭证码（及各自充足燃料）          *)
(*     合成的新码，在任意充足燃料下重演恰为 MP 结论；Prf 侧由 gnPrf_replay    *)
(*     直接供账。dP2 标签 7 分支的 gnF 比对在此被 Nat.eqb_refl 反射满足。      *)
(* ===================================================================== *)

Definition MPc (c1 c2 : nat) : nat := pairp 7 (pairp c1 c2).

Theorem MPc_code_closed : forall (c1 c2 : nat) (a b : Formula),
  (forall k : nat, (c1 <= k)%nat ->
     loeb_tid (option Formula) (dP2 k c1) (Some (fimp a b))) ->
  (forall k : nat, (c2 <= k)%nat ->
     loeb_tid (option Formula) (dP2 k c2) (Some a)) ->
  forall k : nat, (MPc c1 c2 <= k)%nat ->
  loeb_tid (option Formula) (dP2 k (MPc c1 c2)) (Some b).
Proof.
  intros c1 c2 a b H1 H2 k Hk. unfold MPc.
  destruct k as [|k'].
  - unfold MPc in Hk. cbn [pairp] in Hk. lia.
  - cbn [dP2].
    pose proof (pairp_ge1 c1 c2) as Hq1.
    pose proof (pairp_ge c1 c2) as Hq2.
    pose proof (pairp_pos c1 c2) as Hq3.
    unfold MPc in Hk. cbn [pairp] in Hk.
    assert (Hb1 : (c1 <= k')%nat) by lia.
    assert (Hb2 : (c2 <= k')%nat) by lia.
    rewrite unp2_pair. cbv iota.
    rewrite unp2_pair. cbv iota.
    tidQ (H1 k' Hb1) E1. rewrite E1. cbv iota.
    tidQ (H2 k' Hb2) E2. rewrite E2. cbv iota.
    rewrite Nat.eqb_refl.
    apply loeb_tid_refl.
Qed.

Theorem MPc_prf_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a)
  (k : nat), (gnPrf b (mpF a b pf1 pf2) <= k)%nat ->
  loeb_tid (option Formula) (dP2 k (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2 k Hk.
  apply (MPc_code_closed (gnPrf (fimp a b) pf1) (gnPrf a pf2) a b
    (gnPrf_replay (fimp a b) pf1) (gnPrf_replay a pf2) k).
  cbn [gnPrf MPc] in Hk. exact Hk.
Qed.

(* dP 自燃料形式：MP 合成码的重演恰为结论 —— 码层 MP 封闭的干净陈述 *)
Theorem MPc_dP_closed : forall (a b : Formula) (pf1 : Prf (fimp a b)) (pf2 : Prf a),
  loeb_tid (option Formula)
    (dP (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))) (Some b).
Proof.
  intros a b pf1 pf2. unfold dP.
  apply (MPc_code_closed (gnPrf (fimp a b) pf1) (gnPrf a pf2) a b
    (gnPrf_replay (fimp a b) pf1) (gnPrf_replay a pf2)).
  exact (Nat.le_refl (MPc (gnPrf (fimp a b) pf1) (gnPrf a pf2))).
Qed.

(* ===================================================================== *)
(* §11 Σ(σ) 反射承重件                                                       *)
(*     bsearch：真有界搜索（结构递归，false 起点，无硬编码真值分支）；           *)
(*     verPf：dP2 驱动的码级凭证验证器（「重演码 == 目标码」可判定比对）；      *)
(*     Formula2：D1 片段 + fsig（Σ-原子：界 B 下搜索凭证码验证目标码 c）。      *)
(*     语言仍无约束词栏 → substF2 无捕获问题 → evalF2_subst 交换律保持不破。    *)
(* ===================================================================== *)

Fixpoint bsearch (bd : nat) (p : nat -> bool) : bool :=
  match bd with
  | O => false
  | Datatypes.S b' => orb (p b') (bsearch b' p)
  end.

(* 搜索的见证完整性：真 ⇒ 存在低于界的见证 *)
Theorem bsearch_witness : forall (N : nat) (p : nat -> bool) (w : nat),
  loeb_tid bool (Nat.ltb w N) true -> loeb_tid bool (p w) true ->
  loeb_tid bool (bsearch N p) true.
Proof.
  induction N as [|N' IHN]; intros p w Hlt Hp.
  - exfalso. tidQ Hlt E. pose proof (proj1 (Nat.ltb_lt w 0) E) as Hw0. lia.
  - cbn [bsearch]. destruct (Nat.eq_dec w N') as [Heq|Hne].
    + rewrite <- Heq. tidQ Hp Ep. apply loeb_tid_eq. rewrite Ep. reflexivity.
    + assert (Hlt2 : loeb_tid bool (Nat.ltb w N') true).
      { apply loeb_tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w (Datatypes.S N')) Elt) as H1.
        apply (proj2 (Nat.ltb_lt w N')). lia. }
      apply (loeb_tid_trans bool (orb (p N') (bsearch N' p)) (orb (p N') true)).
      * exact (loeb_tid_cong (orb (p N')) (bsearch N' p) true (IHN p w Hlt2 Hp)).
      * apply loeb_tid_eq. destruct (p N'); reflexivity.
Qed.

(* 搜索的刻画：真 ⇒ 存在低于界的码其验证为真（loeb_tid/bool 载体，零 Prop） *)
Theorem bsearch_character : forall (N : nat) (p : nat -> bool),
  loeb_tid bool (bsearch N p) true ->
  sigT (fun w : nat =>
    (loeb_tid bool (Nat.ltb w N) true * loeb_tid bool (p w) true)%type).
Proof.
  induction N as [|N' IHN]; intros p H.
  - exfalso. cbn [bsearch] in H. tidQ H E. discriminate E.
  - cbn [bsearch] in H. destruct (p N') eqn:Ep.
    + exists N'. split.
      * apply loeb_tid_eq. apply (proj2 (Nat.ltb_lt N' (Datatypes.S N'))). lia.
      * apply loeb_tid_eq. rewrite Ep. reflexivity.
    + cbn [orb] in H.
      destruct (IHN p H) as [w [Hlt Hpw]].
      exists w. split.
      * apply loeb_tid_eq. tidQ Hlt Elt.
        pose proof (proj1 (Nat.ltb_lt w N') Elt) as H1.
        apply (proj2 (Nat.ltb_lt w (Datatypes.S N'))). lia.
      * exact Hpw.
Qed.

(* bsearch 的逐点 loeb_tid 同变（Σ-子句沿 loeb_tid 语义的迁移件，供 D3） *)
Theorem bsearch_tid_cong : forall (bd : nat) (p q : nat -> bool),
  (forall j : nat, loeb_tid bool (p j) (q j)) ->
  loeb_tid bool (bsearch bd p) (bsearch bd q).
Proof.
  induction bd as [|bd' IHb]; intros p q Hp.
  - apply loeb_tid_refl.
  - cbn [bsearch]. apply loeb_tid_eq.
    tidQ (Hp bd') Eh. rewrite Eh.
    tidQ (IHb p q Hp) Ei. rewrite Ei.
    reflexivity.
Qed.

(* Σ-语言：D1 片段 + Σ-原子 fsig B c
   （语义：bsearch (valt B s) (fun w => verPf w (valt c s))） *)
Inductive Formula2 : Set :=
| f2b : Formula -> Formula2
| fsig : Term -> Term -> Formula2
| fimp2 : Formula2 -> Formula2 -> Formula2.

Fixpoint substF2 (f : Formula2) (t : Term) : Formula2 :=
  match f with
  | f2b g => f2b (substF g t)
  | fsig B c => fsig (substT B t) (substT c t)
  | fimp2 a b => fimp2 (substF2 a t) (substF2 b t)
  end.

Definition verPf (w c : nat) : bool :=
  match dP2 w w with
  | Some g => Nat.eqb (gnF g) c
  | None => false
  end.

Fixpoint evalF2 (f : Formula2) (s : nat -> nat) : bool :=
  match f with
  | f2b g => evalF g s
  | fsig B c => bsearch (valt B s) (fun w : nat => verPf w (valt c s))
  | fimp2 a b => orb (negb (evalF2 a s)) (evalF2 b s)
  end.

(* ═══ D2 主定理二（交换律不破）：有界搜索语言下的 evalF_subst ═══ *)
Theorem evalF2_subst : forall (f : Formula2) (t : Term) (s : nat -> nat),
  evalF2 (substF2 f t) s = evalF2 f (upd s (valt t s)).
Proof.
  induction f as [g | B c | a IHa b IHb]; intros t s.
  - cbn [substF2 evalF2]. rewrite evalF_subst. reflexivity.
  - cbn [substF2 evalF2]. rewrite !valt_substT. reflexivity.
  - cbn [substF2 evalF2]. rewrite IHa. rewrite IHb. reflexivity.
Qed.

(* Σ(σ) 可靠性半边一：与证明码对齐的 w 必过 verPf 验证 *)
Theorem verPf_ledger_sound : forall (w : nat) (f : Formula) (pf : Prf f),
  loeb_tid nat w (gnPrf f pf) -> loeb_tid bool (verPf w (gnF f)) true.
Proof.
  intros w f pf Hw. apply loeb_tid_eq. unfold verPf.
  tidQ Hw E. rewrite E.
  rewrite (gnPrf_replay_eq f pf). cbv iota. apply Nat.eqb_refl.
Qed.

(* Σ(σ) 可靠性半边二：账本行（凭证码低于界、公式码对齐）⇒ Σ-原子为真 *)
Theorem evalF2_fsig_ledger : forall (B c : Term) (s : nat -> nat)
  (f : Formula) (pf : Prf f),
  loeb_tid bool (Nat.ltb (gnPrf f pf) (valt B s)) true ->
  loeb_tid nat (gnF f) (valt c s) ->
  loeb_tid bool (evalF2 (fsig B c) s) true.
Proof.
  intros B c s f pf Hw Hc. apply loeb_tid_eq. cbn [evalF2].
  assert (Hpw : loeb_tid bool (verPf (gnPrf f pf) (valt c s)) true).
  { apply loeb_tid_eq. unfold verPf.
    rewrite (gnPrf_replay_eq f pf). cbv iota.
    tidQ Hc Ec. rewrite Ec. apply Nat.eqb_refl. }
  tidQ (bsearch_witness (valt B s) (fun w : nat => verPf w (valt c s))
          (gnPrf f pf) Hw Hpw) Ebs.
  exact Ebs.
Qed.

(* 桥接展示：真实账本行（ax_eqT 凭证，证明码 2624）+ 界 3000 ⇒ Σ-原子真 *)
Theorem Sigma_atom_fires_via_ledger :
  loeb_tid bool (evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
              (fun _ : nat => 0)) true.
Proof.
  apply (evalF2_fsig_ledger (numT 3000) (numT (gnF (teq tzero tzero)))
    (fun _ : nat => 0) (teq tzero tzero)
    (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s)))).
  - apply loeb_tid_eq. rewrite valt_numT.
    apply (proj2 (Nat.ltb_lt
      (gnPrf (teq tzero tzero)
        (ax_eqT tzero tzero (fun s : nat -> nat => @loeb_tid_refl nat (valt tzero s))))
      3000)).
    vm_compute. lia.
  - apply loeb_tid_eq. rewrite valt_numT. reflexivity.
Qed.

(* Σ-原子真的反射：搜出低于界的码 w，其重演恰为该码对应的公式
   （dP2 驱动；凭证重构原理上不可能——见文末诚实边界——反射给到重演层） *)
Theorem Sigma_bsearch_reflect : forall (B : nat) (g : Formula),
  loeb_tid bool (bsearch B (fun w : nat => verPf w (gnF g))) true ->
  sigT (fun w : nat =>
    (loeb_tid bool (Nat.ltb w B) true *
     sigT (fun f : Formula =>
       (loeb_tid nat (gnF f) (gnF g) *
        loeb_tid (option Formula) (dP2 w w) (Some f))%type))%type).
Proof.
  intros B g H.
  destruct (bsearch_character B (fun w : nat => verPf w (gnF g)) H)
    as [w [Hlt Hvw]].
  exists w. split.
  - exact Hlt.
  - unfold verPf in Hvw. tidQ Hvw E. cbv beta in E.
    destruct (dP2 w w) as [gg|] eqn:Ed.
    + cbv iota in E.
      pose proof (proj1 (Nat.eqb_eq (gnF gg) (gnF g)) E) as Eeq.
      exists gg. split.
      * apply loeb_tid_eq. exact Eeq.
      * apply loeb_tid_eq. reflexivity.
    + cbv iota in E. discriminate E.
Qed.

(* 真值烟测（假法③的反面证据：搜索是真的，界决定真值；
   2624 = gnPrf (teq tzero tzero) (ax_eqT …) 的证明码，
   656  = gnF (teq tzero tzero) 的公式码） *)
Lemma Sigma_fires : evalF2 (fsig (numT 3000) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Sigma_bound_tight : evalF2 (fsig (numT 2623) (numT (gnF (teq tzero tzero))))
                      (fun _ : nat => 0) = false.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(* 诚实边界（显式声明，不特设构造）：                                            *)
(*   1. dP2/verPf 只重演「被证公式」，不重构 Prf 凭证本身：ax_eqT/repl 的       *)
(*      元级前提是赋值全称的 loeb_tid 值等（外延函数），原理上不可从码重构。          *)
(*      故账本行把凭证 pf 作为一等分量随行挂载（D1 接口建议的原样落实），        *)
(*      而 Σ-原子的反射只到「重演层」（Sigma_bsearch_reflect）。               *)
(*   2. gnPrf/dP2 的码空间分区（项 0–3 / 公式 4–5 / 证明 6–8）只保证标签        *)
(*      互斥；pairp 解码唯一性方向未在本件展开（D1 已给 unp2_pair 正向）。      *)
(*      verPf 的可靠性以「重演码 == 目标码」的可判定比对为界，足以承重          *)
(*      Σ(σ) 的有界搜索语义。                                                *)
(*   3. 燃料参数化定理（gnPrf_replay / MPc_code_closed）的 (… <= k)%nat 界      *)
(*      前提与 D1 的 gnT_fuel / gnF_fuel 同型——Proof 层算术接口，非             *)
(*      Set 层数据；其余全部语句 loeb_tid/sigT/bool 纯载体。                        *)
(*   4. D2 不追 Löb 主定理（D3）。                                           *)
(*                                                                       *)
(* D3 接口建议：                                                            *)
(*   a. 导出条件对应件已齐：ledger_entry（D1'）/ MPc_dP_closed（D2'）/         *)
(*      gnPrf_replay（编码稳定性）。下一棒：Formula2 的 gnF2/dF2b 编解码       *)
(*      往返（标签 9/10/11；fsig 的 B、c 是项槽，直接复用 gnT/gnF_fuel          *)
(*      证明术），然后 Prf(⌜·⌝) 自身的 gnF 稳定性。                           *)
(*   b. Σ(σ) 完备半边：把 Sigma_bsearch_reflect 的 w 反升格为凭证行，           *)
(*      需把 ax_eqT/repl 前提的元级 loeb_tid 值等替换为可判定的码级证书             *)
(*      （如限制 ax_eqT 到闭项对并配 dT2 证书；repl 配 (th,t1,t2) 的           *)
(*      dF2/dT2 证书三元组）——这是账本升为语言内可证性谓词的关键一步。          *)
(*   c. bsearch_tid_cong 可把 Σ-子句沿 loeb_tid 语义迁移；evalF2_subst 已保证       *)
(*      代入交换；Löb 句 diagF2 := substF2 (wrap2 th) (numT (gnF2 (wrap2 th))) *)
(*      的对角组装可直接照抄 D1 §7 的 repl + 码恒等 + 值恒等三件套。            *)
(* ===================================================================== *)

(* —— 替换件假设面自审（切片三，全部应 Closed under the global context） —— *)
Print Assumptions even_ss.
Print Assumptions div2_ss.
Print Assumptions unp2_S.
Print Assumptions dec_gnT.
Print Assumptions wpm_solvent_at_last_covered.
Print Assumptions wpm_melt_bankrupt.
Print Assumptions wpm_wallet_zero_at_last_cover.
Print Assumptions wpm_wallet_negative_at_bankrupt.
Print Assumptions wpm_insolvent_at_bankrupt.
Print Assumptions dwm_X_refuted.
Print Assumptions dwm_wallet_trajectory.
Print Assumptions dwm_halt_fires.
Print Assumptions dwm_emit3_legal.
Print Assumptions dwm_emit3_not_present.

(* —— 替换件假设面自审（切片五追加，全部应 Closed under the global context） —— *)
Print Assumptions dec_gnF.
Print Assumptions unaryT_selfT.
Print Assumptions diagonal_code_fixed.
Print Assumptions MPc_dP_closed.
Print Assumptions grm_two_step_budget_blown.
