(* ============================================================ *)
(* ToyR 玩具证替换件 —— T261 台账席 战役包V（tier2 十二批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   path2_conservation_T（原 L250，3 句玩具证）                          *)
(*   honest_stop_le（原 L71，3 句玩具证）                                 *)
(* ============================================================ *)

(* ============================================================ *)
(* StopTimeConservation.v —— C5 可选停时守恒记账（A2 组合榜组 5）      *)
(*                                                              *)
(* 装配来源：                                                    *)
(*   A 件（UpStopTime.v）                                        *)
(*     A1 :208 grun_budget      生成器头投影：链头预算 = 初始预算 b   *)
(*     A2 :221 grun_budget_at   守卫链在停时处（深度 n ≤ b）预算恒等：*)
(*                              gbudget_at n (grun k b c) = b - n   *)
(*   B 件（UpDissip.v）                                           *)
(*     B1 :186 bond_exchange_conservation 每边交换守恒：             *)
(*                              eps_in = eps_out + edge_diss         *)
(*     B2 :297 path_dissipation_additive  路径耗散可加：             *)
(*                              复合边耗散 = 段1耗散 + 段2耗散        *)
(*                                                              *)
(* 主件（可选停时型守恒记账）stoptime_conservation_master：          *)
(*   同一诚实停时 τ 处，两本账同时封平：                             *)
(*   nat 预算账：停时剩余 gbudget_at τ + 累计耗散 gdiss_at τ = 初始 b；*)
(*              （即击破时刻总量分解：初始 = 剩余 + 累计耗散，        *)
(*                停时剩余 = b − τ、前缀累计耗散 = τ，见推论）         *)
(*   Q  eps 账 ：初始 eps = τ 步兑换后剩余 + τ 步累计耗散（复合边）。  *)
(*   honest_stop τ ch ≜ τ 不越过链头预算（观测不超出生产窗口），       *)
(*   经 A1 换形为 NatLe τ b，在 nat 账中实质使用。                   *)
(*                                                              *)
(* 语义：把 A2「停时处的预算恒等」与 B2「路径耗散可加」拼成完整        *)
(*   记账守恒：B1 逐边守恒沿迭代闭合成有限步显式守恒（n 步归纳形        *)
(*   diss_iter_conservation），S5 给出停时前缀可加（账本无重计）。     *)
(*                                                              *)
(* 层位纪律：nat 侧出口 Id/NatLe/And（Set 层）；Q 侧与 B 件同口径（==） *)
(*   另给 T 化出口 path2_conservation_T（Qeq_bool→Id）。             *)
(*   纯构造性，全部 Qed，文末 Print Assumptions 留痕。               *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpBudgetReal.
Require Import UpConstitution.
Require Import UpStopTime.
Require Import UpDissip.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 记账对象：诚实停时 + 链侧累计耗散                              *)
(* ============================================================ *)

(* 诚实停时：停时 τ 对链 ch 诚实 = 观测深度不越过链头预算            *)
(*   （可选停时的离散形态：τ 是链生产窗口内的合法观测点）。            *)
Definition honest_stop (tau : nat) (ch : GChain) : Set :=
  NatLe tau (gchain_budget ch).

(* 链侧累计耗散：每步耗散 = 本节点头预算 − 下一节点头预算，            *)
(*   触底节点（gstop）清偿完毕、耗散记零（清零制口径，与 gbudget_at 同）。 *)
Fixpoint gdiss_at (n : nat) (ch : GChain) : nat :=
  match n with
  | O => 0%nat
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => 0%nat
      | gstep b _ tl =>
          ((b - gchain_budget tl) + gdiss_at m tl)%nat
      end
  end.

(* ============================================================ *)
(* §1 A 件侧支撑：停时前缀长度件 + 无界预算恒等件 + 前缀耗散显式公式件  *)
(* ============================================================ *)

(* 停时前缀长度件：诚实停时经 A1 换形 ⟹ τ 落在生产窗口 [0, b] 内      *)
Lemma honest_stop_le : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) -> (tau <= b)%nat.
Proof.
  intros k tau b c H.
  exact (NatLe_drop tau b
           (id_trans (id_sym (id_cong (Nat.leb tau) (grun_budget k b c))) H)).
Qed.

(* 无界预算恒等件：A2 去守卫的饱和扩展——任意深度（含触底后清零段）      *)
(*   均有 gbudget_at n (grun k b c) = b - n（nat 减法饱和至 0）。      *)
Lemma grun_budget_at_any : forall (k : Q) (n b : nat) (c : Q),
  Id (gbudget_at n (grun k b c)) (b - n)%nat.
Proof.
  intros k n. induction n as [| n IH]; intros b c.
  - destruct b as [| b']; reflexivity.
  - destruct b as [| b'].
    + reflexivity.
    + change (gbudget_at (Datatypes.S n) (grun k (Datatypes.S b') c))
        with (gbudget_at n (grun k b' (c * (1 - k)))).
      replace (Datatypes.S b' - Datatypes.S n)%nat with (b' - n)%nat by lia.
      apply IH.
Qed.

(* 前缀耗散显式公式件：诚实窗口内，链侧前缀累计耗散恰为步数 τ           *)
(*   （每步严格递减 1：S b' − b' = 1，由 A1 逐层展开）。               *)
Lemma grun_diss_prefix : forall (k : Q) (n b : nat) (c : Q),
  NatLe n b -> Id (gdiss_at n (grun k b c)) n.
Proof.
  intros k n. induction n as [| n IH]; intros b c Hn.
  - reflexivity.
  - destruct b as [| b'].
    + apply NatLe_drop in Hn. lia.
    + change (gdiss_at (Datatypes.S n) (grun k (Datatypes.S b') c))
        with ((Datatypes.S b' - gchain_budget (grun k b' (c * (1 - k)))
               + gdiss_at n (grun k b' (c * (1 - k))))%nat).
      assert (Hg : gchain_budget (grun k b' (c * (1 - k))) = b').
      { apply RealSetoid.Id_eq. apply (grun_budget k b' (c * (1 - k))). }
      rewrite Hg.
      assert (Hd : gdiss_at n (grun k b' (c * (1 - k))) = n).
      { apply RealSetoid.Id_eq. apply IH. apply NatLe_lift.
        apply NatLe_drop in Hn. lia. }
      rewrite Hd. apply RealSetoid.eq_Id. lia.
Qed.

(* ============================================================ *)
(* §2 nat 记账主件：停时处预算守恒                                   *)
(* ============================================================ *)

(* 主件（nat 账）：诚实停时 τ 处，剩余 + 累计耗散 = 初始预算。          *)
(*   装配：honest_stop_le（A1 换形）⟹ τ ≤ b；A2 给剩余 = b − τ；       *)
(*   前缀耗散公式给累计耗散 = τ；合账 (b−τ)+τ = b。                   *)
Theorem stoptime_conservation : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) (gdiss_at tau (grun k b c))) b%nat.
Proof.
  intros k tau b c Hstop.
  pose proof (honest_stop_le k tau b c Hstop) as Hle.
  pose proof (grun_budget_at k tau b c (NatLe_lift tau b Hle)) as Hb.
  pose proof (grun_diss_prefix k tau b c (NatLe_lift tau b Hle)) as Hd.
  apply (id_trans (id_cong2 PeanoNat.Nat.add Hb Hd)).
  apply RealSetoid.eq_Id. lia.
Qed.

(* 推论（显式账面）：停时剩余 = b − τ（A2 原形）且 剩余 + τ = b。       *)
Corollary stoptime_ledger_explicit : forall (k : Q) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  And (Id (gbudget_at tau (grun k b c)) (b - tau)%nat)
      (Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) tau) b%nat).
Proof.
  intros k tau b c Hstop.
  pose proof (honest_stop_le k tau b c Hstop) as Hle.
  split.
  - exact (grun_budget_at k tau b c (NatLe_lift tau b Hle)).
  - exact (id_trans
             (id_sym (id_cong2 PeanoNat.Nat.add
                (@id_refl nat (gbudget_at tau (grun k b c)))
                (grun_diss_prefix k tau b c (NatLe_lift tau b Hle))))
             (stoptime_conservation k tau b c Hstop)).
Qed.

(* ============================================================ *)
(* §3 B 件侧装配：eps 迭代兑换账（有限步链的显式守恒，n 步归纳形）       *)
(* ============================================================ *)

(* τ 步兑换后的 eps 余量（外层优先：每步先过边再递归余量）               *)
Fixpoint exch_iter (t : nat) (e : edge_spec) (x : Q) : Q :=
  match t with
  | O => x
  | Datatypes.S m => exch_iter m e (edge_map e x)
  end.

(* τ 步累计耗散：每站耗散 = 本站入参处的 edge_diss（与 B1 同口径）       *)
Fixpoint diss_iter (t : nat) (e : edge_spec) (x : Q) : Q :=
  match t with
  | O => 0%Q
  | Datatypes.S m => edge_diss e x + diss_iter m e (edge_map e x)
  end.

(* 有限步显式守恒（B1 的 n 步归纳闭合）：                              *)
(*   初始 eps = τ 步兑换后余量 + τ 步累计耗散。                        *)
Lemma diss_iter_conservation : forall (t : nat) (e : edge_spec) (x : Q),
  x == exch_iter t e x + diss_iter t e x.
Proof.
  induction t as [| m IH]; intros e x.
  - apply Qeq_sym. apply Qplus_0_r.
  - change (exch_iter (Datatypes.S m) e x) with (exch_iter m e (edge_map e x)).
    change (diss_iter (Datatypes.S m) e x)
      with (edge_diss e x + diss_iter m e (edge_map e x)).
    remember (edge_map e x) as w eqn:Ew.
    remember (exch_iter m e w) as a eqn:Ea.
    remember (diss_iter m e w) as c eqn:Ec.
    remember (edge_map e w) as b eqn:Eb.
    remember (edge_diss e w) as d eqn:Ed.
    pose proof (IH e w) as H1.
    rewrite <- Ea, <- Ec in H1.   (* H1 : w == a + c *)
    pose proof (diss_conservation e w) as H2.
    rewrite <- Eb, <- Ed in H2.   (* H2 : w == b + d *)
    pose proof (diss_conservation e x) as H3.
    rewrite <- Ew in H3.          (* H3 : x == w + edge_diss e x *)
    apply (Qeq_trans x (w + edge_diss e x) (a + (edge_diss e x + c))).
    + exact H3.
    + apply (Qeq_trans (w + edge_diss e x)
               (b + (d + edge_diss e x))
               (a + (edge_diss e x + c))).
      * rewrite H2. ring.
      * rewrite H2 in H1.
        apply (Qeq_trans (b + (d + edge_diss e x))
                   ((b + d) + edge_diss e x)
                   (a + (edge_diss e x + c))).
        -- ring.
        -- apply (Qeq_trans ((b + d) + edge_diss e x)
                     ((a + c) + edge_diss e x)
                     (a + (edge_diss e x + c))).
           ++ rewrite H1. ring.
           ++ ring.
Qed.

(* 停时前缀可加件：累计耗散按停时切分无重计、无遗漏                     *)
(*   （τ1+τ2 总耗散 = 前 τ1 段耗散 + 自 τ1 起 τ2 段耗散）。            *)
Lemma diss_iter_split : forall (s t : nat) (e : edge_spec) (x : Q),
  diss_iter (s + t) e x == diss_iter s e x + diss_iter t e (exch_iter s e x).
Proof.
  induction s as [| m IH]; intros t e x.
  - change (0 + t)%nat with t.
    change (diss_iter 0 e x) with 0%Q.
    change (exch_iter 0 e x) with x.
    apply Qeq_sym. apply Qplus_0_l.
  - change (Datatypes.S m + t)%nat with (Datatypes.S (m + t))%nat.
    change (diss_iter (Datatypes.S (m + t)) e x)
      with (edge_diss e x + diss_iter (m + t) e (edge_map e x)).
    change (diss_iter (Datatypes.S m) e x)
      with (edge_diss e x + diss_iter m e (edge_map e x)).
    change (exch_iter (Datatypes.S m) e x)
      with (exch_iter m e (edge_map e x)).
    pose proof (IH t e (edge_map e x)) as H.
    rewrite H. ring.
Qed.

(* 两段路径的停时余量 / 路径耗散（B2 的分解口径）                       *)
Definition exch2 (e1 e2 : edge_spec) (x : Q) : Q :=
  edge_map e2 (edge_map e1 x).
Definition path_diss2 (e1 e2 : edge_spec) (x : Q) : Q :=
  edge_diss e1 x + edge_diss e2 (edge_map e1 x).

(* B 装配件：两段路径上的记账守恒 = B1（复合边一次记账）× B2（耗散分解）   *)
(*   初始 eps = 两段兑换后余量 + 段1耗散 + 段2耗散。                    *)
Theorem path2_conservation : forall (e1 e2 : edge_spec) (x : Q),
  x == exch2 e1 e2 x + path_diss2 e1 e2 x.
Proof.
  intros e1 e2 x.
  apply (Qeq_trans x
           (edge_map (edge_comp e2 e1) x + edge_diss (edge_comp e2 e1) x)
           (exch2 e1 e2 x + path_diss2 e1 e2 x)).
  - exact (bond_exchange_conservation (edge_comp e2 e1)
             (mk_bond 0%nat 0 x 0%nat)).
  - rewrite edge_compound_affine. rewrite path_dissipation_additive.
    unfold exch2, path_diss2. reflexivity.
Qed.

(* T 化出口：Qeq_bool 反映形（Q 层 T 化口径）                          *)
Theorem path2_conservation_T : forall (e1 e2 : edge_spec) (x : Q),
  Id (Qeq_bool x (exch2 e1 e2 x + path_diss2 e1 e2 x)) true.
Proof.
  intros e1 e2 x.
  exact (sf_qeq_id x (exch2 e1 e2 x + path_diss2 e1 e2 x)
           (path2_conservation e1 e2 x)).
Qed.

(* ============================================================ *)
(* §4 合成主件：可选停时型守恒记账（A×B 同一停时双账封平）               *)
(* ============================================================ *)

(* 合成主件：给定诚实停时 τ（GuardedChain 停时，A1/A2 口径），           *)
(*   nat 预算账：停时剩余 + 累计耗散 = 初始预算 b（击破时刻总量守恒）；    *)
(*   Q  eps  账：初始 eps = τ 步复合边兑换后余量 + τ 步累计耗散          *)
(*              （B1 逐边守恒沿 τ 步迭代闭合）。                        *)
(*   同一 τ 同时封平两本账——可选停时守恒记账的完整形态。                 *)
Theorem stoptime_conservation_master :
  forall (k : Q) (e1 e2 : edge_spec) (bd : bond) (tau b : nat) (c : Q),
  honest_stop tau (grun k b c) ->
  And (Id (PeanoNat.Nat.add (gbudget_at tau (grun k b c)) (gdiss_at tau (grun k b c)))
           b%nat)
      (bd_eps bd == exch_iter tau (edge_comp e2 e1) (bd_eps bd)
                  + diss_iter tau (edge_comp e2 e1) (bd_eps bd)).
Proof.
  intros k e1 e2 bd tau b c Hstop. split.
  - exact (stoptime_conservation k tau b c Hstop).
  - exact (diss_iter_conservation tau (edge_comp e2 e1) (bd_eps bd)).
Qed.

Print Assumptions stoptime_conservation_master.
Print Assumptions stoptime_conservation.
Print Assumptions path2_conservation.
