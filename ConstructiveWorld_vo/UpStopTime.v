(* ============================================================ *)
(* UpStopTime.v *)
(* *)
(* 目的： 可证书化停时原语与 GuardedChain 守恒击穿链。 *)
(* 主件： stmin 停时最小值与 gchain_budget 预算链、gbudget_at / gbottom_at。 *)
(* 依赖： CW_ConstructiveWorld_219、UpBudgetReal、UpConstitution。 *)
(* 备注： 停时为可判定序上的显式构造；预算链与宪法验证器对接。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpStopTime.v —— 可证书化停时原语 + GuardedChain 守恒击穿链        *)
(*                                                              *)
(* 理论来源：成果存档/圆桌会议/ROUNDTABLE-六席圆桌实验-20260907.md    *)
(*   头部候选「可证书化停时原语」——席 4 BDA 击穿反解 × 席 6 SPC      *)

(*   方法论 §5：GuardedChain = 生产性非良基（CoInductive 每步        *)
(*   携带预算见证），席 2 终稿的阈值策略双目标占优定理离散形态。       *)
(*                                                              *)
(* 五件结果：                                                    *)
(*   件 1  GChain/grun      GuardedChain 守恒击穿链                 *)
(*                         （CoInductive + CoFixpoint 生成器，       *)
(*                          每步产出构造子 = 守恒；预算逐项递减）     *)
(*   件 2  guarded_breaks   生产性⟹健全性：预算严格递降的链必触底     *)
(*                         （nat 良基递降的构造性击穿）+ 触底值推论    *)
(*   件 3  minimal_stoptime 最小停时 N* = min{N : c0·(1−κ)^N < eps} *)
(*                         （stsearch 线性搜索；3a 最小性 + 3b 上界单调） *)
(*   件 4  st_dominance     阈值策略双目标占优（离散形态，纯序代数）   *)
(*   件 5  unguarded_*      反面对照：无见证恒值链永不触底，           *)
(*                         与 GuardedChain 分离（无预算⟹停时不存在）  *)
(*                                                              *)
(* 数学核心：q_decay_breaks（UpConstitution）保证存在性；            *)
(*   stsearch 线性搜索输出最小跨阈指数 + 逐前项未跨阈证书；           *)
(*   阈值策略在证书可测策略类中同时极小化合并次数与无效服务数。        *)
(*                                                              *)
(* 层位纪律：语句全 Set 层（Id/NatLe/NatLt/QltT/QleT'/st_QId/sigT/     *)
(*   And/Or/Not），无 Prop 泄露；纯构造性禁词零出现；全部 Qed。      *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpBudgetReal.
Require Import UpConstitution.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §0 本地桥（nat 序 / bool 反映 / Q 换形；宪法席解法口径）          *)
(* ============================================================ *)

(* NatLt 双向桥（NatLt = Id (Nat.ltb n m) true；       *)
(*   库内 natlt_elim/intro 困在 LiveCore section 不可达，本地重建）   *)
Lemma st_natlt_drop : forall n m : nat, NatLt n m -> (n < m)%nat.
Proof.
intros n m H. apply (proj1 (Nat.ltb_lt n m)).
apply RealSetoid.Id_eq. exact H.
Qed.

Lemma st_natlt_lift : forall n m : nat, (n < m)%nat -> NatLt n m.
Proof.
intros n m H. apply RealSetoid.eq_Id. apply (proj2 (Nat.ltb_lt n m)).
exact H.
Qed.

(* QltT 的 bool false 换形：未跨阈 ⟹ 阈值 ≤ 当前值（件 3a 最小性用） *)
Lemma st_qlt_false_ge : forall x y : Q, Id (Qlt_bool x y) false -> QleT' y x.
Proof.
intros x y Hf.
destruct (Q_dec x y) as [[H1 | H2] | H3].
- exfalso.
  assert (Ht : QltT x y) by (apply Qlt_to_QltT; exact H1).
  pose proof (id_trans (id_sym Hf) Ht) as Hc. inversion Hc.
- apply uc_qleT_of_ltT. apply Qlt_to_QltT. exact H2.
- apply Qle_to_QleT'. apply uc_qeq_le. apply Qeq_sym. exact H3.
Qed.

(* st_QId（Qeq_bool 反映）左元换形：x == y 且 y < z ⟹ x < z *)
Definition st_QId (x y : Q) : Set := Id (Qeq_bool x y) true.

Lemma st_qid_refl : forall x : Q, st_QId x x.
Proof. intro x. apply sf_qeq_id. apply Qeq_refl. Qed.

Lemma st_qid_trans : forall a b c : Q, st_QId a b -> st_QId b c -> st_QId a c.
Proof.
intros a b c H1 H2. apply sf_qeq_id.
apply (Qeq_trans a b c (sf_id_qeq a b H1) (sf_id_qeq b c H2)).
Qed.

Lemma st_qltT_qid_l : forall x y z : Q, st_QId x y -> QltT y z -> QltT x z.
Proof.
intros x y z Hq Hlt. apply Qlt_to_QltT.
apply (uc_qeq_lt_l y x z (Qeq_sym x y (sf_id_qeq x y Hq))).
apply QltT_to_Qlt. exact Hlt.
Qed.

(* QltT ⟹ Qle（Prop 序前提位；Qlt_le_weak 宪法席已验证口径） *)
Lemma st_qle_of_ltT : forall x y : Q, QltT x y -> Qle x y.
Proof. intros x y H. apply Qlt_le_weak. apply QltT_to_Qlt. exact H. Qed.

(* 1 − k ≤ 1（由 0 ≤ k；Qplus_le_compat + Qopp 换形，先例口径） *)
Lemma st_qle_one_minus : forall k : Q, Qle 0 k -> Qle (1 - k) 1.
Proof.
intros k Hk.
apply (uc_qeq_le_l (1 + (- k)) (1 - k)%Q 1%Q).
- reflexivity.
- apply (uc_qeq_le_r (1 + 0)%Q 1%Q (1 + (- k))%Q).
  + apply Qplus_0_r.
  + apply Qplus_le_compat.
    * apply Qle_refl.
    * apply (uc_opp_le_shift k Hk).
Qed.

(* nat 最小值（可提取；leb 判定） *)
Definition stmin (a b : nat) : nat := if Nat.leb a b then a else b.

Lemma stmin_le_l : forall a b : nat, NatLe b a -> Id (stmin a b) b.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- apply Nat.leb_le in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
- reflexivity.
Qed.

Lemma stmin_le_r : forall a b : nat, NatLe a b -> Id (stmin a b) a.
Proof.
intros a b H. apply NatLe_drop in H. unfold stmin.
destruct (Nat.leb a b) eqn:E.
- reflexivity.
- apply Nat.leb_gt in E. assert (Heq : a = b) by lia.
  rewrite Heq. reflexivity.
Qed.

(* Id 上的 nat ≤（相等即 ≤） *)
Lemma st_natle_of_id : forall n m : nat, Id n m -> NatLe n m.
Proof.
intros n m H. apply NatLe_lift. apply Nat.leb_le.
assert (E : n = m) by (apply RealSetoid.Id_eq; exact H).
rewrite E. apply Nat.leb_refl.
Qed.

(* ============================================================ *)
(* §1 件 1：GuardedChain 守恒击穿链                                *)
(*   CoInductive：非良基类型；每步 gstep 产出构造子 = 生产性守恒。    *)
(*   gstop：触底节点（剩余预算、终值）；触底后预算清零、终值保持。    *)
(*   grun：CoFixpoint 生成器（守卫条件：递归调用在 gstep 之下），    *)
(*   预算参数逐层严格递减——生产性由 Coq 守卫检查器静态强制。         *)
(* ============================================================ *)

CoInductive GChain : Set :=
| gstop : nat -> Q -> GChain
| gstep : nat -> Q -> GChain -> GChain.

(* 守恒生成器：几何衰减链（率 k、剩余预算 b、累积值 c） *)
CoFixpoint grun (k : Q) (b : nat) (c : Q) : GChain :=
  match b with
  | O => gstop 0 c
  | Datatypes.S b' => gstep (Datatypes.S b') c (grun k b' (c * (1 - k)))
  end.

(* 投影：链头预算 / 链头累积值 *)
Definition gchain_budget (ch : GChain) : nat :=
  match ch with gstop b _ => b | gstep b _ _ => b end.

Definition gchain_head (ch : GChain) : Q :=
  match ch with gstop _ c => c | gstep _ c _ => c end.

(* 观察者：深度 n 处的预算 / 累积值 / 触底检测 *)

Fixpoint gbudget_at (n : nat) (ch : GChain) : nat :=
  match n with
  | O => gchain_budget ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => 0
      | gstep _ _ tl => gbudget_at m tl
      end
  end.

(*   终值口径（保持制）：gstop 触底后累积值冻结。                   *)
Fixpoint ghead_at (n : nat) (ch : GChain) : Q :=
  match n with
  | O => gchain_head ch
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => gchain_head ch
      | gstep _ _ tl => ghead_at m tl
      end
  end.

(*   触底检测：n 步内出现 gstop，或出现预算已尽的 gstep 节点。       *)
Fixpoint gbottom_at (n : nat) (ch : GChain) : bool :=
  match n with
  | O =>
      match ch with
      | gstop _ _ => true
      | gstep b _ _ => Nat.leb b 0
      end
  | Datatypes.S m =>
      match ch with
      | gstop _ _ => true
      | gstep b _ tl => if Nat.leb b 0 then true else gbottom_at m tl
      end
  end.

(* 参照值序列：c·(1−k)^n 的迭代形（与 grun 逐层同步收缩） *)
Fixpoint gval (k : Q) (c : Q) (n : nat) : Q :=
  match n with
  | O => c
  | Datatypes.S m => gval k (c * (1 - k)) m
  end.

(* ---- 件 1 引理组：守恒性 / 预算单调 / 终值 ----- *)

(* 生成器头投影：链头预算即生成预算（destruct 后 match 强制 cofix 展开） *)
Lemma grun_budget : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_budget (grun k b c)) b.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

Lemma grun_head : forall (k : Q) (b : nat) (c : Q),
  Id (gchain_head (grun k b c)) c.
Proof.
intros k b c. destruct b; reflexivity.
Qed.

(* 预算单调：深度 n ≤ b 处预算 = b − n（每步严格递减的逐点形态） *)
Lemma grun_budget_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (gbudget_at n (grun k b c)) (b - n)%nat.
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + apply NatLe_drop in Hn. lia.
  + change (gbudget_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (gbudget_at n (grun k b' (c * (1 - k)))).
    replace (Datatypes.S b' - Datatypes.S n)%nat with (b' - n)%nat by lia.
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* 终值轨迹：深度 n ≤ b 处累积值 = 参照值序列第 n 项 *)
Lemma grun_head_at : forall (k : Q) (n : nat) (b : nat) (c : Q),
  NatLe n b -> Id (ghead_at n (grun k b c)) (gval k c n).
Proof.
intros k n. induction n as [| n IH]; intros b c Hn.
- destruct b as [| b']; reflexivity.
- destruct b as [| b'].
  + apply NatLe_drop in Hn. lia.
  + change (ghead_at (Datatypes.S n) (grun k (Datatypes.S b') c))
      with (ghead_at n (grun k b' (c * (1 - k)))).
    change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
    apply IH. apply NatLe_lift. apply NatLe_drop in Hn. lia.
Qed.

(* 乘法结合律（原子变量形——Q-ring 拒含 Qminus 项，先抽变量化引理） *)
Lemma st_mult_assoc_qeq : forall (a b p : Q), (a * b) * p == a * (b * p).
Proof. intros a b p. ring. Qed.

(* 参照值序列 == 幂形：gval k c n == c·(1−k)^n（st_QId 反映形） *)
Lemma gval_pow_QId : forall (k : Q) (n : nat) (c : Q),
  st_QId (gval k c n) (c * q_pow (1 - k) n).
Proof.
intros k n. induction n as [| n IH]; intros c.
- replace (q_pow (1 - k) 0) with 1%Q by reflexivity.
  apply sf_qeq_id. apply Qeq_sym. apply Qmult_1_r.
- change (gval k c (Datatypes.S n)) with (gval k (c * (1 - k)) n).
  change (q_pow (1 - k) (Datatypes.S n)) with ((1 - k) * q_pow (1 - k) n).
  assert (H1 : Id (Qeq_bool (gval k (c * (1 - k)) n)
                     ((c * (1 - k)) * q_pow (1 - k) n)) true)
    by exact (IH (c * (1 - k))).
  assert (H2 : Id (Qeq_bool ((c * (1 - k)) * q_pow (1 - k) n)
                     (c * ((1 - k) * q_pow (1 - k) n))) true)
    by (apply sf_qeq_id;
        exact (st_mult_assoc_qeq c (1 - k) (q_pow (1 - k) n))).
  exact (st_qid_trans _ _ _ H1 H2).
Qed.

(* 触底检测单调：n 步内触底 ⟹ 后继步内仍触底 *)
(*   修复记录：不动点观察 gbottom_at (S n) (gstep b ..) 里的 Nat.leb b 0   *)
(*   是卡死项——直接 destruct b，令 leb (S b') 0 ≡ false 定义性归约。     *)
Lemma gbottom_mono : forall (n : nat) (ch : GChain),
  Id (gbottom_at n ch) true -> Id (gbottom_at (Datatypes.S n) ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbottom_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbottom_at (Datatypes.S n) tl).
      apply IH.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      exact H.
Qed.

(* 触底 ⟹ 后继深度预算清零（清零制口径；需全程递减前提
   排除「预算 0 仍续步」的空洞链——该前提即 GuardedChain 纪律本体） *)
(*   修复记录：原稿 destruct (Nat.leb b 0) eqn: 留卡死 if，且 Hdec 多传   *)
(*   实参；改为 destruct b + Hdec 单实参 + Id_eq 换形 nat 序后 lia。     *)
Lemma gbottom_true_spend : forall (n : nat) (ch : GChain),
  (forall m : nat, NatLt (gbudget_at (Datatypes.S m) ch) (gbudget_at m ch)) ->
  Id (gbottom_at n ch) true -> Id (gbudget_at (Datatypes.S n) ch) 0%nat.
Proof.
intros n. induction n as [| n IH]; intros ch Hdec H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* gstep 0 触底：全程递减在 m=0 要求尾链预算 < 0——空洞链被排除 *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at 0%nat (gstep (Datatypes.S b') c tl)) with false in H.
      inversion H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * (* gstep 0：同一空洞链排除 *)
      exfalso.
      pose proof (Hdec 0%nat) as Hbad.
      change (gbudget_at 1%nat (gstep 0%nat c tl)) with (gbudget_at 0%nat tl)
        in Hbad.
      change (gbudget_at 0%nat (gstep 0%nat c tl)) with 0%nat in Hbad.
      pose proof (proj1 (Nat.ltb_lt (gbudget_at 0%nat tl) 0%nat)
                    (RealSetoid.Id_eq _ _ Hbad)) as Hlt.
      lia.
    * change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl) in H.
      change (gbudget_at (Datatypes.S (Datatypes.S n)) (gstep (Datatypes.S b') c tl))
        with (gbudget_at (Datatypes.S n) tl).
      apply IH.
      -- (* 递减前提沿 gstep 尾链传输（Hdec 全称量词直接取后继实例） *)
         intros m.
         pose proof (Hdec (Datatypes.S m)) as Hs.
         change (gbudget_at (Datatypes.S (Datatypes.S m)) (gstep (Datatypes.S b') c tl))
           with (gbudget_at (Datatypes.S m) tl) in Hs.
         change (gbudget_at (Datatypes.S m) (gstep (Datatypes.S b') c tl))
           with (gbudget_at m tl) in Hs.
         exact Hs.
      -- exact H.
Qed.

(* 预算尽 ⟹ 触底（无前提形态：检测器计数预算尽的 gstep 节点） *)
Lemma gbottom_true_of_budget0 : forall (n : nat) (ch : GChain),
  Id (gbudget_at n ch) 0%nat -> Id (gbottom_at n ch) true.
Proof.
intros n. induction n as [| n IH]; intros ch H.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + change (gbudget_at 0%nat (gstep b c tl)) with b in H.
    rewrite (RealSetoid.Id_eq b 0%nat H). reflexivity.
- destruct ch as [b c | b c tl].
  + reflexivity.
  + destruct b as [| b'].
    * reflexivity.
    * change (gbudget_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbudget_at n tl) in H.
      change (gbottom_at (Datatypes.S n) (gstep (Datatypes.S b') c tl))
        with (gbottom_at n tl).
      apply IH. exact H.
Qed.

(* ---- 件 1 vm_compute 自测（G3 样例输出源之一） ---- *)
(*   grun (1/2) 4 (8/10)：预算 4→3→2→1→0 触底，值 0.8·(1/2)^n 递减 *)
Eval vm_compute in gbudget_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in ghead_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 4 (grun (1#2) 4 (8#10)).
Eval vm_compute in gbottom_at 3 (grun (1#2) 4 (8#10)).

Lemma test_grun_budget0 : Id (gbudget_at 4 (grun (1#2) 4 (8#10))) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_bottom : Id (gbottom_at 4 (grun (1#2) 4 (8#10))) true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_grun_running3 : Id (gbottom_at 3 (grun (1#2) 4 (8#10))) false.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §2 件 2：生产性⟹健全性（消费 UpConstitution.q_decay_breaks）      *)
(*   生产性：CoFixpoint 生成器每步严格递减预算 ⟹ b 步内必触底；        *)
(*   健全性：以 q_decay_breaks 解出的击穿预算 N 作链预算，             *)
(*   链在深度 N 触底且终值 = c0·(1−κ)^N < eps——停时携带证书。         *)
(* ============================================================ *)


Corollary guarded_ledger_clears : forall (k : Q) (b : nat) (c : Q),
  Id (gbudget_at b (grun k b c)) 0%nat.
Proof.
intros k b c.
assert (Hzz : Id (b - b)%nat 0%nat)
  by (apply RealSetoid.eq_Id; apply Nat.sub_diag).
exact (id_trans (grun_budget_at k b b c (NatLe_lift b b (Nat.le_refl b))) Hzz).
Qed.

(* 生产性 b：预算严格递减的逐点见证（m < b ⟹ 深度 m+1 处预算更小） *)
Lemma grun_budget_strict : forall (k : Q) (b : nat) (c : Q) (m : nat),
  NatLt m b ->
  NatLt (gbudget_at (Datatypes.S m) (grun k b c)) (gbudget_at m (grun k b c)).
Proof.
intros k b c m Hm. apply NatLe_drop in Hm.
assert (H1 : Id (gbudget_at (Datatypes.S m) (grun k b c)) (b - Datatypes.S m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
assert (H2 : Id (gbudget_at m (grun k b c)) (b - m)%nat).
{ apply grun_budget_at. apply NatLe_lift. lia. }
apply st_natlt_lift.
rewrite (RealSetoid.Id_eq _ _ H1).
rewrite (RealSetoid.Id_eq _ _ H2).
lia.
Qed.

(* 生产性 c：任意预算 b 的守恒链在深度 b 必触底 *)
Theorem guarded_productive : forall (k : Q) (b : nat) (c : Q),
  Id (gbottom_at b (grun k b c)) true.
Proof.
intros k b c. apply gbottom_true_of_budget0. apply guarded_ledger_clears.
Qed.

(* 健全性：q_decay_breaks 的击穿预算即守恒链的合格停时——
   链在该深度触底，且触底值（保持制冻结值）严格低于阈值 eps *)
Theorem guarded_breaks : forall (k c0 eps : Q),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  sigT (fun N => And (NatLe 1 N)
           (And (Id (gbottom_at N (grun k N c0)) true)
                (QltT (ghead_at N (grun k N c0)) eps))).
Proof.
intros k c0 eps Hk0 Hk1 Hc0 He.
destruct (q_decay_breaks k c0 eps Hk0 Hk1 Hc0 He) as [N [HN1 HN]].
exists N. split.
- exact HN1.
- split.
  + apply guarded_productive.
  + pose proof (grun_head_at k N N c0 (NatLe_lift N N (Nat.le_refl N))) as Hh.
    rewrite (RealSetoid.Id_eq (ghead_at N (grun k N c0)) (gval k c0 N) Hh).
    exact (st_qltT_qid_l (gval k c0 N) (c0 * q_pow (1 - k) N) eps
             (gval_pow_QId k N c0) HN).
Qed.

(* ============================================================ *)
(* §3 件 3：最小停时可判定构造（Q 层单调谓词线性搜索）                *)
(*   跨阈谓词 P n = (c0·(1−κ)^n < eps)：Qlt_bool 判定、衰减单调。     *)
(*   stsearch 从种子上界 U 线性下扫，返回最小跨阈指数 N* 连同           *)
(*   (界内、已跨阈、逐前项未跨阈) 三联证书；失败分支携带全程未跨阈证。   *)
(* ============================================================ *)

(* 跨阈谓词（可执行） *)
Definition st_pred_decay (k c0 eps : Q) : nat -> bool :=
  fun n => Qlt_bool (c0 * q_pow (1 - k) n) eps.

(* 搜索结果（Set 层）：命中 = 最小指数三联证书；脱靶 = 全程未跨阈证 *)
Definition st_hit (P : nat -> bool) (U : nat) : Set :=
  sigT (fun N => And (NatLe N U)
           (And (Id (P N) true)
                (forall j : nat, NatLt j N -> Id (P j) false))).

Definition st_miss (P : nat -> bool) (U : nat) : Set :=
  forall j : nat, NatLe j U -> Id (P j) false.

Definition st_res (P : nat -> bool) (U : nat) : Set :=
  Or (st_hit P U) (st_miss P U).

(* 搜索步（须 Defined：stsearch 是可执行判定器，提取探针要用其本体） *)
Lemma stsearch_step_0 (P : nat -> bool) : st_res P 0%nat.
Proof.
destruct (P 0%nat) eqn:E0.
- apply inl. exists 0%nat. split.
  + apply NatLe_lift. apply Nat.le_refl.
  + split.
    * apply RealSetoid.eq_Id. exact E0.
    * intros j Hj. exfalso.
      pose proof (proj1 (Nat.ltb_lt j 0%nat) (RealSetoid.Id_eq _ _ Hj)) as Hlt.
      lia.
- apply inr. intros j Hj. apply NatLe_drop in Hj. destruct j as [| j'].
  + apply RealSetoid.eq_Id. exact E0.
  + exfalso. lia.
Defined.

Lemma stsearch_step_S (P : nat -> bool) (U : nat) (r : st_res P U)
  : st_res P (Datatypes.S U).
Proof.
destruct r as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  apply inl. exists N. split.
  + apply NatLe_lift. apply NatLe_drop in HNle. lia.
  + split; assumption.
- destruct (P (Datatypes.S U)) eqn:E.
  + apply inl. exists (Datatypes.S U). split.
    * apply NatLe_lift. apply Nat.le_refl.
    * split.
      -- apply RealSetoid.eq_Id. exact E.
      -- intros j Hj. apply miss. apply NatLe_lift.
         apply NatLe_drop in Hj. lia.
  + apply inr. intros j Hj. apply NatLe_drop in Hj.
    destruct (Nat.eq_dec j (Datatypes.S U)) as [Heq | Hne].
    * rewrite Heq. apply RealSetoid.eq_Id. exact E.
    * apply miss. apply NatLe_lift. lia.
Defined.

(* 线性搜索本体：从上界 U 下扫到 0，保最小命中 *)
Fixpoint stsearch (P : nat -> bool) (U : nat) : st_res P U :=
  match U as u return st_res P u with
  | O => stsearch_step_0 P
  | Datatypes.S U' => stsearch_step_S P U' (stsearch P U')
  end.

(* 非负幂：0 ≤ x ⟹ 0 ≤ x^n（Qmult_le_0_compat 归纳） *)
Lemma st_qpow_nonneg : forall (x : Q) (n : nat), Qle 0 x -> Qle 0 (q_pow x n).
Proof.
intros x n Hx. induction n as [| n IH].
- (* Qle 0 1：经 uc_znat_pos 1（Z.of_nat 1 # 1 ≡ 1 定义性归约） *)
  exact (uc_znat_pos 1%nat).
- change (q_pow x (Datatypes.S n)) with (x * q_pow x n).
  apply Qmult_le_0_compat.
  + exact Hx.
  + exact IH.
Qed.

(* 衰减单调（件 3b 引擎）：n ≤ m 且 n 处已跨阈 ⟹ m 处仍跨阈
   （0 ≤ 1−κ ≤ 1 ⟹ (1−κ)^m ≤ (1−κ)^n，q_pow 指数加法 + uc_pow_le_drop；
   需 c0 ≥ 0 保乘法单调前提 0 ≤ c0·(1−κ)^n） *)
Lemma st_decay_mono : forall (k c0 eps : Q) (n m : nat),
  QltT 0 k -> QltT k 1 -> Qle 0 c0 ->
  NatLe n m -> QltT (c0 * q_pow (1 - k) n) eps ->
  QltT (c0 * q_pow (1 - k) m) eps.
Proof.
intros k c0 eps n m Hk0 Hk1 Hc0 Hle Hn.
apply NatLe_drop in Hle.
pose proof (QltT_to_Qlt _ _ Hn) as Hn'.
pose proof (st_qle_of_ltT 0 k Hk0) as H0k.
assert (H1kle : Qle 0 (1 - k))
  by (apply Qlt_le_weak; exact (uc_lt_opp_shift k 1 (QltT_to_Qlt k 1 Hk1))).
assert (Hle01 : Qle (1 - k) 1) by (apply st_qle_one_minus; exact H0k).
(* 指数裂变：q_pow (1−k) m == q_pow (1−k) n · q_pow (1−k) (m−n) *)
assert (Hdec : c0 * q_pow (1 - k) m
               == (c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat).
{ assert (Hm : (n + (m - n))%nat = m) by lia.
  assert (T2 : q_pow (1 - k) (n + (m - n))%nat == q_pow (1 - k) m)
    by (rewrite Hm; apply Qeq_refl).
  assert (Hpow : q_pow (1 - k) m
                 == q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat).
  { exact (Qeq_trans (q_pow (1 - k) m) (q_pow (1 - k) (n + (m - n))%nat)
             (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat)
             (Qeq_sym (q_pow (1 - k) (n + (m - n))%nat) (q_pow (1 - k) m) T2)
             (uc_pow_add (1 - k) n (m - n)%nat)). }
  rewrite Hpow.
  exact (Qeq_sym ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                 (c0 * (q_pow (1 - k) n * q_pow (1 - k) (m - n)%nat))
                 (st_mult_assoc_qeq c0 (q_pow (1 - k) n)
                    (q_pow (1 - k) (m - n)%nat))). }
(* 差项 ≤ 1 ⟹ 系数乘法收缩 *)
assert (Hgap : Qle ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) n)).
{ apply (uc_qeq_le_r ((c0 * q_pow (1 - k) n) * 1%Q) (c0 * q_pow (1 - k) n)
          ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)).
  - apply Qmult_1_r.
  - apply (uc_qeq_le_r (1%Q * (c0 * q_pow (1 - k) n))
             ((c0 * q_pow (1 - k) n) * 1%Q)
             ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)).
    + apply Qmult_comm.
    + apply (uc_qeq_le_l
               (q_pow (1 - k) (m - n)%nat * (c0 * q_pow (1 - k) n))
               ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
               (1%Q * (c0 * q_pow (1 - k) n))).
      * apply Qmult_comm.
      * apply (Qmult_le_compat_r (q_pow (1 - k) (m - n)%nat) 1%Q
                 (c0 * q_pow (1 - k) n)).
        -- exact (uc_pow_le_drop (1 - k) 0%nat (m - n)%nat H1kle Hle01).
        -- apply Qmult_le_0_compat.
           ++ exact Hc0.
           ++ exact (st_qpow_nonneg (1 - k) n H1kle). }
apply Qlt_to_QltT.
apply (uc_qeq_lt_l ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                   (c0 * q_pow (1 - k) m) eps (Qeq_sym _ _ Hdec)).
apply (Qle_lt_trans ((c0 * q_pow (1 - k) n) * q_pow (1 - k) (m - n)%nat)
                    (c0 * q_pow (1 - k) n) eps).
- exact Hgap.
- exact Hn'.
Qed.

(* 最小停时 N*：存在性 + 3a 最小性证书 + 3b 上界单调证书 *)
Theorem minimal_stoptime : forall (k c0 eps : Q) (U : nat),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun N => And (NatLe N U)
           (And (QltT (c0 * q_pow (1 - k) N) eps)
                (And (forall j : nat, NatLt j N -> QleT' eps (c0 * q_pow (1 - k) j))
                     (forall j : nat, NatLe N j -> QltT (c0 * q_pow (1 - k) j) eps)))).
Proof.
intros k c0 eps U Hk0 Hk1 Hc0 He HU.
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N. split.
  + exact HNle.
  + split.
    * exact hP.
    * split.
      -- (* 3a 最小性：逐前项未跨阈证书 ⟹ eps ≤ 前项值 *)
         intros j Hj. apply st_qlt_false_ge. exact (hmin j Hj).
      -- (* 3b 上界单调：衰减单调把跨阈从 N* 传到一切后继 *)
         intros j Hj.
         exact (st_decay_mono k c0 eps N j Hk0 Hk1
                  (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hj hP).
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* 搜索报告（vm_compute 友好：不打印函数证书） *)
Definition stsearch_report (P : nat -> bool) (U : nat) : nat * bool :=
  match stsearch P U with
  | inl h => (projT1 h, true)
  | inr _ => (U, false)
  end.

(* ============================================================ *)
(* §4 件 4：阈值策略双目标占优（离散形态，纯序代数）                   *)
(*   策略 = 停时指数 + 该处跨阈证书。目标 1 合并次数 = 停时；           *)
(*   目标 2 无效服务数 = st_waste（停时前已跨阈仍在服务的步数）。       *)
(*   N* 同时极小化两目标：占优 1 停时 ≤ 竞品；占优 2 竞品在 [N*,M)      *)
(*   全程跨阈 ⟹ 其无效服务 ≥ 整段差距 M − N*。                        *)
(* ============================================================ *)

(* 无效服务计数器：停时 N 之前已跨阈（P = true）的步数——跨阈后仍在服务即无效 *)
Fixpoint st_waste (P : nat -> bool) (N : nat) : nat :=
  match N with
  | O => 0%nat
  | Datatypes.S m => (st_waste P m + (if P m then 1 else 0))%nat
  end.

(* 最小者的无效服务恰为零（逐前项未跨阈证书逐层累加） *)
Lemma st_waste_zero : forall (P : nat -> bool) (N : nat),
  (forall j : nat, NatLt j N -> Id (P j) false) -> Id (st_waste P N) 0%nat.
Proof.
intros P N. induction N as [| N IH]; intros Hmin.
- reflexivity.
- change (st_waste P (Datatypes.S N))
    with (st_waste P N + (if P N then 1 else 0))%nat.
  rewrite (RealSetoid.Id_eq _ _
             (IH (fun j Hj => Hmin j (st_natlt_lift j (Datatypes.S N)
                       (Nat.lt_lt_succ_r j N (st_natlt_drop j N Hj)))))).
  rewrite (RealSetoid.Id_eq _ _
             (Hmin N (st_natlt_lift N (Datatypes.S N)
                        (Nat.lt_succ_diag_r N)))).
  reflexivity.
Qed.

(* 计数下界：[a, m) 全程跨阈 ⟹ 无效服务 ≥ m − a *)
Lemma st_waste_lower : forall (P : nat -> bool) (a m : nat),
  NatLe a m ->
  (forall j : nat, NatLe a j -> NatLt j m -> Id (P j) true) ->
  NatLe (m - a)%nat (st_waste P m).
Proof.
intros P a m. induction m as [| m IH]; intros Hle Hge.
- apply NatLe_lift.
  change (st_waste P 0%nat) with 0%nat.
  apply NatLe_drop in Hle. lia.
- apply NatLe_lift.
  change (st_waste P (Datatypes.S m))
    with (st_waste P m + (if P m then 1 else 0))%nat.
  destruct (Nat.leb a m) eqn:Ea.
  + assert (H1 : NatLe (m - a)%nat (st_waste P m)).
    { apply IH.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - intros j Hj1 Hj2. apply Hge.
        * exact Hj1.
        * exact (st_natlt_lift j (Datatypes.S m)
                   (Nat.lt_lt_succ_r j m (st_natlt_drop j m Hj2))). }
    apply NatLe_drop in H1. apply NatLe_drop in Hle.
    assert (Ham : (a <= m)%nat) by exact (proj1 (Nat.leb_le a m) Ea).
    assert (Hs : ((Datatypes.S m) - a)%nat = (Datatypes.S (m - a))%nat) by lia.
    rewrite Hs.
    assert (HPm : (P m)%bool = true).
    { apply RealSetoid.Id_eq. apply Hge.
      - exact (NatLe_lift a m (proj1 (Nat.leb_le a m) Ea)).
      - exact (st_natlt_lift m (Datatypes.S m) (Nat.lt_succ_diag_r m)). }
    rewrite HPm.
    change (if true then 1 else 0)%nat with 1%nat.
    lia.
  + apply Nat.leb_gt in Ea. apply NatLe_drop in Hle.
    assert (Hz : ((Datatypes.S m) - a)%nat = 0%nat) by lia.
    rewrite Hz.
    destruct (P m); lia.
Qed.

(* 证书可测策略类：停时 + 该处跨阈见证 *)
Record st_policy (P : nat -> bool) : Set := mk_policy {
  pol_stop : nat;
  pol_break : Id (P pol_stop) true
}.

Arguments pol_stop {P} _.
Arguments pol_break {P} _.
Arguments mk_policy {P} _ _.

(* 双目标占优（纯序代数形态）：对任意持证竞品，
   目标 1：N* ≤ M（合并次数不增）；
   目标 2：waste(Nstar) = 0 且 waste(M) ≥ M − Nstar（无效服务被压制） *)
Theorem st_dominance : forall (P : nat -> bool) (Nstar : nat) (q : st_policy P),
  (forall j : nat, NatLt j Nstar -> Id (P j) false) ->
  Id (P Nstar) true ->
  (forall n m : nat, NatLe n m -> Id (P n) true -> Id (P m) true) ->
  And (NatLe Nstar (pol_stop q))
      (And (Id (st_waste P Nstar) 0%nat)
           (NatLe ((pol_stop q - Nstar)%nat)
                  (st_waste P (pol_stop q)))).
Proof.
intros P Nstar q Hmin hN Hmono. destruct q as [M hM].
split.
- (* 占优 1：M < N* 与逐前项未跨阈证书矛盾 *)
  destruct (Nat.leb Nstar M) eqn:E.
  + exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E)).
  + exfalso.
    pose proof (Hmin M (st_natlt_lift M Nstar
                   (proj1 (Nat.leb_gt Nstar M) E))) as Hf.
    pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra.
- split.
  + exact (st_waste_zero P Nstar Hmin).
  + assert (Hle : NatLe Nstar M).
    { destruct (Nat.leb Nstar M) eqn:E2.
      - exact (NatLe_lift Nstar M (proj1 (Nat.leb_le Nstar M) E2)).
      - exfalso.
        pose proof (Hmin M (st_natlt_lift M Nstar
                       (proj1 (Nat.leb_gt Nstar M) E2))) as Hf.
        pose proof (id_trans (id_sym hM) Hf) as Hcontra. inversion Hcontra. }
    apply st_waste_lower.
    * exact Hle.
    * intros j Hj1 Hj2. exact (Hmono Nstar j Hj1 hN).
Qed.

(* 阈值策略占优的几何衰减实例化：把件 3 的最小停时喂给件 4 的抽象格 *)
Theorem st_thresh_dominance : forall (k c0 eps : Q) (U : nat)
                                     (q : st_policy (st_pred_decay k c0 eps)),
  QltT 0 k -> QltT k 1 -> QltT 0 c0 -> QltT 0 eps ->
  Id (st_pred_decay k c0 eps U) true ->
  sigT (fun Nstar =>
          And (NatLe Nstar (pol_stop q))
              (And (QltT (c0 * q_pow (1 - k) Nstar) eps)
                   (And (Id (st_waste (st_pred_decay k c0 eps) Nstar) 0%nat)
                        (NatLe ((pol_stop q - Nstar)%nat)
                               (st_waste (st_pred_decay k c0 eps) (pol_stop q)))))).
Proof.
intros k c0 eps U q Hk0 Hk1 Hc0 He HU.
assert (Hmono : forall n m : nat,
          NatLe n m -> Id (st_pred_decay k c0 eps n) true ->
          Id (st_pred_decay k c0 eps m) true).
{ intros n m Hle Hn.
  exact (st_decay_mono k c0 eps n m Hk0 Hk1
           (Qlt_le_weak 0%Q c0 (QltT_to_Qlt 0%Q c0 Hc0)) Hle Hn). }
destruct (stsearch (st_pred_decay k c0 eps) U) as [hit | miss].
- destruct hit as [N [HNle [hP hmin]]].
  exists N.
  destruct (st_dominance (st_pred_decay k c0 eps) N q hmin hP Hmono)
    as [Hd1 [Hd2 Hd3]].
  split.
  + exact Hd1.
  + split.
    * exact hP.
    * split.
      -- exact Hd2.
      -- exact Hd3.
- exfalso.
  pose proof (miss U (NatLe_lift U U (Nat.le_refl U))) as Hf.
  pose proof (id_trans (id_sym HU) Hf) as Hcontra. inversion Hcontra.
Qed.

(* ============================================================ *)
(* §5 件 5：反面对照——无预算见证的自指恒值链                          *)
(*   uloop：每步预算恒为 1、终值恒为 c 的自指链（CoFixpoint 守卫允许，   *)
(*   但无递减见证）。三重平凡性：预算永不归零、检测永不触底、停时不存在，  *)
(*   与件 2 的 GuardedChain（预算递减⟹必触底）构成分离。              *)
(* ============================================================ *)

CoFixpoint uloop (c : Q) : GChain := gstep 1%nat c (uloop c).

(* 平凡性 a：预算恒为 1（match 观察者强制 cofix 展开，预算永不清零） *)
Lemma unguarded_budget_const : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 1%nat.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbudget_at (Datatypes.S n) (uloop c)) with (gbudget_at n (uloop c)).
  exact IH.
Qed.

(* 平凡性 b：终值恒为 c（自指恒值，永无改进轨迹） *)
Lemma unguarded_head_const : forall (c : Q) (n : nat),
  Id (ghead_at n (uloop c)) c.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (ghead_at (Datatypes.S n) (uloop c)) with (ghead_at n (uloop c)).
  exact IH.
Qed.

(* 平凡性 c：任意深度检测均为未触底 *)
Lemma unguarded_never_bottoms : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) false.
Proof.
intros c n. induction n as [| n IH].
- reflexivity.
- change (gbottom_at (Datatypes.S n) (uloop c)) with (gbottom_at n (uloop c)).
  exact IH.
Qed.

(* 反面定理：无见证恒值链的停时不存在（触底检测 true 直接矛盾） *)
Theorem unguarded_no_stoptime : forall (c : Q) (n : nat),
  Id (gbottom_at n (uloop c)) true -> Empty_set.
Proof.
intros c n H.
pose proof (unguarded_never_bottoms c n) as Hf.
pose proof (id_trans (id_sym H) Hf) as Hcontra. inversion Hcontra.
Qed.

(* 分离定理：恒值链的账本永不触及清零口径，与 GuardedChain 账本对立 *)
Theorem unguarded_vs_guarded : forall (c : Q) (n : nat),
  Id (gbudget_at n (uloop c)) 0%nat -> Empty_set.
Proof.
intros c n H0.
pose proof (unguarded_budget_const c n) as H1.
pose proof (id_trans (id_sym H0) H1) as Hcontra. inversion Hcontra.
Qed.

(* 平凡性总装（三联观察） *)
Theorem unguarded_trivial : forall (c : Q) (n : nat),
  And (Id (gbudget_at n (uloop c)) 1%nat)
      (And (Id (gbottom_at n (uloop c)) false)
           (Id (ghead_at n (uloop c)) c)).
Proof.
intros c n. split.
- apply unguarded_budget_const.
- split.
  + apply unguarded_never_bottoms.
  + apply unguarded_head_const.
Qed.

(* ---- 件 5 vm_compute 自测 ---- *)
Eval vm_compute in gbottom_at 7 (uloop (1#10)).
Eval vm_compute in gbudget_at 7 (uloop (1#10)).

Lemma test_uloop_never : Id (gbottom_at 7 (uloop (1#10))) false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_uloop_budget : Id (gbudget_at 7 (uloop (1#10))) 1%nat.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §6 件 3/件 4 联合 vm_compute 自测（G3 样例输出源之二）              *)
(*   c0 = 4/5, κ = 1/2, eps = 1/10：跨阈谓词在 n = 4 首次为真         *)
(*   （4/5, 2/5, 1/5, 1/10, 1/20）；stsearch 自上界 5 报最小停时 4。   *)
(* ============================================================ *)

Definition stpred_demo : nat -> bool := st_pred_decay (1#2) (8#10) (1#10).

Eval vm_compute in (stpred_demo 0, stpred_demo 1, stpred_demo 2,
                    stpred_demo 3, stpred_demo 4, stpred_demo 5).
Eval vm_compute in stsearch_report stpred_demo 5.
Eval vm_compute in st_waste stpred_demo 6.

Lemma test_stsearch_min : Id (stsearch_report stpred_demo 5) (4%nat, true).
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_star : Id (st_waste stpred_demo 4) 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_waste_gap : Id (st_waste stpred_demo 6) 2%nat.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §7 提取探针（G3：Obj.magic = 0）                                  *)
(*   提取停时判定器全链：谓词 / 搜索 / 报告 / 无效服务计数 / 幂核。      *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Set Warnings "-extraction-opaque-accessed".
Set Extraction Output Directory ".".
Extraction "upstoptime.ml" st_pred_decay stsearch stsearch_report st_waste q_pow.
