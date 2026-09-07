(* ===================================================================== *)
(* UpSLM.v — SLM v2 熔合不可逆演算（见证擦除演算）Coq 落地                    *)
(*                                                                       *)
(* 立项出处：                                                            *)
(*   ROUNDTABLE.md 席 5 终稿（SLM 2.0 见证擦除演算）；                       *)
(*   排队席位方案-二轮成果Coq化-20260907.md Q6 条目。                        *)
(*                                                                       *)
(* 载体：Z / nat / bool 判定层；语句零 Prop（tid / nle / bool / sigT）。      *)
(* 纪律：纯构造性（禁 Axiom / Admitted / Parameter / Conjecture / Abort）；   *)
(* stdlib only；可提取（探针验 Obj.magic = 0）。                            *)
(*                                                                       *)
(* 定稿决策（设计未定稿处由本席按「结构最简 + 判定层最短」定稿）：               *)
(*  D1 严格性单元 = (权重 w : Z, pos 判词, 生产者 pid : nat)；                 *)
(*     pos 判词取 tid bool (Z.ltb 0 w) true —— bool 判定式的 Set 层恒等，      *)
(*     忠实（Z.ltb_lt 可反演 0 < w）且可提取。                              *)
(*  D2 熔合为一等总函数：fuse2（两单元）/ fuseL_into（带种子序列）              *)
(*     / fuse_all（整账定位带）/ fuse_ledger（两账本合并后熔断）；              *)
(*     产物 agg 只携 (Σw, Σ判词)，无 pid 字段——擦除在类型层落实。              *)
(*  D3 空熔合 = 种子恒等：fuseL_into 以种子聚合元为单位元。                     *)
(*     「账本不制造严格性」落实为：无定位单元则无新聚合元（fuse_all 空带恒等）。 *)
(*  D4 不可逆的构造性刻画 = 具体碰撞见证：两组 pid 互异的前驱（3,4 权重，         *)
(*     pid 7/9 与 pid 5/11）熔合出同一聚合元（tid 判定相等），且前驱在熔合前     *)
(*     由 bool 探针可判定区分、熔合对象对一切 pid 探针失明（探针恒 false）。     *)
(*  D5 花与需求流：spend 取头定位单元（花后 pid 即废）；未 funded 事件永不发射、  *)
(*     原账保真并签发无地址需求票（负向事件产出可再出资义务）；                  *)
(*     赎回 = race-to-mint：任一生产者在自报预算内铸出新定位单元即销票，         *)
(*     票据按代数焚毁（同票不可赎两次），铸造单元完成重定位。                    *)
(*                                                                       *)
(* 六件：                                                                *)
(*  件 1  单元与判词机器（locu / agg / probe_pid + 判词桥 + pos_add 两判词合一） *)
(*  件 2  熔合一等运算（fuse2 / fuseL_into + 和守恒 + Σ>0 健全）                *)
(*  件 3  账本熔合（union_led / fuse_all / fuse_ledger + 总量守恒 + 定位清零）   *)
(*  件 4  不可逆碰撞见证（同产物 / 前驱可判定区分 / 熔后全探针失明 / 总量守恒）    *)
(*  件 5  花：spend 即废（在场判定 / pid 消失 / 总量严格下降 nle 见证）          *)
(*  件 6  多租户安全 + race-to-mint 赎回（未 funded 不发射 / 保真 / 签票；        *)
(*        铸造赎回 / 票据焚毁 / 重定位 / 单票单铸程）                           *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import ZArith_dec.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(* ===================================================================== *)
(* 0. Set 层基建（内联自成果存档 UpPLA.v 前 180 行；不 Require UpPLA）        *)
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

(* 显式命名版 eq 提取（证明内部推理用） *)
Ltac tidQl H Hp :=
  pose proof (match H in tid _ a b return a = b with tid_refl _ _ => eq_refl end) as Hp.

(* Set 层 nle 基本件 *)
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
    + exact (nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ → tid bool (leb) true 桥 *)
Lemma lebT : forall a b : nat, (a <= b)%nat -> tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply tid_refl.
Qed.

Lemma nle_trans : forall a b c : nat, nle a b -> nle b c -> nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply nle_S. exact IH.
Qed.

(* nle 前驱消解：nle (S a) (S b) -> nle a b *)
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

(* nle (S O) O 荒谬件（合法关闭任意 Set 目标） *)
Lemma nle_10_absurd : forall P : Type, nle (S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* Z 层严格序 → nle 编码桥 *)
Lemma zle_to_nle_S : forall a b : Z, (0 <= a)%Z -> (a < b)%Z ->
  nle (S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  assert (Hb : (0 <= b)%Z) by lia.
  apply nle_of_leb.
  assert (Hleb : (Nat.leb (S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b Ha Hb) Hlt). }
  rewrite Hleb. apply tid_refl.
Qed.

(* n≠0 ⟹ |n| 的 nat 编码 ≥ (S O) *)
Lemma to_nat_abs_pos : forall n : Z,
  tid bool (Z.eqb n 0) false -> nle (S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (zle_to_nle_S 0 (Z.abs n)).
  - lia.
  - pose proof (proj2 (Z.abs_pos n) Hne). lia.
Qed.

(* 1 ≤ x ⟹ nle (S O) (Z.to_nat x)（Z 正量 → nle 编码） *)
Lemma zpos_to_nle : forall x : Z, (1 <= x)%Z -> nle (S O) (Z.to_nat x).
Proof.
  intros x Hx.
  assert (Hb : (0 <= x)%Z) by lia.
  assert (Hb1 : (0 <= 1)%Z) by lia.
  apply nle_of_leb. apply lebT.
  exact (proj1 (Z2Nat.inj_le 1 x Hb1 Hb) Hx).
Qed.

(* ===================================================================== *)
(* 件 1. 单元与判词机器                                                      *)
(* ===================================================================== *)

(* tid 层的 eq 桥（证明内部算术收口用） *)
Lemma tid_Z_of_eq : forall x y : Z, x = y -> tid Z x y.
Proof.
  intros x y H. rewrite H. apply tid_refl.
Qed.

Lemma tid_bool_of_eq : forall x y : bool, x = y -> tid bool x y.
Proof.
  intros x y H. rewrite H. apply tid_refl.
Qed.

(* tid bool true false 荒谬件（bool 判定矛盾的合法消去，可关任意 Type 目标） *)
Lemma tid_bool_tf_absurd : forall P : Type, tid bool true false -> P.
Proof.
  intros P H. tidE H. discriminate HE.
Qed.

(* pos 判词构造桥：(0 < a)%Z → tid bool (Z.ltb 0 a) true *)
Lemma ltbT : forall a : Z, (0 < a)%Z -> tid bool (Z.ltb 0 a) true.
Proof.
  intros a H. rewrite (proj2 (Z.ltb_lt 0 a) H). apply tid_refl.
Qed.

(* pos 判词反演桥：tid bool (Z.ltb 0 a) true → (0 < a)%Z（忠实性） *)
Lemma ltbF_inv : forall a : Z, tid bool (Z.ltb 0 a) true -> (0 < a)%Z.
Proof.
  intros a H. tidQl H HE. exact (proj1 (Z.ltb_lt 0 a) HE).
Qed.

(* 定位单元：权重 + pos 判词 + 生产者定位（不可复制的运行时资源） *)
Record locu : Type := mkLocu {
  lu_w : Z ;
  lu_pos : tid bool (Z.ltb 0 lu_w) true ;
  lu_pid : nat
}.

(* 聚合元：只有总量与 Σ 判词，无 pid 字段——定位在类型层被擦除 *)
Record agg : Type := mkAgg {
  ag_sum : Z ;
  ag_pos : tid bool (Z.ltb 0 ag_sum) true
}.

(* ===================================================================== *)
(* 件 2. 熔合一等运算：两判词合一 + 两单元熔为一聚合元                          *)
(* ===================================================================== *)

(* 两判词合一：两条 pos 判词熔为一条 Σ 判词（Σ>0 健全性的构造核心） *)
Lemma pos_add : forall a b : Z,
  tid bool (Z.ltb 0 a) true -> tid bool (Z.ltb 0 b) true ->
  tid bool (Z.ltb 0 (a + b)) true.
Proof.
  intros a b Ha Hb. apply ltbT.
  pose proof (ltbF_inv a Ha). pose proof (ltbF_inv b Hb). lia.
Qed.

(* 熔合（两单元 → 一聚合元）：只携和与 Σ 判词，pid 无处安放 *)
Definition fuse2 (u v : locu) : agg :=
  mkAgg (lu_w u + lu_w v) (pos_add (lu_w u) (lu_w v) (lu_pos u) (lu_pos v)).

(* 定位单元账的和（守恒记账的量） *)
Fixpoint lsum_w (l : list locu) : Z :=
  match l with
  | nil => 0
  | u :: t => lu_w u + lsum_w t
  end.

(* 种子式序列熔合：以聚合元 a 为单位元（空熔合 = 恒等，账本不制造严格性） *)
Fixpoint fuseL_into (a : agg) (l : list locu) : agg :=
  match l with
  | nil => a
  | u :: t => fuseL_into
                (mkAgg (ag_sum a + lu_w u) (pos_add _ _ (ag_pos a) (lu_pos u))) t
  end.

(* 熔合和守恒：产物总量 = 种子 + 各单元权重和 *)
Lemma fuseL_into_sum : forall (l : list locu) (a : agg),
  tid Z (ag_sum (fuseL_into a l)) (ag_sum a + lsum_w l).
Proof.
  induction l as [| u t IH]; intros a.
  - cbn. apply tid_Z_of_eq. lia.
  - cbn. tidQl (IH (mkAgg (ag_sum a + lu_w u) (pos_add _ _ (ag_pos a) (lu_pos u)))) E1.
    rewrite E1. cbn. apply tid_Z_of_eq. lia.
Qed.

(* 熔合健全（Σ>0 沿熔合链不灭）：正种子 + 正单元 ⟹ 产物判词恒真 *)
Lemma fuseL_into_pos : forall (l : list locu) (a : agg),
  tid bool (Z.ltb 0 (ag_sum a)) true ->
  tid bool (Z.ltb 0 (ag_sum (fuseL_into a l))) true.
Proof.
  induction l as [| u t IH]; intros a Hpos.
  - exact Hpos.
  - exact (IH (mkAgg (ag_sum a + lu_w u) (pos_add _ _ (ag_pos a) (lu_pos u)))
              (pos_add _ _ Hpos (lu_pos u))).
Qed.

(* 两单元熔合的守恒与健全（件 2 入口定理） *)
Lemma fuse2_sum : forall u v : locu,
  tid Z (ag_sum (fuse2 u v)) (lu_w u + lu_w v).
Proof.
  intros u v. apply tid_refl.
Qed.

Lemma fuse2_pos : forall u v : locu,
  tid bool (Z.ltb 0 (ag_sum (fuse2 u v))) true.
Proof.
  intros u v. exact (ag_pos (fuse2 u v)).
Qed.

(* ===================================================================== *)
(* 件 3. 账本熔合：两账本合并为单一对象 + 定位清零                             *)
(* ===================================================================== *)

(* 账本 = 定位带 + 聚合带 *)
Record ledger : Type := mkLed {
  led_loc : list locu ;
  led_agg : list agg
}.

Fixpoint lsum_a (l : list agg) : Z :=
  match l with
  | nil => 0
  | a :: t => ag_sum a + lsum_a t
  end.

(* 账本总量（守恒记账的量） *)
Definition led_total (L : ledger) : Z := lsum_w (led_loc L) + lsum_a (led_agg L).

(* 定位探针：pid p 是否仍在账（bool 判定） *)
Definition probe_pid (p : nat) (L : ledger) : bool :=
  existsb (fun x : locu => Nat.eqb (lu_pid x) p) (led_loc L).

(* 账本合并（可逆并置；真熔断在 fuse_all） *)
Definition union_led (L1 L2 : ledger) : ledger :=
  mkLed (led_loc L1 ++ led_loc L2) (led_agg L1 ++ led_agg L2).

Lemma lsum_w_app : forall l1 l2 : list locu,
  tid Z (lsum_w (l1 ++ l2)) (lsum_w l1 + lsum_w l2).
Proof.
  induction l1 as [| u t IH]; intros l2.
  - cbn. apply tid_Z_of_eq. lia.
  - cbn. tidQl (IH l2) E1. rewrite E1. apply tid_Z_of_eq. lia.
Qed.

Lemma lsum_a_app : forall l1 l2 : list agg,
  tid Z (lsum_a (l1 ++ l2)) (lsum_a l1 + lsum_a l2).
Proof.
  induction l1 as [| a t IH]; intros l2.
  - cbn. apply tid_Z_of_eq. lia.
  - cbn. tidQl (IH l2) E1. rewrite E1. apply tid_Z_of_eq. lia.
Qed.

(* 合并守恒：并置零损失（对照：真熔合才擦除） *)
Lemma union_led_total : forall L1 L2 : ledger,
  tid Z (led_total (union_led L1 L2)) (led_total L1 + led_total L2).
Proof.
  intros L1 L2. unfold led_total, union_led. cbn.
  tidQl (lsum_w_app (led_loc L1) (led_loc L2)) E1.
  tidQl (lsum_a_app (led_agg L1) (led_agg L2)) E2.
  apply tid_Z_of_eq. lia.
Qed.

(* 熔断：整条定位带熔为单一聚合元（不可逆主运算） *)
Definition fuse_all (L : ledger) : ledger :=
  match led_loc L with
  | nil => L
  | u :: t => mkLed nil (fuseL_into (mkAgg (lu_w u) (lu_pos u)) t :: led_agg L)
  end.

(* 空带熔断恒等：无定位单元则无新聚合元（账本不制造严格性） *)
Lemma fuse_all_empty_id : forall ags : list agg,
  tid (list agg) (led_agg (fuse_all (mkLed nil ags))) ags.
Proof.
  intros ags. exact (@tid_refl (list agg) ags).
Qed.

(* 熔断总量守恒（非空带档位） *)
Lemma fuse_all_total_cons : forall (u : locu) (t : list locu) (ags : list agg),
  tid Z (led_total (fuse_all (mkLed (u :: t) ags)))
       (lu_w u + lsum_w t + lsum_a ags).
Proof.
  intros u t ags. unfold fuse_all, led_total. cbn.
  tidQl (fuseL_into_sum t (mkAgg (lu_w u) (lu_pos u))) E1.
  apply tid_Z_of_eq. rewrite E1. cbn. lia.
Qed.

(* 两账本熔合为一等对象：先并置再熔断（唯一的账本级熔合入口） *)
Definition fuse_ledger (L1 L2 : ledger) : ledger := fuse_all (union_led L1 L2).

(* 两账本熔合总量守恒（左账定位带非空档位） *)
Lemma fuse_ledger_total_cons : forall (u1 : locu) (t1 : list locu)
                                      (ags1 : list agg) (L2 : ledger),
  tid Z (led_total (fuse_ledger (mkLed (u1 :: t1) ags1) L2))
       (lu_w u1 + lsum_w t1 + lsum_a ags1 + led_total L2).
Proof.
  intros u1 t1 ags1 L2. unfold fuse_ledger, fuse_all, union_led, led_total. cbn.
  tidQl (fuseL_into_sum (t1 ++ led_loc L2) (mkAgg (lu_w u1) (lu_pos u1))) E1.
  tidQl (lsum_w_app t1 (led_loc L2)) E2.
  tidQl (lsum_a_app ags1 (led_agg L2)) E3.
  apply tid_Z_of_eq. rewrite E1, E2, E3. cbn. lia.
Qed.

(* 熔合定位清零：熔合产物对任意 pid 探针失明（单向擦除的判定形态） *)
Lemma fuse_all_blind : forall (L : ledger) (p : nat),
  tid bool (probe_pid p (fuse_all L)) false.
Proof.
  intros L p. unfold probe_pid. destruct L as [locs ags].
  destruct locs as [| u t].
  - exact (@tid_refl bool false).
  - exact (@tid_refl bool false).
Qed.

Lemma fuse_ledger_blind : forall (L1 L2 : ledger) (p : nat),
  tid bool (probe_pid p (fuse_ledger L1 L2)) false.
Proof.
  intros L1 L2 p. unfold fuse_ledger, probe_pid.
  destruct L1 as [l1 a1]. destruct L2 as [l2 a2].
  destruct l1 as [| u t].
  - destruct l2 as [| u2 t2].
    + exact (@tid_refl bool false).
    + exact (@tid_refl bool false).
  - exact (@tid_refl bool false).
Qed.

(* ===================================================================== *)
(* 件 4. 不可逆碰撞见证（熔合后信息不保的构造性刻画）                            *)
(* ===================================================================== *)

(* 具体 pos 判词 *)
Lemma hw3 : tid bool (Z.ltb 0 3) true.
Proof. apply ltbT. lia. Qed.

Lemma hw4 : tid bool (Z.ltb 0 4) true.
Proof. apply ltbT. lia. Qed.

(* 前驱组 P：权重 (3,4)，生产者定位 7 与 9 *)
Definition uA1 : locu := mkLocu 3 hw3 7.
Definition uA2 : locu := mkLocu 4 hw4 9.

(* 前驱组 Q：权重 (3,4)，生产者定位 5 与 11 *)
Definition uB1 : locu := mkLocu 3 hw3 5.
Definition uB2 : locu := mkLocu 4 hw4 11.

Definition ledP : ledger := mkLed (uA1 :: uA2 :: nil) nil.
Definition ledQ : ledger := mkLed (uB1 :: uB2 :: nil) nil.

(* 见证 1（碰撞）：两组互异前驱熔合出同一聚合元——产物逐字段相等，
   pid 差异在产物中无字段可容身（定位擦除的构造性内容）。 *)
Lemma col_same_fused : tid agg (fuse2 uA1 uA2) (fuse2 uB1 uB2).
Proof.
  apply tid_refl.
Qed.

(* 见证 2（前驱可判定区分）：熔合前探针 7 在 P 在账、在 Q 不在账——
   两个前驱由一次 bool 判定即可分开。 *)
Lemma col_preds_distinguishable :
  tid bool (andb (probe_pid 7 ledP) (negb (probe_pid 7 ledQ))) true.
Proof.
  apply tid_refl.
Qed.

(* 见证 3（熔后失明）：两账本熔合产物对任意 pid 探针恒 false——
   熔合前可回答的判定问题（谁出的资）熔合后对一切 p 不可答。 *)
Lemma col_fused_blind : forall p : nat,
  tid bool (probe_pid p (fuse_ledger ledP ledQ)) false.
Proof.
  intros p. apply fuse_ledger_blind.
Qed.

(* 见证 4（碰撞档守恒）：熔合擦除定位但不动账——总量前后一致。 *)
Lemma col_total :
  tid Z (led_total (fuse_ledger ledP ledQ)) (led_total ledP + led_total ledQ).
Proof.
  unfold ledP, ledQ. cbn. apply tid_Z_of_eq. lia.
Qed.

(* 不可逆主定理（碰撞三联的打包陈述，零 Prop 载体）：
   若前驱可判定区分（andb 位为 true）则其熔合产物与对照产物 tid 相等——
   判定位在熔合中丢失。 *)
Record irrev_wit : Type := mkIrrev {
  iw_sep : bool ;
  iw_sep_tid : tid bool iw_sep true ;
  iw_left : locu ;
  iw_right : locu ;
  iw_fused : agg ;
  iw_hit : tid agg (fuse2 iw_left iw_right) iw_fused
}.

Definition irrev_collision : irrev_wit :=
  mkIrrev (andb (probe_pid 7 ledP) (negb (probe_pid 7 ledQ)))
          col_preds_distinguishable
          uA1 uA2 (fuse2 uA1 uA2)
          col_same_fused.

(* ===================================================================== *)
(* 件 5. 花：spend 即废（不可复制）                                           *)
(* ===================================================================== *)

(* 花掉头定位单元；无定位单元时花为恒等（诚实降档，不硬判） *)
Definition spend_led (L : ledger) : ledger :=
  match led_loc L with
  | nil => L
  | _ :: tl => mkLed tl (led_agg L)
  end.

(* 花取头：花后定位带 = 原带去头 *)
Lemma spend_loc_head : forall (u : locu) (tl : list locu) (ags : list agg),
  tid (list locu) (led_loc (spend_led (mkLed (u :: tl) ags))) tl.
Proof.
  intros u tl ags. exact (@tid_refl (list locu) tl).
Qed.

(* 花前在场：头单元的 pid 在账可探（bool true） *)
Lemma spend_head_present : forall (w : Z) (hw : tid bool (Z.ltb 0 w) true)
                                  (p : nat) (tl : list locu) (ags : list agg),
  tid bool (probe_pid p (mkLed (mkLocu w hw p :: tl) ags)) true.
Proof.
  intros w hw p tl ags. unfold probe_pid. cbn.
  rewrite Nat.eqb_refl. apply tid_refl.
Qed.

(* 花后即废：头单元 pid 花后消失（前提：tl 中本无该 pid） *)
Lemma spend_kills_pid : forall (w : Z) (hw : tid bool (Z.ltb 0 w) true) (p : nat)
                               (tl : list locu) (ags : list agg),
  tid bool (existsb (fun x : locu => Nat.eqb (lu_pid x) p) tl) false ->
  tid bool (probe_pid p (spend_led (mkLed (mkLocu w hw p :: tl) ags))) false.
Proof.
  intros w hw p tl ags H.
  apply (tid_trans bool (probe_pid p (spend_led (mkLed (mkLocu w hw p :: tl) ags)))
                       (existsb (fun x : locu => Nat.eqb (lu_pid x) p) tl) false).
  - exact (tid_cong (fun l : list locu => existsb (fun x : locu => Nat.eqb (lu_pid x) p) l)
                    _ _ (spend_loc_head (mkLocu w hw p) tl ags)).
  - exact H.
Qed.

(* 花的单调性：花一枚正权重单元后总量严格下降（nle 编码的构造见证） *)
Lemma spend_total_strict_drop : forall (w : Z) (hw : tid bool (Z.ltb 0 w) true)
                                       (p : nat) (tl : list locu) (ags : list agg),
  nle (S O) (Z.to_nat (led_total (mkLed (mkLocu w hw p :: tl) ags)
                         - led_total (spend_led (mkLed (mkLocu w hw p :: tl) ags)))).
Proof.
  intros w hw p tl ags.
  apply (zpos_to_nle (led_total (mkLed (mkLocu w hw p :: tl) ags)
                        - led_total (spend_led (mkLed (mkLocu w hw p :: tl) ags)))).
  pose proof (ltbF_inv w hw). unfold led_total. cbn. lia.
Qed.

(* 非空定位带的长度编码（nle 在场见证） *)
Lemma ledger_loc_len_pos : forall (u : locu) (tl : list locu) (ags : list agg),
  nle (S O) (length (led_loc (mkLed (u :: tl) ags))).
Proof.
  intros u tl ags. exact (nle_add_r (S O) (length tl)).
Qed.

(* ===================================================================== *)
(* 件 6. 多租户安全 + race-to-mint 赎回                                      *)
(* ===================================================================== *)

(* 单步出账：状态 + 是否发射 + 需求票增量 *)
Record step_out : Type := mkStep {
  so_led : ledger ;
  so_fired : bool ;
  so_dem : nat
}.

(* 定位带非空判定（bool 层） *)
Definition has_loc (L : ledger) : bool :=
  match led_loc L with
  | nil => false
  | _ => true
  end.

(* 发射一步：有定位单元则花头发射；无则不发射、原账保真、签发一张需求票
   （多租户安全定理：未 funded 的事件永不发射、转为需求流，机器继续运转） *)
Definition step_fire (L : ledger) : step_out :=
  match led_loc L with
  | nil => mkStep L false (S O)
  | _ :: tl => mkStep (mkLed tl (led_agg L)) true O
  end.

(* 安全定理：未 funded ⟹ 不发射 *)
Lemma unfunded_never_fires : forall L : ledger,
  tid bool (has_loc L) false -> tid bool (so_fired (step_fire L)) false.
Proof.
  intros [locs ags] H. destruct locs as [| u tl].
  - exact (@tid_refl bool false).
  - exact (tid_bool_tf_absurd _ H).
Qed.

(* 发射 ⟹ 曾 funded（判定对齐：两定义同带同支） *)
Lemma fired_only_funded : forall L : ledger,
  tid bool (so_fired (step_fire L)) true -> tid bool (has_loc L) true.
Proof.
  intros [locs ags] H. destruct locs as [| u tl].
  - exact H.
  - exact H.
Qed.

(* funded ⟹ 发射 *)
Lemma funded_fires : forall (u : locu) (tl : list locu) (ags : list agg),
  tid bool (so_fired (step_fire (mkLed (u :: tl) ags))) true.
Proof.
  intros u tl ags. exact (@tid_refl bool true).
Qed.

(* 未 funded 档：聚合带保真（机器其余事件继续运转） *)
Lemma unfunded_preserves : forall ags : list agg,
  tid (list agg) (led_agg (so_led (step_fire (mkLed nil ags)))) ags.
Proof.
  intros ags. exact (@tid_refl (list agg) ags).
Qed.

(* 未 funded 档：负向事件签发一张可再出资义务票（需求流 +1） *)
Lemma unfunded_emits_demand : forall ags : list agg,
  tid nat (so_dem (step_fire (mkLed nil ags))) (S O).
Proof.
  intros ags. exact (@tid_refl nat (S O)).
Qed.

(* 需求票：缺口定位单元数 + 票据代数——无地址字段（广播，不可指派） *)
Record demand : Type := mkDem {
  dem_short : nat ;
  dem_gen : nat
}.

(* race-to-mint 预算判定：正权重且不超自报预算（bool 判定） *)
Definition budget_ok (w budget : Z) : bool := andb (Z.ltb 0 w) (Z.leb w budget).

(* andb 左支提取 *)
Lemma andb_l_extract : forall b c : bool, tid bool (andb b c) true -> tid bool b true.
Proof.
  intros b c H. destruct b.
  - exact (@tid_refl bool true).
  - exact H.
Qed.

(* 后继不判等自身（票据焚毁引理） *)
Lemma eqb_S_neq : forall n : nat, tid bool (Nat.eqb (S n) n) false.
Proof.
  induction n as [| n IH].
  - exact (@tid_refl bool false).
  - exact IH.
Qed.

(* 赎回：任一生产者在自报预算内铸出新定位单元即销票——
   铸出的单元带新 pid（重定位），票据代数 +1（旧票作废），缺口 -1。 *)
Definition redeem (d : demand) (w budget : Z) (pid : nat)
           (Hok : tid bool (budget_ok w budget) true) : locu * demand :=
  (mkLocu w (andb_l_extract (Z.ltb 0 w) (Z.leb w budget) Hok) pid,
   mkDem (Nat.pred (dem_short d)) (S (dem_gen d))).

(* 赎回铸造的是真定位单元（pos 判词随身） *)
Lemma redeem_relocates : forall (d : demand) (w budget : Z) (pid : nat)
                                (Hok : tid bool (budget_ok w budget) true),
  tid bool (Z.ltb 0 (lu_w (fst (redeem d w budget pid Hok)))) true.
Proof.
  intros d w budget pid Hok. exact (andb_l_extract (Z.ltb 0 w) (Z.leb w budget) Hok).
Qed.

(* 赎回铸造的重定位：新单元 pid 即赎单生产者 *)
Lemma redeem_pid_fresh : forall (d : demand) (w budget : Z) (pid : nat)
                                (Hok : tid bool (budget_ok w budget) true),
  tid nat (lu_pid (fst (redeem d w budget pid Hok))) pid.
Proof.
  intros d w budget pid Hok. exact (@tid_refl nat pid).
Qed.

(* 单票单铸程：赎回后票据代数严格 +1，同票不可再赎（赎回活性判定形态） *)
Lemma redeem_burns_ticket : forall (d : demand) (w budget : Z) (pid : nat)
                                   (Hok : tid bool (budget_ok w budget) true),
  tid bool (Nat.eqb (dem_gen (snd (redeem d w budget pid Hok))) (dem_gen d)) false.
Proof.
  intros d w budget pid Hok. exact (eqb_S_neq (dem_gen d)).
Qed.

(* 赎回进度：缺口按 pred 递减 *)
Lemma redeem_progress : forall (d : demand) (w budget : Z) (pid : nat)
                               (Hok : tid bool (budget_ok w budget) true),
  tid nat (dem_short (snd (redeem d w budget pid Hok))) (Nat.pred (dem_short d)).
Proof.
  intros d w budget pid Hok. exact (@tid_refl nat (Nat.pred (dem_short d))).
Qed.

(* 赎回收口：单缺口票一次赎回即闭票 *)
Lemma redeem_closes_single : forall (w budget : Z) (pid : nat)
                                    (Hok : tid bool (budget_ok w budget) true)
                                    (g : nat),
  tid bool (Nat.eqb (dem_short (snd (redeem (mkDem (S O) g) w budget pid Hok))) O)
            true.
Proof.
  intros w budget pid Hok g. exact (@tid_refl bool true).
Qed.

(* 赎回在零缺口票上不产生负缺口（闭票保持闭票） *)
Lemma redeem_zero_stays : forall (w budget : Z) (pid : nat)
                                 (Hok : tid bool (budget_ok w budget) true)
                                 (g : nat),
  tid bool (Nat.eqb (dem_short (snd (redeem (mkDem O g) w budget pid Hok))) O) true.
Proof.
  intros w budget pid Hok g. exact (@tid_refl bool true).
Qed.
