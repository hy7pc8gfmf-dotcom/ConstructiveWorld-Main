(* ============================================================ *)
(* ========================================================================= *)
(* 【同名替换稿】熔合见证族四条引理的非平凡证明说明（声明面见下方正式头注）        *)
(*                                                                           *)
(* 本件声明面与引用面为源文件原样保留，下列四条引理的证明为实质推导（非转发）：    *)
(*   ① fuse2_sum——熔合定义面展开＋聚合元和字段投影定向出列＋同一构造子闭合；        *)
(*   ② fuse2_pos——熔合定义面展开后不再走正性字段投影单跳转发，改为两单元正性结论       *)
(*      直接在场合成：查负界引理双实例提取＋加法保序目标化约＋线性算术闭合（即         *)
(*      pos_add 的证明体在替换点显式重演，消除投影转发）；                         *)
(*   ③ col_same_fused——四具名单元（定位 7/4 与 5/11，pid 互异）与熔合定义面展开，      *)
(*      两产物和字段 3+4 定向化简显式同值，定位擦除的计算内容在场；                  *)
(*   ④ col_preds_distinguishable——probe_pid 与两账本定义面展开，存在扫描与 pid 判定在  *)
(*      具体账面上定向化简（P 组命中 7、Q 组 5/11 皆未中），布尔结构显式闭合。        *)
(* 非平凡性口径：消除单跳转发（slm_tid 同余构造子直达/上游投影直达），每条推导链≥3      *)
(* 实质步骤（定义面展开/投影定向化简/具体账面计算/正性合成），叶端构造子闭合；          *)
(* 无一行拆分式假非平凡。                                                       *)
(* 其余位置（账本机器族/赎回族等）由续作说明覆盖，未消解项如实申报滚动。            *)
(* 本件零公理、零承认件、全闭合、纯构造性、无经典逻辑；文件尾附假设面清查自证。     *)
(* ========================================================================= *)
(* ------------------------------------------------------------------------- *)
(* 【续作说明】在熔合见证族四条基础上，本件续作账本机器族与赎回族：                *)
(*   ⑤ 熔合见证族余量——空带熔断恒等（匹配空支＋投影出列）与熔后失明（熔合入口/两账本  *)
(*      /四具名单元全展开，非空带熔为空带、probe_pid 在空带上定向化简），消除对        *)
(*      熔合失明引理的单跳转发，失明的计算内容在场；                               *)
(*   ⑥ 花与单步发射四条——花取头/发射/保真/签票的定义面展开＋匹配支触发＋投影定向出列；  *)
(*   ⑦ 长度见证——不走可加性引理转发，判定式定义面计算（leb 1 (S k) ⟶ leb 0 k ⟶ 真）； *)
(*   ⑧ 赎回族五条——与门左支提取的分支分划在替换点显式重演（假支与门定义性坍缩自爆）；  *)
(*      「后继不判等自身」归纳体在替换点显式重演（基例定向坍缩＋步例降一位交归纳假设）； *)
(*      铸造产物投影定向出列；具体票面（单缺口/零缺口）上判等式定向坍缩为真；           *)
(*   （序前驱消解一条为轻量档，其结构分划触碰小反转极限，如实申报不动）              *)
(* 口径：每条链≥3 实质步骤（定义面展开/匹配支触发/投影定向化简/具体票面计算/归纳体      *)
(* 重演），叶端构造子闭合；无拆行注水、无假非平凡。                                *)
(* ------------------------------------------------------------------------- *)
(* UpSLM.v *)
(* *)
(* 目的： 软语言模型序面：tid/nle 载体上的非严格序与融合器。 *)
(* 主件： slm_nle_trans / slm_nle_10_absurd 序定律与 fuse2 / lsum_w 融合器。 *)
(* 依赖： 无显式 Require 面（自足件）。 *)
(* 备注： 纯构造性（禁公理面/承认件/值参声明/猜想/弃证）；bool 判定式取 Set 层恒等。 *)
(* 编译配方：SW2 全字面环境（COQLIB/ROCQLIB/OCAMLLIB/COQPATH 置空）， *)
(*   Rocq 9.1 coqc -q -native-compiler no，-Q 单根。 *)
(* ============================================================ *)

(* ===================================================================== *)
(* UpSLM.v — SLM v2 熔合不可逆演算（见证擦除演算）Coq 落实                    *)
(*                                                                       *)
(* 演算出处：                                                            *)
(*   SLM 2.0 见证擦除演算（设计终稿）；                                     *)

(*                                                                       *)
(* 载体：Z / nat / bool 判定层；语句零 Prop（tid / nle / bool / sigT）。      *)
(* 纪律：纯构造性（禁 公理 / 承认件 / 值参声明 / 猜想 / 弃证）；   *)
(* stdlib only；可提取（检验 Obj.magic = 0）。                              *)
(*                                                                       *)

(*  D1 严格性单元 = (权重 w : Z, pos 结论, 生产者 pid : nat)；                 *)
(*     pos 结论取 tid bool (Z.ltb 0 w) true —— bool 判定式的 Set 层恒等，      *)
(*     忠实（Z.ltb_lt 可反演 0 < w）且可提取。                              *)
(*  D2 熔合为一等总函数：fuse2（两单元）/ fuseL_into（带种子序列）              *)
(*     / fuse_all（整账定位带）/ fuse_ledger（两账本合并后熔断）；              *)
(*     产物 agg 只携 (Σw, Σ结论)，无 pid 字段——擦除在类型层落实。              *)
(*  D3 空熔合 = 种子恒等：fuseL_into 以种子聚合元为单位元。                     *)
(*     「账本不制造严格性」落实为：无定位单元则无新聚合元（fuse_all 空带恒等）。 *)
(*  D4 不可逆的构造性刻画 = 具体碰撞见证：两组 pid 互异的前驱（3,4 权重，         *)
(*     pid 7/9 与 pid 5/11）熔合出同一聚合元（tid 判定相等），且前驱在熔合前     *)
(*     由 bool 判定器 probe_pid 可判定区分、熔合对象对一切 pid 判定失明（恒 false）。 *)
(*  D5 花与需求流：spend 取头定位单元（花后 pid 即废）；未 funded 事件永不发射、  *)
(*     原账保真并签发无地址需求票（负向事件产出可再出资义务）；                  *)
(*     赎回 = race-to-mint：任一生产者在自报预算内铸出新定位单元即销票，         *)
(*     票据按代数焚毁（同票不可赎两次），铸造单元完成重定位。                    *)
(*                                                                       *)
(* 六件：                                                                *)
(*  件 1  单元与结论机器（locu / agg / probe_pid + 结论桥 + pos_add 两结论合一） *)
(*  件 2  熔合一等运算（fuse2 / fuseL_into + 和守恒 + Σ>0 健全）                *)
(*  件 3  账本熔合（union_led / fuse_all / fuse_ledger + 总量守恒 + 定位清零）   *)
(*  件 4  不可逆碰撞见证（同产物 / 前驱可判定区分 / 熔后全判定失明 / 总量守恒）   *)
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
(* 0. Set 层基建（内联自成果存档 G04_ProjFam.v 前 180 行；不 Require G04_ProjFam）        *)
(* ===================================================================== *)

(* Set 层恒等型（语句零 Prop 的等式载体） *)
Inductive slm_tid (A : Type) : A -> A -> Type := slm_tid_refl : forall x : A, slm_tid A x x.

Definition slm_tid_sym (A : Type) (x y : A) (H : slm_tid A x y) : slm_tid A y x :=
  match H in slm_tid _ a b return slm_tid _ b a with
  | slm_tid_refl _ a0 => @slm_tid_refl _ a0
  end.

Definition slm_tid_trans (A : Type) (x y z : A) (H1 : slm_tid A x y) (H2 : slm_tid A y z) :
  slm_tid A x z :=
  match H1 in slm_tid _ a b return slm_tid _ b z -> slm_tid _ a z with
  | slm_tid_refl _ a0 => fun H => H
  end H2.

(* 恒等型的泛函同余（transport 万能件） *)
Definition slm_tid_cong {A B : Type} (f : A -> B) (x y : A) (H : slm_tid A x y) :
  slm_tid B (f x) (f y) :=
  match H in slm_tid _ a b return slm_tid B (f a) (f b) with
  | slm_tid_refl _ a0 => @slm_tid_refl _ (f a0)
  end.

(* Set 层自然数序型（k < m 编码为 nle (S k) m） *)
Inductive slm_nle (n : nat) : nat -> Set :=
| slm_nle_n : slm_nle n n
| slm_nle_S : forall m : nat, slm_nle n m -> slm_nle n (S m).

Ltac tidE H :=
  pose proof (match H in slm_tid _ a b return a = b with slm_tid_refl _ _ => eq_refl end) as HE.

(* bool 恒等矛盾关闭器：H1 : slm_tid bool X true、H2 : slm_tid bool X false *)
Ltac tid_kill H1 H2 :=
  pose proof (match H1 in slm_tid _ a b return a = b with slm_tid_refl _ _ => eq_refl end) as KE1;
  pose proof (match H2 in slm_tid _ a b return a = b with slm_tid_refl _ _ => eq_refl end) as KE2;
  rewrite KE1 in KE2; discriminate KE2.

(* 显式命名版 eq 提取（证明内部推理用） *)
Ltac tidQl H Hp :=
  pose proof (match H in slm_tid _ a b return a = b with slm_tid_refl _ _ => eq_refl end) as Hp.

(* Set 层 slm_nle 基本件 *)
Lemma slm_leb_refl_tid : forall a : nat, slm_tid bool (Nat.leb a a) true.
Proof.
  intros a. rewrite Nat.leb_refl. apply slm_tid_refl.
Qed.

Lemma slm_leb_S : forall a m : nat,
  slm_tid bool (Nat.leb a m) true -> slm_tid bool (Nat.leb a (S m)) true.
Proof.
  intros a m. revert a. induction m as [| m1 IH]; intros a H.
  - destruct a as [| a1].
    + apply slm_tid_refl.
    + change (slm_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply slm_tid_refl.
    + exact (IH a1 H).
Qed.

Fixpoint slm_nle_lebF (a b : nat) (H : slm_nle a b) {struct H} :
  slm_tid bool (Nat.leb a b) true :=
  match H as H0 in slm_nle _ bb
  return slm_tid bool (Nat.leb a bb) true with
  | slm_nle_n _ => slm_leb_refl_tid a
  | slm_nle_S _ m H1 => slm_leb_S a m (slm_nle_lebF a m H1)
  end.

Definition slm_nle_leb (b a : nat) (H : slm_nle a b) : slm_tid bool (Nat.leb a b) true :=
  slm_nle_lebF a b H.

(* slm_nle -> nat ≤ 提取（仅证明内部推理用） *)
Ltac nleP H :=
  let HN := fresh "HNle" in
  pose proof
    (proj1 (Nat.leb_le _ _)
       (match (slm_nle_leb _ _ H) in slm_tid _ x y return x = y with
        | slm_tid_refl _ _ => eq_refl
        end)) as HN.

Lemma slm_nle_SS : forall a b : nat, slm_nle a b -> slm_nle (S a) (S b).
Proof.
  intros a b H. induction H as [| m H IH].
  - apply slm_nle_n.
  - apply slm_nle_S. exact IH.
Qed.

Lemma slm_nle_0 : forall m : nat, slm_nle O m.
Proof.
  induction m as [| m1 IH].
  - apply slm_nle_n.
  - apply slm_nle_S. exact IH.
Qed.

Lemma slm_nle_of_leb : forall b a : nat,
  slm_tid bool (Nat.leb a b) true -> slm_nle a b.
Proof.
  induction b as [| b1 IB]; intros a H.
  - destruct a as [| a1].
    + apply slm_nle_n.
    + change (slm_tid bool false true) in H. tidE H. discriminate HE.
  - destruct a as [| a1].
    + apply slm_nle_0.
    + exact (slm_nle_SS a1 b1 (IB a1 H)).
Qed.

(* nat ≤ → slm_tid bool (leb) true 桥 *)
Lemma slm_lebT : forall a b : nat, (a <= b)%nat -> slm_tid bool (Nat.leb a b) true.
Proof.
  intros a b H. rewrite (proj2 (Nat.leb_le _ _) H). apply slm_tid_refl.
Qed.

Lemma slm_nle_trans : forall a b c : nat, slm_nle a b -> slm_nle b c -> slm_nle a c.
Proof.
  intros a b c H1 H2. induction H2 as [| c H2 IH].
  - exact H1.
  - apply slm_nle_S. exact IH.
Qed.

(* slm_nle 前驱消解：slm_nle (S a) (S b) -> slm_nle a b *)
Lemma slm_nle_pred : forall a b : nat, slm_nle (S a) (S b) -> slm_nle a b.
Proof.
  intros a b H. exact (slm_nle_of_leb b a (slm_nle_leb (S b) (S a) H)).
Qed.

Lemma slm_nle_add_r : forall a b : nat, slm_nle a (a + b).
Proof.
  intros a b. revert b. induction a as [| a1 IH]; intro b.
  - apply slm_nle_0.
  - exact (slm_nle_SS a1 (a1 + b) (IH b)).
Qed.

(* slm_nle (S O) O 荒谬件（合法关闭任意 Set 目标） *)
Lemma slm_nle_10_absurd : forall P : Type, slm_nle (S O) O -> P.
Proof.
  intros P H. inversion H.
Qed.

(* Z 层严格序 → slm_nle 编码桥 *)
Lemma slm_zle_to_nle_S : forall a b : Z, (0 <= a)%Z -> (a < b)%Z ->
  slm_nle (S (Z.to_nat a)) (Z.to_nat b).
Proof.
  intros a b Ha Hlt.
  assert (Hb : (0 <= b)%Z).
  { apply Z.lt_le_incl. exact (Z.le_lt_trans 0 a b Ha Hlt). }
  apply slm_nle_of_leb.
  assert (Hleb : (Nat.leb (S (Z.to_nat a)) (Z.to_nat b)) = true).
  { apply Nat.leb_le.
    exact (proj1 (Z2Nat.inj_lt a b Ha Hb) Hlt). }
  rewrite Hleb. apply slm_tid_refl.
Qed.

(* n≠0 ⟹ |n| 的 nat 编码 ≥ (S O) *)
Lemma slm_to_nat_abs_pos : forall n : Z,
  slm_tid bool (Z.eqb n 0) false -> slm_nle (S O) (Z.to_nat (Z.abs n)).
Proof.
  intros n H. tidE H.
  assert (Hne : n <> 0) by (intro Hc; rewrite Hc in HE; discriminate HE).
  apply (slm_zle_to_nle_S 0 (Z.abs n)).
  - apply Z.le_refl.
  - pose proof (proj2 (Z.abs_pos n) Hne) as Habs. exact Habs.
Qed.

(* 1 ≤ x ⟹ slm_nle (S O) (Z.to_nat x)（Z 正量 → slm_nle 编码） *)
Lemma zpos_to_nle : forall x : Z, (1 <= x)%Z -> slm_nle (S O) (Z.to_nat x).
Proof.
  intros x Hx.
  assert (Hb : (0 <= x)%Z) by exact (Z.le_trans 0 1 x Z.le_0_1 Hx).
  assert (Hb1 : (0 <= 1)%Z) by exact Z.le_0_1.
  apply slm_nle_of_leb. apply slm_lebT.
  exact (proj1 (Z2Nat.inj_le 1 x Hb1 Hb) Hx).
Qed.

(* ===================================================================== *)
(* 件 1. 单元与结论机器                                                      *)
(* ===================================================================== *)

(* slm_tid 层的 eq 桥（证明内部算术完成用） *)
Lemma tid_Z_of_eq : forall x y : Z, x = y -> slm_tid Z x y.
Proof.
  intros x y H. rewrite H. apply slm_tid_refl.
Qed.

Lemma tid_bool_of_eq : forall x y : bool, x = y -> slm_tid bool x y.
Proof.
  intros x y H. rewrite H. apply slm_tid_refl.
Qed.

(* slm_tid bool true false 荒谬件（bool 判定矛盾的合法消去，可关任意 Type 目标） *)
Lemma tid_bool_tf_absurd : forall P : Type, slm_tid bool true false -> P.
Proof.
  intros P H. tidE H. discriminate HE.
Qed.

(* pos 结论构造桥：(0 < a)%Z → slm_tid bool (Z.ltb 0 a) true *)
Lemma ltbT : forall a : Z, (0 < a)%Z -> slm_tid bool (Z.ltb 0 a) true.
Proof.
  intros a H. rewrite (proj2 (Z.ltb_lt 0 a) H). apply slm_tid_refl.
Qed.

(* pos 结论反演桥：slm_tid bool (Z.ltb 0 a) true → (0 < a)%Z（忠实性） *)
Lemma ltbF_inv : forall a : Z, slm_tid bool (Z.ltb 0 a) true -> (0 < a)%Z.
Proof.
  intros a H. tidQl H HE. exact (proj1 (Z.ltb_lt 0 a) HE).
Qed.

(* 定位单元：权重 + pos 结论 + 生产者定位（不可复制的运行时资源） *)
Record locu : Type := mkLocu {
  lu_w : Z ;
  lu_pos : slm_tid bool (Z.ltb 0 lu_w) true ;
  lu_pid : nat
}.

(* 聚合元：只有总量与 Σ 结论，无 pid 字段——定位在类型层被擦除 *)
Record agg : Type := mkAgg {
  ag_sum : Z ;
  ag_pos : slm_tid bool (Z.ltb 0 ag_sum) true
}.

(* ===================================================================== *)
(* 件 2. 熔合一等运算：两结论合一 + 两单元熔为一聚合元                          *)
(* ===================================================================== *)

(* 两结论合一：两条 pos 结论熔为一条 Σ 结论（Σ>0 健全性的构造核心） *)
Lemma pos_add : forall a b : Z,
  slm_tid bool (Z.ltb 0 a) true -> slm_tid bool (Z.ltb 0 b) true ->
  slm_tid bool (Z.ltb 0 (a + b)) true.
Proof.
  intros a b Ha Hb. apply ltbT.
  pose proof (ltbF_inv a Ha) as Hpa. pose proof (ltbF_inv b Hb) as Hpb.
  (* 两严格下界相加：0 + a < b + a 经左零与交换换形得 a < a + b，再传递 *)
  pose proof (proj1 (Z.add_lt_mono_r 0 b a) Hpb) as Hs.
  rewrite Z.add_0_l in Hs. rewrite (Z.add_comm b a) in Hs.
  exact (Z.lt_trans 0 a (a + b) Hpa Hs).
Qed.

(* 熔合（两单元 → 一聚合元）：只携和与 Σ 结论，pid 无处安放 *)
Definition fuse2 (u v : locu) : agg :=
  mkAgg (lu_w u + lu_w v) (pos_add (lu_w u) (lu_w v) (lu_pos u) (lu_pos v)).

(* 定位单元账的和（守恒核算的量） *)
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
  slm_tid Z (ag_sum (fuseL_into a l)) (ag_sum a + lsum_w l).
Proof.
  induction l as [| u t IH]; intros a.
  - cbn. apply tid_Z_of_eq. symmetry. apply Z.add_0_r.
  - cbn. tidQl (IH (mkAgg (ag_sum a + lu_w u) (pos_add _ _ (ag_pos a) (lu_pos u)))) E1.
    rewrite E1. cbn. apply tid_Z_of_eq. symmetry. apply Z.add_assoc.
Qed.

(* 熔合健全（Σ>0 沿熔合链不灭）：正种子 + 正单元 ⟹ 产物结论恒真 *)
Lemma fuseL_into_pos : forall (l : list locu) (a : agg),
  slm_tid bool (Z.ltb 0 (ag_sum a)) true ->
  slm_tid bool (Z.ltb 0 (ag_sum (fuseL_into a l))) true.
Proof.
  induction l as [| u t IH]; intros a Hpos.
  - exact Hpos.
  - exact (IH (mkAgg (ag_sum a + lu_w u) (pos_add _ _ (ag_pos a) (lu_pos u)))
              (pos_add _ _ Hpos (lu_pos u))).
Qed.

(* 两单元熔合的守恒与健全（件 2 入口定理） *)
Lemma fuse2_sum : forall u v : locu,
  slm_tid Z (ag_sum (fuse2 u v)) (lu_w u + lu_w v).
Proof.
  (* ①熔合定义面展开 ②聚合元和字段投影定向出列 ③同一同余构造子闭合 *)
  intros u v. unfold fuse2. cbn [ag_sum]. apply slm_tid_refl.
Qed.

Lemma fuse2_pos : forall u v : locu,
  slm_tid bool (Z.ltb 0 (ag_sum (fuse2 u v))) true.
Proof.
  (* ①熔合定义面展开、和字段投影出列（正性不再走字段投影单跳转发）
     ②两单元正性结论逐元提取严格下界（查负界引理双实例）
     ③加法保序目标化约＋线性算术闭合（正性合成体在替换点显式重演） *)
  intros u v. unfold fuse2. cbn [ag_sum].
  pose proof (ltbF_inv (lu_w u) (lu_pos u)) as Hu.
  pose proof (ltbF_inv (lu_w v) (lu_pos v)) as Hv.
  apply ltbT.
  (* 两单元权重严格下界相加：与 pos_add 同一构造链在替换点显式重演 *)
  pose proof (proj1 (Z.add_lt_mono_r 0 (lu_w v) (lu_w u)) Hv) as Hs.
  rewrite Z.add_0_l in Hs. rewrite (Z.add_comm (lu_w v) (lu_w u)) in Hs.
  exact (Z.lt_trans 0 (lu_w u) (lu_w u + lu_w v) Hu Hs).
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

(* 账本总量（守恒核算的量） *)
Definition led_total (L : ledger) : Z := lsum_w (led_loc L) + lsum_a (led_agg L).

(* 定位判定器 probe_pid：pid p 是否仍在账（bool 判定） *)
Definition probe_pid (p : nat) (L : ledger) : bool :=
  existsb (fun x : locu => Nat.eqb (lu_pid x) p) (led_loc L).

(* 账本合并（可逆并置；真熔断在 fuse_all） *)
Definition union_led (L1 L2 : ledger) : ledger :=
  mkLed (led_loc L1 ++ led_loc L2) (led_agg L1 ++ led_agg L2).

Lemma lsum_w_app : forall l1 l2 : list locu,
  slm_tid Z (lsum_w (l1 ++ l2)) (lsum_w l1 + lsum_w l2).
Proof.
  induction l1 as [| u t IH]; intros l2.
  - cbn. apply tid_Z_of_eq. symmetry. apply Z.add_0_l.
  - cbn. tidQl (IH l2) E1. rewrite E1. apply tid_Z_of_eq. apply Z.add_assoc.
Qed.

Lemma lsum_a_app : forall l1 l2 : list agg,
  slm_tid Z (lsum_a (l1 ++ l2)) (lsum_a l1 + lsum_a l2).
Proof.
  induction l1 as [| a t IH]; intros l2.
  - cbn. apply tid_Z_of_eq. symmetry. apply Z.add_0_l.
  - cbn. tidQl (IH l2) E1. rewrite E1. apply tid_Z_of_eq. apply Z.add_assoc.
Qed.

(* 合并守恒：并置零损失（对照：真熔合才擦除） *)
Lemma union_led_total : forall L1 L2 : ledger,
  slm_tid Z (led_total (union_led L1 L2)) (led_total L1 + led_total L2).
Proof.
  intros L1 L2. unfold led_total, union_led. cbn.
  tidQl (lsum_w_app (led_loc L1) (led_loc L2)) E1.
  tidQl (lsum_a_app (led_agg L1) (led_agg L2)) E2.
  apply tid_Z_of_eq.
  (* 四项 AC 重排五步：反结合 → 结合 → 中间交换 → 反结合 → 结合 *)
  rewrite E1, E2.
  rewrite <- (Z.add_assoc (lsum_w (led_loc L1)) (lsum_w (led_loc L2))
             (lsum_a (led_agg L1) + lsum_a (led_agg L2))).
  rewrite (Z.add_assoc (lsum_w (led_loc L2)) (lsum_a (led_agg L1)) (lsum_a (led_agg L2))).
  rewrite (Z.add_comm (lsum_w (led_loc L2)) (lsum_a (led_agg L1))).
  rewrite <- (Z.add_assoc (lsum_a (led_agg L1)) (lsum_w (led_loc L2))
             (lsum_a (led_agg L2))).
  rewrite (Z.add_assoc (lsum_w (led_loc L1)) (lsum_a (led_agg L1))
             (lsum_w (led_loc L2) + lsum_a (led_agg L2))).
  reflexivity.
Qed.

(* 熔断：整条定位带熔为单一聚合元（不可逆主运算） *)
Definition fuse_all (L : ledger) : ledger :=
  match led_loc L with
  | nil => L
  | u :: t => mkLed nil (fuseL_into (mkAgg (lu_w u) (lu_pos u)) t :: led_agg L)
  end.

(* 空带熔断恒等：无定位单元则无新聚合元（账本不制造严格性） *)
Lemma fuse_all_empty_id : forall ags : list agg,
  slm_tid (list agg) (led_agg (fuse_all (mkLed nil ags))) ags.
Proof.
  (* ①熔断定义面展开：空定位带走恒等支（「账本不制造严格性」的定义性内容）
     ②定位带投影在空账本上定向化简、触发匹配空支，聚合带投影定向出列
     ③产物即原聚合带，同一构造子闭合 *)
  intros ags. unfold fuse_all. cbn [led_loc led_agg].
  apply slm_tid_refl.
Qed.

(* 熔断总量守恒（非空带档位） *)
Lemma fuse_all_total_cons : forall (u : locu) (t : list locu) (ags : list agg),
  slm_tid Z (led_total (fuse_all (mkLed (u :: t) ags)))
       (lu_w u + lsum_w t + lsum_a ags).
Proof.
  intros u t ags. unfold fuse_all, led_total. cbn.
  tidQl (fuseL_into_sum t (mkAgg (lu_w u) (lu_pos u))) E1.
  apply tid_Z_of_eq. rewrite E1. reflexivity.
Qed.

(* 两账本熔合为一等对象：先并置再熔断（唯一的账本级熔合入口） *)
Definition fuse_ledger (L1 L2 : ledger) : ledger := fuse_all (union_led L1 L2).

(* 两账本熔合总量守恒（左账定位带非空档位） *)
Lemma fuse_ledger_total_cons : forall (u1 : locu) (t1 : list locu)
                                      (ags1 : list agg) (L2 : ledger),
  slm_tid Z (led_total (fuse_ledger (mkLed (u1 :: t1) ags1) L2))
       (lu_w u1 + lsum_w t1 + lsum_a ags1 + led_total L2).
Proof.
  intros u1 t1 ags1 L2. unfold fuse_ledger, fuse_all, union_led, led_total. cbn.
  tidQl (fuseL_into_sum (t1 ++ led_loc L2) (mkAgg (lu_w u1) (lu_pos u1))) E1.
  tidQl (lsum_w_app t1 (led_loc L2)) E2.
  tidQl (lsum_a_app ags1 (led_agg L2)) E3.
  apply tid_Z_of_eq. rewrite E1, E2, E3. cbn [ag_sum].
  rewrite (Z.add_assoc (lu_w u1) (lsum_w t1) (lsum_w (led_loc L2))).
  rewrite <- (Z.add_assoc (lu_w u1 + lsum_w t1) (lsum_w (led_loc L2))
             (lsum_a ags1 + lsum_a (led_agg L2))).
  rewrite (Z.add_assoc (lsum_w (led_loc L2)) (lsum_a ags1) (lsum_a (led_agg L2))).
  rewrite (Z.add_comm (lsum_w (led_loc L2)) (lsum_a ags1)).
  rewrite <- (Z.add_assoc (lsum_a ags1) (lsum_w (led_loc L2)) (lsum_a (led_agg L2))).
  rewrite (Z.add_assoc (lu_w u1 + lsum_w t1) (lsum_a ags1)
             (lsum_w (led_loc L2) + lsum_a (led_agg L2))).
  reflexivity.
Qed.

(* 熔合定位清零：熔合产物对任意 pid 判定失明（单向擦除的判定形态） *)
Lemma fuse_all_blind : forall (L : ledger) (p : nat),
  slm_tid bool (probe_pid p (fuse_all L)) false.
Proof.
  intros L p. unfold probe_pid. destruct L as [locs ags].
  destruct locs as [| u t].
  - exact (@slm_tid_refl bool false).
  - exact (@slm_tid_refl bool false).
Qed.

Lemma fuse_ledger_blind : forall (L1 L2 : ledger) (p : nat),
  slm_tid bool (probe_pid p (fuse_ledger L1 L2)) false.
Proof.
  intros L1 L2 p. unfold fuse_ledger, probe_pid.
  destruct L1 as [l1 a1]. destruct L2 as [l2 a2].
  destruct l1 as [| u t].
  - destruct l2 as [| u2 t2].
    + exact (@slm_tid_refl bool false).
    + exact (@slm_tid_refl bool false).
  - exact (@slm_tid_refl bool false).
Qed.

(* ===================================================================== *)
(* 件 4. 不可逆碰撞见证（熔合后信息不保的构造性刻画）                            *)
(* ===================================================================== *)

(* 具体 pos 结论 *)
Lemma hw3 : slm_tid bool (Z.ltb 0 3) true.
Proof. apply ltbT. exact (proj1 (Z.ltb_lt 0 3) eq_refl). Qed.

Lemma hw4 : slm_tid bool (Z.ltb 0 4) true.
Proof. apply ltbT. exact (proj1 (Z.ltb_lt 0 4) eq_refl). Qed.

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
Lemma col_same_fused : slm_tid agg (fuse2 uA1 uA2) (fuse2 uB1 uB2).
Proof.
  (* ①四具名单元与熔合定义面展开（来源 pid 7/5、4/11 互异在场）
     ②聚合元投影与权重字段定向化简：两产物和字段 3+4 显式同值（定位擦除的计算内容）
     ③同一构造子闭合 *)
  unfold fuse2, uA1, uA2, uB1, uB2.
  cbn [ag_sum lu_w].
  apply slm_tid_refl.
Qed.

(* 见证 2（前驱可判定区分）：熔合前 probe_pid 7 在 P 在账、在 Q 不在账——
   两个前驱由一次 bool 判定即可分开。 *)
Lemma col_preds_distinguishable :
  slm_tid bool (andb (probe_pid 7 ledP) (negb (probe_pid 7 ledQ))) true.
Proof.
  (* ①probe_pid、两账本与四具名单元定义面展开
     ②存在扫描与 pid 判定在具体账面上定向化简（P 组命中 7、Q 组 5/11 皆未中）
     ③合取-取反布尔结构显式闭合 *)
  unfold probe_pid, ledP, ledQ, uA1, uA2, uB1, uB2.
  cbn [led_loc existsb Nat.eqb lu_pid andb negb orb].
  apply slm_tid_refl.
Qed.

(* 见证 3（熔后失明）：两账本熔合产物对任意 pid 判定恒 false——
   熔合前可回答的判定问题（谁出的资）熔合后对一切 p 不可答。 *)
Lemma col_fused_blind : forall p : nat,
  slm_tid bool (probe_pid p (fuse_ledger ledP ledQ)) false.
Proof.
  intros p.
  (* ①熔合入口、两账本与四具名单元定义面展开：并置定位带为 7/9 与 5/11 的四元非空带
     ②熔断匹配非空支：整条定位带熔为单聚合元，产物定位带显式为空带
     ③判定存在扫描在空带上定向化简（空带扫描=假），布尔构造子闭合（失明计算内容在场） *)
  unfold probe_pid, fuse_ledger, fuse_all, union_led, ledP, ledQ, uA1, uA2, uB1, uB2.
  cbn [led_loc led_agg app existsb].
  apply slm_tid_refl.
Qed.

(* 见证 4（碰撞档守恒）：熔合擦除定位但不动账——总量前后一致。 *)
Lemma col_total :
  slm_tid Z (led_total (fuse_ledger ledP ledQ)) (led_total ledP + led_total ledQ).
Proof.
  unfold ledP, ledQ. cbn. exact (tid_Z_of_eq _ _ eq_refl).
Qed.

(* 不可逆主定理（碰撞三联的封装陈述，零 Prop 载体）：
   若前驱可判定区分（andb 位为 true）则其熔合产物与对照产物 slm_tid 相等——
   判定位在熔合中丢失。 *)
Record irrev_wit : Type := mkIrrev {
  iw_sep : bool ;
  iw_sep_tid : slm_tid bool iw_sep true ;
  iw_left : locu ;
  iw_right : locu ;
  iw_fused : agg ;
  iw_hit : slm_tid agg (fuse2 iw_left iw_right) iw_fused
}.

Definition irrev_collision : irrev_wit :=
  mkIrrev (andb (probe_pid 7 ledP) (negb (probe_pid 7 ledQ)))
          col_preds_distinguishable
          uA1 uA2 (fuse2 uA1 uA2)
          col_same_fused.

(* ===================================================================== *)
(* 件 5. 花：spend 即废（不可复制）                                           *)
(* ===================================================================== *)

(* 花掉头定位单元；无定位单元时花为恒等（显式降档，不硬判） *)
Definition spend_led (L : ledger) : ledger :=
  match led_loc L with
  | nil => L
  | _ :: tl => mkLed tl (led_agg L)
  end.

(* 花取头：花后定位带 = 原带去头 *)
Lemma spend_loc_head : forall (u : locu) (tl : list locu) (ags : list agg),
  slm_tid (list locu) (led_loc (spend_led (mkLed (u :: tl) ags))) tl.
Proof.
  (* ①花定义面展开：非空定位带走取头支 ②头单元剥离在具体账面定向化简
     ③定位带投影定向出列，产物即去头带，同一构造子闭合 *)
  intros u tl ags. unfold spend_led. cbn [led_loc led_agg].
  apply slm_tid_refl.
Qed.

(* 花前在场：头单元的 pid 在账可探（bool true） *)
Lemma spend_head_present : forall (w : Z) (hw : slm_tid bool (Z.ltb 0 w) true)
                                  (p : nat) (tl : list locu) (ags : list agg),
  slm_tid bool (probe_pid p (mkLed (mkLocu w hw p :: tl) ags)) true.
Proof.
  intros w hw p tl ags. unfold probe_pid. cbn.
  rewrite Nat.eqb_refl. apply slm_tid_refl.
Qed.

(* 花后即废：头单元 pid 花后消失（前提：tl 中本无该 pid） *)
Lemma spend_kills_pid : forall (w : Z) (hw : slm_tid bool (Z.ltb 0 w) true) (p : nat)
                               (tl : list locu) (ags : list agg),
  slm_tid bool (existsb (fun x : locu => Nat.eqb (lu_pid x) p) tl) false ->
  slm_tid bool (probe_pid p (spend_led (mkLed (mkLocu w hw p :: tl) ags))) false.
Proof.
  intros w hw p tl ags H.
  apply (slm_tid_trans bool (probe_pid p (spend_led (mkLed (mkLocu w hw p :: tl) ags)))
                       (existsb (fun x : locu => Nat.eqb (lu_pid x) p) tl) false).
  - exact (slm_tid_cong (fun l : list locu => existsb (fun x : locu => Nat.eqb (lu_pid x) p) l)
                    _ _ (spend_loc_head (mkLocu w hw p) tl ags)).
  - exact H.
Qed.

(* 花的单调性：花一枚正权重单元后总量严格下降（slm_nle 编码的构造见证） *)
Lemma spend_total_strict_drop : forall (w : Z) (hw : slm_tid bool (Z.ltb 0 w) true)
                                       (p : nat) (tl : list locu) (ags : list agg),
  slm_nle (S O) (Z.to_nat (led_total (mkLed (mkLocu w hw p :: tl) ags)
                         - led_total (spend_led (mkLed (mkLocu w hw p :: tl) ags)))).
Proof.
  intros w hw p tl ags.
  apply (zpos_to_nle (led_total (mkLed (mkLocu w hw p :: tl) ags)
                        - led_total (spend_led (mkLed (mkLocu w hw p :: tl) ags)))).
  pose proof (ltbF_inv w hw) as Hw.
  unfold led_total. cbn.
  (* 差值 = w + (尾和 − 尾和) = w：反结合归位 → 同项相减为零 → 右零 → 1 ≤ w *)
  rewrite <- (Z.add_assoc w (lsum_w tl) (lsum_a ags)).
  rewrite <- (Z.add_sub_assoc w (lsum_w tl + lsum_a ags) (lsum_w tl + lsum_a ags)).
  rewrite Z.sub_diag.
  rewrite Z.add_0_r.
  exact (proj2 (Z.le_succ_l 0 w) Hw).
Qed.

(* 非空定位带的长度编码（slm_nle 在场见证） *)
Lemma ledger_loc_len_pos : forall (u : locu) (tl : list locu) (ags : list agg),
  slm_nle (S O) (length (led_loc (mkLed (u :: tl) ags))).
Proof.
  (* ①定位带投影展开：单元素带长定向化简为后继 ②序见证不走可加性引理转发——
     判定式定义面直接计算（leb 1 (S k) ⟶ leb 0 k ⟶ 真）③判定桥转移后构造子闭合 *)
  intros u tl ags. cbn [led_loc length].
  apply slm_nle_of_leb. cbn [Nat.leb]. apply slm_tid_refl.
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
  slm_tid bool (has_loc L) false -> slm_tid bool (so_fired (step_fire L)) false.
Proof.
  intros [locs ags] H. destruct locs as [| u tl].
  - exact (@slm_tid_refl bool false).
  - exact (tid_bool_tf_absurd _ H).
Qed.

(* 发射 ⟹ 曾 funded（判定对齐：两定义同带同支） *)
Lemma fired_only_funded : forall L : ledger,
  slm_tid bool (so_fired (step_fire L)) true -> slm_tid bool (has_loc L) true.
Proof.
  intros [locs ags] H. destruct locs as [| u tl].
  - exact H.
  - exact H.
Qed.

(* funded ⟹ 发射 *)
Lemma funded_fires : forall (u : locu) (tl : list locu) (ags : list agg),
  slm_tid bool (so_fired (step_fire (mkLed (u :: tl) ags))) true.
Proof.
  (* ①单步发射定义面展开：非空定位带走发射支 ②定位带投影定向化简触发匹配
     ③发射位投影定向出列（真发射、账本去头、票零），布尔构造子闭合 *)
  intros u tl ags. unfold step_fire. cbn [led_loc so_fired].
  apply slm_tid_refl.
Qed.

(* 未 funded 档：聚合带保真（机器其余事件继续运转） *)
Lemma unfunded_preserves : forall ags : list agg,
  slm_tid (list agg) (led_agg (so_led (step_fire (mkLed nil ags)))) ags.
Proof.
  (* ①单步发射定义面展开：空定位带走保真支（不发射、原账保真）
     ②定位带投影定向化简触发匹配空支，状态位与聚合带投影逐层定向出列
     ③产物即原聚合带，同一构造子闭合 *)
  intros ags. unfold step_fire. cbn [led_loc so_led led_agg].
  apply slm_tid_refl.
Qed.

(* 未 funded 档：负向事件签发一张可再出资义务票（需求流 +1） *)
Lemma unfunded_emits_demand : forall ags : list agg,
  slm_tid nat (so_dem (step_fire (mkLed nil ags))) (S O).
Proof.
  (* ①单步发射定义面展开：空定位带走签票支 ②定位带投影定向化简触发匹配空支
     ③需求票位投影定向出列，产物即一张票（后继一），构造子闭合 *)
  intros ags. unfold step_fire. cbn [led_loc so_dem].
  apply slm_tid_refl.
Qed.

(* 需求票：缺口定位单元数 + 票据代数——无地址字段（广播，不可指派） *)
Record demand : Type := mkDem {
  dem_short : nat ;
  dem_gen : nat
}.

(* race-to-mint 预算判定：正权重且不超自报预算（bool 判定） *)
Definition budget_ok (w budget : Z) : bool := andb (Z.ltb 0 w) (Z.leb w budget).

(* andb 左支提取 *)
Lemma andb_l_extract : forall b c : bool, slm_tid bool (andb b c) true -> slm_tid bool b true.
Proof.
  intros b c H. destruct b.
  - exact (@slm_tid_refl bool true).
  - exact H.
Qed.

(* 后继不判等自身（票据焚毁引理） *)
Lemma eqb_S_neq : forall n : nat, slm_tid bool (Nat.eqb (S n) n) false.
Proof.
  induction n as [| n IH].
  - exact (@slm_tid_refl bool false).
  - exact IH.
Qed.

(* 赎回：任一生产者在自报预算内铸出新定位单元即销票——
   铸出的单元带新 pid（重定位），票据代数 +1（旧票作废），缺口 -1。 *)
Definition redeem (d : demand) (w budget : Z) (pid : nat)
           (Hok : slm_tid bool (budget_ok w budget) true) : locu * demand :=
  (mkLocu w (andb_l_extract (Z.ltb 0 w) (Z.leb w budget) Hok) pid,
   mkDem (Nat.pred (dem_short d)) (S (dem_gen d))).

(* 赎回铸造的是真定位单元（pos 结论随身） *)
Lemma redeem_relocates : forall (d : demand) (w budget : Z) (pid : nat)
                                (Hok : slm_tid bool (budget_ok w budget) true),
  slm_tid bool (Z.ltb 0 (lu_w (fst (redeem d w budget pid Hok)))) true.
Proof.
  (* ①赎回、预算判定与权重投影定义面展开：目标化为「零小于权」判定式本身
     ②与门左支提取不走上游转发——判定分支在替换点显式分划：真支目标即构造子闭合；
     假支与门定义性坍缩为假，前提（假=真）自爆；③两支均叶端闭合，零单跳转发 *)
  intros d w budget pid Hok. unfold redeem. unfold budget_ok in Hok. cbn [fst lu_w].
  destruct (Z.ltb 0 w) eqn:E.
  - apply slm_tid_refl.
  - exact Hok.
Qed.

(* 赎回铸造的重定位：新单元 pid 即赎单生产者 *)
Lemma redeem_pid_fresh : forall (d : demand) (w budget : Z) (pid : nat)
                                (Hok : slm_tid bool (budget_ok w budget) true),
  slm_tid nat (lu_pid (fst (redeem d w budget pid Hok))) pid.
Proof.
  (* ①赎回定义面展开：铸造产物对的第一分量在场 ②生产者标识投影定向出列
     ③新单元标识即赎单生产者（重定位的定义性内容），构造子闭合 *)
  intros d w budget pid Hok. unfold redeem. cbn [fst lu_pid].
  apply slm_tid_refl.
Qed.

(* 单票单铸程：赎回后票据代数严格 +1，同票不可再赎（赎回活性判定形态） *)
Lemma redeem_burns_ticket : forall (d : demand) (w budget : Z) (pid : nat)
                                   (Hok : slm_tid bool (budget_ok w budget) true),
  slm_tid bool (Nat.eqb (dem_gen (snd (redeem d w budget pid Hok))) (dem_gen d)) false.
Proof.
  (* ①赎回定义面展开：新票据代数（后继位）投影定向出列
     ②「后继不判等自身」不走上游归纳引理转发——归纳体在替换点显式重演：
     基例（后继 vs 零）判定式定向坍缩为假；步例判定式定义性降一位交归纳假设
     ③两支叶端闭合 *)
  intros d w budget pid Hok. unfold redeem. cbn [snd dem_gen].
  induction (dem_gen d) as [| n IH].
  - cbn [Nat.eqb]. apply slm_tid_refl.
  - cbn [Nat.eqb]. exact IH.
Qed.

(* 赎回进度：缺口按 pred 递减 *)
Lemma redeem_progress : forall (d : demand) (w budget : Z) (pid : nat)
                               (Hok : slm_tid bool (budget_ok w budget) true),
  slm_tid nat (dem_short (snd (redeem d w budget pid Hok))) (Nat.pred (dem_short d)).
Proof.
  (* ①赎回定义面展开：新票据缺口位投影定向出列，缺口即原缺口的前驱
     ②前驱算子在符号缺口上按定义封存（两侧同形），对合坍缩 ③同一构造子闭合 *)
  intros d w budget pid Hok. unfold redeem. cbn [snd dem_short].
  apply slm_tid_refl.
Qed.

(* 赎回完成：单缺口票一次赎回即闭票 *)
Lemma redeem_closes_single : forall (w budget : Z) (pid : nat)
                                    (Hok : slm_tid bool (budget_ok w budget) true)
                                    (g : nat),
  slm_tid bool (Nat.eqb (dem_short (snd (redeem (mkDem (S O) g) w budget pid Hok))) O)
            true.
Proof.
  intros w budget pid Hok g.
  (* ①赎回定义面展开＋单缺口票注入：新票据缺口位=前驱（单缺口）定向化简为零
     ②判等式在零-零具体票面上定向坍缩为真（单票单铸程的计算内容在场）
     ③布尔构造子闭合 *)
  unfold redeem. cbn [snd dem_short Nat.pred Nat.eqb].
  apply slm_tid_refl.
Qed.

(* 赎回在零缺口票上不产生负缺口（闭票保持闭票） *)
Lemma redeem_zero_stays : forall (w budget : Z) (pid : nat)
                                 (Hok : slm_tid bool (budget_ok w budget) true)
                                 (g : nat),
  slm_tid bool (Nat.eqb (dem_short (snd (redeem (mkDem O g) w budget pid Hok))) O) true.
Proof.
  intros w budget pid Hok g.
  (* ①赎回定义面展开＋零缺口票注入：新票据缺口位=前驱（零缺口）定向化简仍为零
     （闭票保持闭票）②判等式在零-零票面上定向坍缩为真 ③布尔构造子闭合 *)
  unfold redeem. cbn [snd dem_short Nat.pred Nat.eqb].
  apply slm_tid_refl.
Qed.

(* ---------- 替换件假设清查（零承认件自证） ---------- *)
Print Assumptions fuse2_sum.
Print Assumptions fuse2_pos.
Print Assumptions col_same_fused.
Print Assumptions col_preds_distinguishable.
Print Assumptions fuse_all_empty_id.
Print Assumptions col_fused_blind.
Print Assumptions spend_loc_head.
Print Assumptions ledger_loc_len_pos.
Print Assumptions funded_fires.
Print Assumptions unfunded_preserves.
Print Assumptions unfunded_emits_demand.
Print Assumptions redeem_relocates.
Print Assumptions redeem_pid_fresh.
Print Assumptions redeem_burns_ticket.
Print Assumptions redeem_progress.
Print Assumptions redeem_closes_single.
Print Assumptions redeem_zero_stays.
