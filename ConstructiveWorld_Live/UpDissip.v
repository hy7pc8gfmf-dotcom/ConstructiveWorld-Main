(* ============================================================ *)
(* UpDissip.v —— BEA 2.0 耗散本位界汇经济：券/边/复合律/耗散记账/借据 *)
(*                                                              *)
(* 理论来源：ROUNDTABLE.md 席 3 终稿【BEA 2.0——耗散本位界汇经济】   *)
(*   「不算数、只换界」——券的 eps 槽位 = 严格性量化资源；           *)
(*   每条边 = 带 eps-重参数化的转化定理（入参 eps 仿射映射出参：      *)
(*   eps_out = a·eps_in + b，a > 0）；                              *)
(*   路径合法性 = 仿射复合恒正（沿路径线性可判定）；                 *)
(*   借据 = 未命中签发的缺口义务（可再入）。                         *)
(*                                                              *)
(* 交付六件：                                                    *)
(*   件 1  bond / bond_check   券类型（Set 层 Record）+ 券面校验器    *)
(*   件 2  edge_spec / edge_map / edge_check                       *)
(*                             兑换边：eps 仿射映射 + 斜率正性验证器  *)
(*   件 3  edge_compound_affine 主件：边复合 = eps 仿射复合；        *)
(*         path2_ok 线性可判定路径合法性 + edge_comp_legal          *)
(*   件 4  diss_conservation（币制守恒恒等式）+                     *)
(*         path_dissipation_additive（路径耗散可加）+               *)
(*         path_dissipation_mono（耗散对入参 eps 单调）              *)
(*   件 5  iou_issue 借据签发（查询未命中 → 缺口义务载荷的 inr）      *)
(*         + redeem 借据再入 + redeem_closes（证成 ⟹ 图谱成长闭合）   *)
(*   件 6  vm_compute 自测：3 边图谱 eps/2→eps/4→eps/8 链           *)
(*                                                              *)
(* 层位纪律：语句全 Set 层（QltT/QleT'/Id/sigT/And/Or，判定走        *)
(*   Qle_bool/Qlt_bool/Nat.eqb）；Prop 零出场。消费 UpConstitution   *)
(*   的 Q 层桥（uc_qeq_le 等）。全部 Qed/Defined 闭合。              *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpConstitution.

Local Open Scope Q_scope.

(* ============================================================ *)
(* §1 Q 层微件（消费 UpConstitution 桥；补右加法弱不等式）            *)
(* ============================================================ *)

Lemma ud_le_add_r : forall z w : Q, Qle 0 w -> Qle z (z + w).
Proof.
  intros z w Hw.
  apply (Qle_trans z (z + 0) (z + w)).
  - apply (uc_qeq_le_r z (z + 0) z).
    + ring.
    + apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hw].
Qed.

(* ============================================================ *)
(* §2 件 1：券 bond——界券组合的 Set 层类型                           *)
(*   币制本体：eps 槽位是严格性的量化资源（余量多少 eps）。           *)
(* ============================================================ *)

Record bond : Set := mk_bond {
  bd_id : nat;        (* 命题 id *)
  bd_bound : Q;       (* 界值：不超过哪个上界 *)
  bd_eps : Q;         (* eps 槽位：严格性余量 *)
  bd_src : nat        (* 签发源：哪个度量/格式 *)
}.

(* 券面校验器（Defined 可执行；inr 带拒绝码，对照宪法形态） *)
Inductive bond_reject : Set :=
| br_eps.              (* eps 槽位为负：无严格性余量可让渡 *)

Definition bond_check (bd : bond)
  : Or (QleT' 0 (bd_eps bd)) (And (Id (Qle_bool 0 (bd_eps bd)) false) bond_reject) :=
  match Qle_bool 0 (bd_eps bd) as b
        return Or (Id b true) (And (Id b false) bond_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, br_eps)
  end.

(* ============================================================ *)
(* §3 件 2：兑换边 edge——eps 仿射重参数化的转化定理                   *)
(*   eps_out = a·eps_in + b，a > 0（斜率正 ⟹ 保严格序）。           *)
(* ============================================================ *)

Record edge_spec : Set := mk_edge {
  ed_id : nat;        (* 边 id *)
  ed_src : nat;       (* 源格式（度量索引） *)
  ed_dst : nat;       (* 目标格式 *)
  ed_a : Q;           (* 斜率 a > 0 *)
  ed_b : Q            (* 截距 b *)
}.

Definition edge_map (e : edge_spec) (x : Q) : Q := ed_a e * x + ed_b e.
Definition edge_diss (e : edge_spec) (x : Q) : Q := x - edge_map e x.
Definition edge_ok (e : edge_spec) : bool := Qlt_bool 0 (ed_a e).
Definition edge_bi (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool 0 (ed_b e)).
Definition edge_tame (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool (ed_a e) 1).

(* 边验证器（Defined 可执行；拒绝码形态） *)
Inductive edge_reject : Set :=
| er_slope.             (* 斜率非正：兑换不保严格序 *)

Definition edge_check (e : edge_spec)
  : Or (QltT 0 (ed_a e)) (And (Id (Qlt_bool 0 (ed_a e)) false) edge_reject) :=
  match Qlt_bool 0 (ed_a e) as b
        return Or (Id b true) (And (Id b false) edge_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, er_slope)
  end.

(* 布尔门证书提取：正则边（a>0 ∧ b≥0）的两个 Q 事实 *)
Lemma edge_bi_spec : forall e : edge_spec,
  Id (edge_bi e) true -> And (Qlt 0 (ed_a e)) (Qle 0 (ed_b e)).
Proof.
  intros e H. unfold edge_bi in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool 0 (ed_b e)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply QltT_to_Qlt. apply RealSetoid.eq_Id. exact E1.
  - apply QleT'_to_Qle. apply RealSetoid.eq_Id. exact E2.
Qed.

(* 温和边（a>0 ∧ a≤1）的两个 Q 事实 *)
Lemma edge_tame_spec : forall e : edge_spec,
  Id (edge_tame e) true -> And (Qlt 0 (ed_a e)) (Qle (ed_a e) 1).
Proof.
  intros e H. unfold edge_tame, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e)) eqn:E1; destruct (Qle_bool (ed_a e) 1) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  split.
  - apply QltT_to_Qlt. apply RealSetoid.eq_Id. exact E1.
  - apply QleT'_to_Qle. apply RealSetoid.eq_Id. exact E2.
Qed.

(* 边=转化定理的序性质：a>0 ⟹ eps 仿射重参数化严格保序 *)
Lemma edge_strict_mono : forall (e : edge_spec) (x y : Q),
  Qlt 0 (ed_a e) -> Qlt x y -> Qlt (edge_map e x) (edge_map e y).
Proof.
  intros e x y Ha Hxy. unfold edge_map.
  assert (H1 : Qlt (x * ed_a e) (y * ed_a e)).
  { apply (Qmult_lt_compat_r x y (ed_a e) Ha Hxy). }
  assert (H2a : Qlt (ed_a e * x) (y * ed_a e)).
  { apply (uc_qeq_lt_l (x * ed_a e) (ed_a e * x) (y * ed_a e)).
    - ring.
    - exact H1. }
  assert (H2 : Qlt (ed_a e * x) (ed_a e * y)).
  { apply (uc_qeq_lt_r (y * ed_a e) (ed_a e * y) (ed_a e * x)).
    - ring.
    - exact H2a. }
  assert (H3 : Qlt (ed_b e + ed_a e * x) (ed_b e + ed_a e * y)).
  { apply (proj2 (Qplus_lt_r (ed_a e * x) (ed_a e * y) (ed_b e))). exact H2. }
  assert (H4 : Qlt (ed_a e * x + ed_b e) (ed_b e + ed_a e * y)).
  { apply (uc_qeq_lt_l (ed_b e + ed_a e * x)
                       (ed_a e * x + ed_b e)
                       (ed_b e + ed_a e * y)).
    - ring.
    - exact H3. }
  apply (uc_qeq_lt_r (ed_b e + ed_a e * y)
                     (ed_a e * y + ed_b e)
                     (ed_a e * x + ed_b e)).
  - ring.
  - exact H4.
Qed.

(* 正则边保持 eps 槽位严格正（严格性不因兑换湮灭） *)
Lemma edge_map_pos : forall (e : edge_spec) (x : Q),
  QltT 0 x -> Id (edge_bi e) true -> QltT 0 (edge_map e x).
Proof.
  intros e x Hx Hbi.
  pose proof (edge_bi_spec e Hbi) as [Ha Hb].
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (ed_a e * x) (edge_map e x)).
  - apply (Qmult_lt_0_compat (ed_a e) x Ha (QltT_to_Qlt 0 x Hx)).
  - unfold edge_map.
    apply (uc_qeq_le_l (ed_a e * x + 0) (ed_a e * x) (ed_a e * x + ed_b e)).
    + ring.
    + apply Qplus_le_compat; [apply Qle_refl | exact Hb].
Qed.

(* 券沿边兑换：eps 槽位按仿射映射重参数化 *)
Definition bond_exchange (e : edge_spec) (bd : bond) : bond :=
  mk_bond (bd_id bd) (bd_bound bd) (edge_map e (bd_eps bd)) (ed_dst e).

Lemma bond_exchange_eps : forall (e : edge_spec) (bd : bond),
  bd_eps (bond_exchange e bd) == edge_map e (bd_eps bd).
Proof. intros e bd. reflexivity. Qed.

(* 币制守恒（券级实例）：入参 eps = 出参 eps + 耗散 *)
Theorem bond_exchange_conservation : forall (e : edge_spec) (bd : bond),
  bd_eps bd == bd_eps (bond_exchange e bd) + edge_diss e (bd_eps bd).
Proof.
  intros e bd. rewrite bond_exchange_eps.
  unfold edge_diss, edge_map. ring.
Qed.

(* 兑换保严格性：正则边 ⟹ 兑换后 eps 槽位仍严格正 *)
Theorem bond_exchange_pos : forall (e : edge_spec) (bd : bond),
  Id (edge_bi e) true -> QltT 0 (bd_eps bd) ->
  QltT 0 (bd_eps (bond_exchange e bd)).
Proof.
  intros e bd Hbi Hx. unfold bond_exchange.
  apply (edge_map_pos e (bd_eps bd) Hx Hbi).
Qed.

(* ============================================================ *)
(* §4 件 3（主件）：edge_compound_affine——边复合 = eps 仿射复合      *)
(*   复合边斜率 = a2·a1 > 0（恒正线性可判定）；                      *)
(*   路径合法性 = 仿射复合恒正，布尔判定器 path2_ok 线性判定。        *)
(* ============================================================ *)

Definition edge_comp (e2 e1 : edge_spec) : edge_spec :=
  mk_edge (ed_id e1) (ed_src e1) (ed_dst e2)
          (ed_a e2 * ed_a e1) (ed_a e2 * ed_b e1 + ed_b e2).

Lemma edge_comp_slope : forall e1 e2 : edge_spec,
  ed_a (edge_comp e2 e1) == ed_a e2 * ed_a e1.
Proof. intros e1 e2. reflexivity. Qed.

Lemma edge_comp_b : forall e1 e2 : edge_spec,
  ed_b (edge_comp e2 e1) == ed_a e2 * ed_b e1 + ed_b e2.
Proof. intros e1 e2. reflexivity. Qed.

(* 主件：复合边的 eps 映射 = 两边映射的仿射复合（路径语义正确性） *)
Theorem edge_compound_affine : forall (e1 e2 : edge_spec) (x : Q),
  edge_map (edge_comp e2 e1) x == edge_map e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* 复合合法性：两边斜率正 ⟹ 复合斜率恒正 *)
Theorem edge_comp_legal : forall e1 e2 : edge_spec,
  QltT 0 (ed_a e1) -> QltT 0 (ed_a e2) -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H1 H2. apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (ed_a e2) (ed_a e1)
           (QltT_to_Qlt 0 (ed_a e2) H2) (QltT_to_Qlt 0 (ed_a e1) H1)).
Qed.

(* 路径合法性的线性（布尔）判定器：两段路径 *)
Definition path2_ok (e2 e1 : edge_spec) : bool :=
  andb (edge_ok e1) (edge_ok e2).

(* 判定器健全性：布尔判真 ⟹ 复合斜率恒正（线性可判定的合法性） *)
Theorem path2_ok_sound : forall e1 e2 : edge_spec,
  Id (path2_ok e2 e1) true -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H. unfold path2_ok, edge_ok in H.
  destruct (Qlt_bool 0 (ed_a e1)) eqn:E1; destruct (Qlt_bool 0 (ed_a e2)) eqn:E2;
    rewrite ?E1 in H; rewrite ?E2 in H; simpl in H; try (inversion H).
  apply edge_comp_legal.
  - apply RealSetoid.eq_Id. exact E1.
  - apply RealSetoid.eq_Id. exact E2.
Qed.

(* 温和边的复合仍温和（斜率乘积 ≤ 1）——耗散记账沿路径封闭 *)
Theorem edge_tame_comp : forall e1 e2 : edge_spec,
  Id (edge_tame e1) true -> Id (edge_tame e2) true ->
  Id (edge_tame (edge_comp e2 e1)) true.
Proof.
  intros e1 e2 H1 H2.
  pose proof (edge_tame_spec e1 H1) as [Ha1 Hb1].
  pose proof (edge_tame_spec e2 H2) as [Ha2 Hb2].
  assert (Hc : Qle (ed_a (edge_comp e2 e1)) 1).
  { assert (Ecomm : ed_a (edge_comp e2 e1) == ed_a e1 * ed_a e2).
    { rewrite edge_comp_slope. ring. }
    assert (Hbound : Qle (ed_a e1 * ed_a e2) 1).
    { apply (Qle_trans (ed_a e1 * ed_a e2) (1 * ed_a e2) 1).
      - apply (Qmult_le_compat_r (ed_a e1) 1 (ed_a e2) Hb1).
        apply (Qlt_le_weak 0 (ed_a e2) Ha2).
      - rewrite Qmult_1_l. exact Hb2. }
    apply (uc_qeq_le_l (ed_a e1 * ed_a e2) (ed_a (edge_comp e2 e1)) 1).
    - symmetry. exact Ecomm.
    - exact Hbound. }
  pose proof (edge_comp_legal e1 e2 (Qlt_to_QltT 0 (ed_a e1) Ha1)
                (Qlt_to_QltT 0 (ed_a e2) Ha2)) as Hp.
  pose proof (RealSetoid.Id_eq (Qlt_bool 0 (ed_a (edge_comp e2 e1))) true Hp) as EA.
  pose proof (Qle_to_QleT' (ed_a (edge_comp e2 e1)) 1 Hc) as HcT.
  pose proof (RealSetoid.Id_eq (Qle_bool (ed_a (edge_comp e2 e1)) 1) true HcT) as EB.
  unfold edge_tame, edge_ok.
  apply RealSetoid.eq_Id.
  rewrite EA. rewrite EB. reflexivity.
Qed.

(* ============================================================ *)
(* §5 件 4：耗散记账 path_dissipation                                *)
(*   币制语义：eps 是守恒量——每次兑换 eps_in = eps_out + 耗散；        *)
(*   耗散沿路径可加（簿记无重计/无凭空铸造）；                        *)
(*   温和边（a≤1）的耗散对入参 eps 单调（大额兑换耗散更大）。          *)
(* ============================================================ *)

(* 币制守恒恒等式 *)
Theorem diss_conservation : forall (e : edge_spec) (x : Q),
  x == edge_map e x + edge_diss e x.
Proof.
  intros e x. unfold edge_diss, edge_map. ring.
Qed.

(* 路径耗散可加：复合路径总耗散 = 段耗散之和（ telescoping 恒等式） *)
Theorem path_dissipation_additive : forall (e1 e2 : edge_spec) (x : Q),
  edge_diss (edge_comp e2 e1) x == edge_diss e1 x + edge_diss e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_diss, edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* 路径耗散单调：温和边 ⟹ 入参 eps 越大耗散越大 *)
Theorem path_dissipation_mono : forall (e : edge_spec) (x y : Q),
  Id (edge_tame e) true -> Qle y x -> Qle (edge_diss e y) (edge_diss e x).
Proof.
  intros e x y Ht Hyx.
  pose proof (edge_tame_spec e Ht) as [Ha Hb].
  assert (H1a : Qle 0 (1 - ed_a e)).
  { exact (uc_le_opp_shift (ed_a e) 1 Hb). }
  assert (Hxy : Qle 0 (x - y)).
  { exact (uc_le_opp_shift y x Hyx). }
  assert (Hprod : Qle 0 ((1 - ed_a e) * (x - y))).
  { apply (Qle_trans 0 (0 * (x - y)) ((1 - ed_a e) * (x - y))).
    - apply uc_qeq_le. ring.
    - apply (Qmult_le_compat_r 0 (1 - ed_a e) (x - y) H1a Hxy). }
  assert (Heq : edge_diss e x == edge_diss e y + (1 - ed_a e) * (x - y)).
  { unfold edge_diss, edge_map, Qminus. ring. }
  rewrite Heq.
  apply (Qle_trans (edge_diss e y)
                   (edge_diss e y + 0)
                   (edge_diss e y + (1 - ed_a e) * (x - y))).
  - apply (uc_qeq_le_r (edge_diss e y) (edge_diss e y + 0) (edge_diss e y)).
    + ring.
    + apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hprod].
Qed.

(* 路径级推论：两段温和边复合后耗散仍单调 *)
Theorem path_dissipation_mono_compound : forall (e1 e2 : edge_spec) (x y : Q),
  Id (edge_tame e1) true -> Id (edge_tame e2) true -> Qle y x ->
  Qle (edge_diss (edge_comp e2 e1) y) (edge_diss (edge_comp e2 e1) x).
Proof.
  intros e1 e2 x y H1 H2 Hyx.
  apply (path_dissipation_mono (edge_comp e2 e1) x y).
  - apply edge_tame_comp; assumption.
  - exact Hyx.
Qed.

(* ============================================================ *)
(* §6 件 5：借据 iou——查询未命中签发缺口义务（可再入）                 *)
(*   对照宪法 check_claim 的 inr 拒绝码形态：resolve 的 inr 载荷即借据。*)
(*   命中 = 可执行证书链（格式接续 + 斜率正 + 耗散在预算内 + 出参正）；  *)
(*   未命中 = 借据（缺口 from→to、耗散预算 δ、eps 槽位、回指查询 id）。  *)
(* ============================================================ *)

Record query : Set := mk_query {
  qr_id : nat;        (* 查询 id *)
  qr_from : nat;      (* 持有格式 *)
  qr_to : nat;        (* 需求格式 *)
  qr_eps : Q;         (* 入参 eps（持券槽位） *)
  qr_delta : Q        (* 耗散预算 δ *)
}.

Record iou : Set := mk_iou {
  iou_from : nat;     (* 缺口源格式 *)
  iou_to : nat;       (* 缺口目标格式 *)
  iou_eps : Q;        (* 待重演的 eps 槽位 *)
  iou_delta : Q;      (* 耗散预算 δ *)
  iou_ref : nat       (* 回指查询 id：证成后新边长入图谱 *)
}.

(* 借据签发：查询的缺口义务（未命中的唯一产物，不报错） *)
Definition iou_issue (q : query) : iou :=
  mk_iou (qr_from q) (qr_to q) (qr_eps q) (qr_delta q) (qr_id q).

(* 布尔门：true 发 Id b true 证，false 发 (Id b false, 借据) 载荷 *)
Definition bool_gate (b : bool) (w : iou) : Or (Id b true) (And (Id b false) iou) :=
  match b as x return Or (Id x true) (And (Id x false) iou) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, w)
  end.

(* 五道门（Defined 可执行）：格式接续 src/dst、斜率正、耗散在预算内、出参正 *)
Definition gate_src (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_src e) (qr_from q)) true)
       (And (Id (Nat.eqb (ed_src e) (qr_from q)) false) iou) :=
  bool_gate (Nat.eqb (ed_src e) (qr_from q)) (iou_issue q).

Definition gate_dst (e : edge_spec) (q : query)
  : Or (Id (Nat.eqb (ed_dst e) (qr_to q)) true)
       (And (Id (Nat.eqb (ed_dst e) (qr_to q)) false) iou) :=
  bool_gate (Nat.eqb (ed_dst e) (qr_to q)) (iou_issue q).

Definition gate_slope (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (ed_a e)) true)
       (And (Id (Qlt_bool 0 (ed_a e)) false) iou) :=
  bool_gate (Qlt_bool 0 (ed_a e)) (iou_issue q).

Definition gate_diss (e : edge_spec) (q : query)
  : Or (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
       (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) false) iou) :=
  bool_gate (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) (iou_issue q).

Definition gate_pos (e : edge_spec) (q : query)
  : Or (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true)
       (And (Id (Qlt_bool 0 (edge_map e (qr_eps q))) false) iou) :=
  bool_gate (Qlt_bool 0 (edge_map e (qr_eps q))) (iou_issue q).

(* 命中证书：五证包（全 Set 层 Id-of-bool，可提取） *)
Definition hit_cert (e : edge_spec) (q : query) : Set :=
  And (And (Id (Nat.eqb (ed_src e) (qr_from q)) true)
           (Id (Nat.eqb (ed_dst e) (qr_to q)) true))
      (And (Id (Qlt_bool 0 (ed_a e)) true)
           (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
                (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true))).

(* 单边兑换判定：全过发证书，任一门不过发借据（inr 带载荷） *)
Definition resolve1 (e : edge_spec) (q : query) : Or (hit_cert e q) iou :=
  match gate_src e q with
  | inr p => inr (snd p)
  | inl h1 =>
    match gate_dst e q with
    | inr p => inr (snd p)
    | inl h2 =>
      match gate_slope e q with
      | inr p => inr (snd p)
      | inl h3 =>
        match gate_diss e q with
        | inr p => inr (snd p)
        | inl h4 =>
          match gate_pos e q with
          | inr p => inr (snd p)
          | inl h5 => inl (((h1, h2), (h3, (h4, h5))))
          end
        end
      end
    end
  end.

(* Nat.eqb 判真 → Leibniz 相等的 Set 层 Id 桥 *)
Lemma nat_eqb_id : forall (x y : nat), Id (Nat.eqb x y) true -> Id x y.
Proof.
  intro x. induction x as [| x IH]; intros y H; destruct y as [| y]; simpl in H.
  - apply id_refl.
  - inversion H.
  - inversion H.
  - apply (RealSetoid.eq_Id (Nat.succ x) (Nat.succ y)).
    f_equal. apply RealSetoid.Id_eq. apply IH. exact H.
Qed.

(* 命中证书的语义形态：格式接续的直证 + Q 层事实 *)
Theorem hit_cert_honest : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  And (And (Id (ed_src e) (qr_from q)) (Id (ed_dst e) (qr_to q)))
      (And (QltT 0 (ed_a e))
           (And (QleT' (edge_diss e (qr_eps q)) (qr_delta q))
                (QltT 0 (edge_map e (qr_eps q))))).
Proof.
  intros e q [[h1 h2] [h3 [h4 h5]]].
  split; [split | split].
  - apply nat_eqb_id. exact h1.
  - apply nat_eqb_id. exact h2.
  - exact h3.
  - split; [exact h4 | exact h5].
Qed.

(* 布尔门拒绝分支的载荷恒为借据本身 *)
Lemma bool_gate_inr : forall (b : bool) (w : iou) (p1 : Id b false) (p2 : iou),
  Id (bool_gate b w) (inr (p1, p2)) -> Id p2 w.
Proof.
  intros b w p1 p2 H.
  pose proof (RealSetoid.Id_eq (bool_gate b w) (inr (p1, p2)) H) as E.
  unfold bool_gate in E. destruct b; simpl in E.
  - discriminate E.
  - injection E as E1 E2.
    apply RealSetoid.eq_Id. symmetry. exact E2.
Qed.

(* 件 5 主定理：单边未命中 ⟹ 借据携带缺口义务（from/to/eps/δ 全回指查询） *)
Theorem resolve1_inr_fields : forall (e : edge_spec) (q : query) (r : iou),
  Id (resolve1 e q) (inr r) ->
  And (And (Id (iou_from r) (qr_from q)) (Id (iou_to r) (qr_to q)))
      (And (Id (iou_eps r) (qr_eps q)) (Id (iou_delta r) (qr_delta q))).
Proof.
  intros e q r H. unfold resolve1 in H.
  destruct (gate_src e q) as [h1 | [p11 p12]] eqn:Ep1;
    cbv beta iota in H.
  - destruct (gate_dst e q) as [h2 | [p21 p22]] eqn:Ep2;
      cbv beta iota in H.
    + destruct (gate_slope e q) as [h3 | [p31 p32]] eqn:Ep3;
        cbv beta iota in H.
      * destruct (gate_diss e q) as [h4 | [p41 p42]] eqn:Ep4;
          cbv beta iota in H.
        -- destruct (gate_pos e q) as [h5 | [p51 p52]] eqn:Ep5;
             cbv beta iota in H.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
           ++ pose proof (RealSetoid.Id_eq _ _ H) as E.
              injection E as E1.
              pose proof (bool_gate_inr _ _ _ _
                (RealSetoid.eq_Id _ _ Ep5)) as Hpay.
              rewrite <- E1. rewrite Hpay.
              split; [split; reflexivity | split; reflexivity].
        -- pose proof (RealSetoid.Id_eq _ _ H) as E.
           injection E as E1.
           pose proof (bool_gate_inr _ _ _ _
             (RealSetoid.eq_Id _ _ Ep4)) as Hpay.
           rewrite <- E1. rewrite Hpay.
           split; [split; reflexivity | split; reflexivity].
      * pose proof (RealSetoid.Id_eq _ _ H) as E.
        injection E as E1.
        pose proof (bool_gate_inr _ _ _ _
          (RealSetoid.eq_Id _ _ Ep3)) as Hpay.
        rewrite <- E1. rewrite Hpay.
        split; [split; reflexivity | split; reflexivity].
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (bool_gate_inr _ _ _ _
        (RealSetoid.eq_Id _ _ Ep2)) as Hpay.
      rewrite <- E1. rewrite Hpay.
      split; [split; reflexivity | split; reflexivity].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1.
    pose proof (bool_gate_inr _ _ _ _
      (RealSetoid.eq_Id _ _ Ep1)) as Hpay.
    rewrite <- E1. rewrite Hpay.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* 图谱扫描（Defined 可执行）：按格式键 (from,to) 找第一条服务边 *)
Fixpoint find_serving (g : list edge_spec) (f t : nat) : option edge_spec :=
  match g with
  | nil => None
  | e :: g' =>
      match Nat.eqb (ed_src e) f with
      | true =>
          match Nat.eqb (ed_dst e) t with
          | true => Some e
          | false => find_serving g' f t
          end
      | false => find_serving g' f t
      end
  end.

Lemma find_serving_cons_some : forall (e : edge_spec) (g : list edge_spec) (f t : nat),
  Nat.eqb (ed_src e) f = true -> Nat.eqb (ed_dst e) t = true ->
  Id (find_serving (e :: g) f t) (Some e).
Proof.
  intros e g f t H1 H2. simpl.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* 图谱级兑换：Some e 走单边判定，None 签发借据 *)
Definition resolve_opt (o : option edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) iou :=
  match o with
  | None => inr (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => inl (existT _ e w)
      | inr r => inr r
      end
  end.

Definition resolve (g : list edge_spec) (q : query)
  : Or (sigT (fun e => hit_cert e q)) iou :=
  resolve_opt (find_serving g (qr_from q) (qr_to q)) q.

Lemma resolve_opt_some : forall (e : edge_spec) (q : query) (w : hit_cert e q),
  Id (resolve1 e q) (inl w) ->
  Id (resolve_opt (Some e) q) (inl (existT _ e w)).
Proof.
  intros e q w H. unfold resolve_opt. rewrite H. reflexivity.
Qed.

(* 判定总全性：任何查询必得命中或借据（对照宪法 check_claim_total） *)
Theorem resolve_total : forall (g : list edge_spec) (q : query),
  Or (sigT (fun e => sigT (fun w => Id (resolve g q) (inl (existT _ e w)))))
     (sigT (fun r => Id (resolve g q) (inr r))).
Proof.
  intros g q. unfold resolve, resolve_opt.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r].
    + left. exists e. exists w. reflexivity.
    + right. exists r. reflexivity.
  - right. exists (iou_issue q). reflexivity.
Qed.

(* 件 5 图谱级形态：未命中 ⟹ 借据携带缺口义务 *)
Theorem resolve_miss_iou : forall (g : list edge_spec) (q : query) (r : iou),
  Id (resolve g q) (inr r) ->
  And (And (Id (iou_from r) (qr_from q)) (Id (iou_to r) (qr_to q)))
      (And (Id (iou_eps r) (qr_eps q)) (Id (iou_delta r) (qr_delta q))).
Proof.
  intros g q r H. unfold resolve, resolve_opt in H.
  destruct (find_serving g (qr_from q) (qr_to q)) as [e |].
  - destruct (resolve1 e q) as [w | r0] eqn:Eq; cbv beta iota in H.
    + pose proof (RealSetoid.Id_eq _ _ H) as E. discriminate E.
    + pose proof (RealSetoid.Id_eq _ _ H) as E.
      injection E as E1.
      pose proof (resolve1_inr_fields e q r0
        (RealSetoid.eq_Id _ _ Eq)) as [[Hf Ht] [He Hd]].
      rewrite <- E1.
      split; [split; assumption | split; assumption].
  - pose proof (RealSetoid.Id_eq _ _ H) as E.
    injection E as E1. rewrite <- E1.
    split; [split; reflexivity | split; reflexivity].
Qed.

(* 命中健全性：命中 ⟹ 出参 eps 严格正且耗散在预算内（可执行证书语义） *)
Theorem resolve_hit_sound : forall (g : list edge_spec) (q : query)
                                   (e : edge_spec) (w : hit_cert e q),
  Id (resolve g q) (inl (existT _ e w)) ->
  And (QltT 0 (edge_map e (qr_eps q)))
      (QleT' (edge_diss e (qr_eps q)) (qr_delta q)).
Proof.
  intros g q e w _. destruct w as [_ [_ [h4 h5]]].
  split; assumption.
Qed.

(* ============================================================ *)
(* 件 5b：借据再入——redeem（证成）与 reissue（义务持久）              *)
(*   redeem io e = e 若闭 io 的缺口则发证书（新边可长入图谱）；        *)
(*   兑换不过门则借据原样再入（义务不灭，可携新边重试）。              *)
(* ============================================================ *)

Definition iou_query (io : iou) : query :=
  mk_query (iou_ref io) (iou_from io) (iou_to io) (iou_eps io) (iou_delta io).

Definition dis_redeem (io : iou) (e : edge_spec) : Or (hit_cert e (iou_query io)) iou :=
  resolve1 e (iou_query io).

(* 再入：dis_redeem 拒绝 ⟹ 返回借据的缺口字段与原借据逐位相同（义务持久） *)
Theorem redeem_reissue : forall (io : iou) (e : edge_spec) (r : iou),
  Id (dis_redeem io e) (inr r) ->
  And (And (Id (iou_from r) (iou_from io))
           (And (Id (iou_to r) (iou_to io)) (Id (iou_eps r) (iou_eps io))))
      (Id (iou_delta r) (iou_delta io)).
Proof.
  intros io e r H.
  pose proof H as H'.
  pose proof (resolve1_inr_fields e (iou_query io) r H') as [[Hf Ht] [He Hd]].
  split.
  - split; [exact Hf | split; [exact Ht | exact He]].
  - exact Hd.
Qed.

(* 证成：借据被新边闭合 ⟹ 新边长入图谱且原查询命中（图谱成长定理） *)
Theorem redeem_closes : forall (io : iou) (e : edge_spec) (g : list edge_spec)
                               (w : hit_cert e (iou_query io)),
  Id (dis_redeem io e) (inl w) ->
  sigT (fun w2 => Id (resolve (e :: g) (iou_query io)) (inl w2)).
Proof.
  intros io e g w Hred.
  destruct w as [[h1 h2] [h3 [h4 h5]]].
  pose proof Hred as Hred'.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_src e) (qr_from (iou_query io))) true
                h1) as E1.
  pose proof (RealSetoid.Id_eq (Nat.eqb (ed_dst e) (qr_to (iou_query io))) true
                h2) as E2.
  pose proof (find_serving_cons_some e g (qr_from (iou_query io))
                (qr_to (iou_query io)) E1 E2) as Hfs.
  pose proof (RealSetoid.Id_eq _ _ Hfs) as Efs.
  pose proof (resolve_opt_some e (iou_query io)
              (((h1, h2), (h3, (h4, h5)))) Hred') as Hw2.
  exists (existT (fun e0 : edge_spec => hit_cert e0 (iou_query io)) e
                 (((h1, h2), (h3, (h4, h5))))).
  unfold resolve. rewrite Efs. exact Hw2.
Qed.

(* ============================================================ *)
(* 判定报文（非依赖形态：无 sigT，可整体提取；vm_compute 友好）        *)
(* ============================================================ *)

Inductive resolve_verdict : Set :=
| rv_hit : edge_spec -> Q -> resolve_verdict
| rv_miss : iou -> resolve_verdict.

Definition resolve_report (g : list edge_spec) (q : query) : resolve_verdict :=
  match find_serving g (qr_from q) (qr_to q) with
  | None => rv_miss (iou_issue q)
  | Some e =>
      match resolve1 e q with
      | inl w => rv_hit e (Qred (edge_map e (qr_eps q)))
      | inr r => rv_miss r
      end
  end.

(* ============================================================ *)
(* §7 件 6：vm_compute 数值自测——3 边图谱 eps/2→eps/4→eps/8 链        *)
(*   图谱 = 3 条原始半耗散边 + 2 条复合边（复合封闭性使寻路可达）。      *)
(* ============================================================ *)

(* 原始边：fmt0→fmt1→fmt2→fmt3，每段 eps 减半（a=1/2, b=0，零注入） *)
Definition e_h1 : edge_spec := mk_edge 1 0 1 (1#2) 0.
Definition e_h2 : edge_spec := mk_edge 2 1 2 (1#2) 0.
Definition e_h3 : edge_spec := mk_edge 3 2 3 (1#2) 0.

(* 复合边长入图谱：ec12 : fmt0→fmt2 斜率 1/4；ec123 : fmt0→fmt3 斜率 1/8 *)
Definition ec12 : edge_spec := edge_comp e_h2 e_h1.
Definition ec123 : edge_spec := edge_comp e_h3 ec12.

Definition atlas3 : list edge_spec := e_h1 :: e_h2 :: e_h3 :: ec12 :: ec123 :: nil.

(* 查询 7：持 fmt0、eps 槽位 1，要 fmt3，耗散预算 δ=1 —— 命中 ec123 *)
Definition q_chain : query := mk_query 7 0 3 1 1.
(* 查询 8：fmt3→fmt0 无任何边 —— 未命中，签发借据 *)
Definition q_back : query := mk_query 8 3 0 1 1.
(* 查询 9：fmt0→fmt3 但预算 δ=1/2 —— 耗散 7/8 超预算，借据（缺口义务） *)
Definition q_tight : query := mk_query 9 0 3 1 (1#2).

(* 链命中：出参 eps = 1/8（eps→eps/8），证书可执行 *)
Theorem demo_chain_hit : Id (resolve_report atlas3 q_chain) (rv_hit ec123 (1#8)).
Proof. vm_compute. reflexivity. Qed.

(* 路径耗散值：1 − 1/8 = 7/8（可加记账：1/2 + (3/4) 段耗散之和） *)
Theorem demo_diss_total : Id (Qred (edge_diss ec123 1)) (7#8).
Proof. vm_compute. reflexivity. Qed.

Theorem demo_diss_steps : edge_diss ec123 1
  == edge_diss ec12 1 + edge_diss e_h3 (edge_map ec12 1).
Proof. vm_compute. reflexivity. Qed.

(* 币制守恒恒等式的数值实例：1 = 1/8 + 7/8 *)
Theorem demo_conservation : 1 == edge_map ec123 1 + edge_diss ec123 1.
Proof. vm_compute. reflexivity. Qed.

(* 反向查询无边：未命中 ⟹ 借据（缺口 fmt3→fmt0，回指查询 8） *)
Theorem demo_miss_back : Id (resolve_report atlas3 q_back)
  (rv_miss (mk_iou 3 0 1 1 8)).
Proof. vm_compute. reflexivity. Qed.

(* 预算不足：耗散 7/8 > δ=1/2 ⟹ 借据（缺口 fmt0→fmt3，回指查询 9） *)
Theorem demo_tight_iou : Id (resolve_report atlas3 q_tight)
  (rv_miss (mk_iou 0 3 1 (1#2) 9)).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* 件 5b 数值自测：借据再入——好边兑换闭合缺口，新边长入图谱          *)
(* ============================================================ *)

Definition demo_io_tight : iou := mk_iou 0 3 1 (1#2) 9.

(* 好边：fmt0→fmt3 斜率 15/16 —— 耗散 1/16 ≤ 1/2，出参 15/16 > 0 *)
Definition e_good : edge_spec := mk_edge 4 0 3 (15#16) 0.

(* dis_redeem：借据 demo_io_tight 被 e_good 证成（五证全过） *)
Definition cert_good : hit_cert e_good (iou_query demo_io_tight) :=
  ((@id_refl bool true, @id_refl bool true),
   (@id_refl bool true, (@id_refl bool true, @id_refl bool true))).

Theorem demo_redeem_ok : Id (dis_redeem demo_io_tight e_good) (inl cert_good).
Proof. vm_compute. reflexivity. Qed.

(* redeem_closes 数值实例：新边长入图谱后，原查询 9 命中 e_good *)
Definition atlas4 : list edge_spec := e_good :: atlas3.

Theorem demo_growth_closes :
  Id (resolve_report atlas4 q_tight) (rv_hit e_good (15#16)).
Proof. vm_compute. reflexivity. Qed.

(* 再入形态数值实例：坏边（负截距吞掉 eps 槽位）证不成，借据原样返回 *)
Definition e_bad : edge_spec := mk_edge 5 0 3 (15#16) (-1).

Theorem demo_redeem_reissue :
  sigT (fun r => Id (dis_redeem demo_io_tight e_bad) (inr r)).
Proof.
  exists (iou_issue (iou_query demo_io_tight)).
  unfold dis_redeem. vm_compute. reflexivity.
Qed.

(* ============================================================ *)
(* §8 判定报文输出（G3 自测样例源）                                  *)
(* ============================================================ *)

Eval vm_compute in resolve_report atlas3 q_chain.
Eval vm_compute in resolve_report atlas3 q_back.
Eval vm_compute in resolve_report atlas3 q_tight.
Eval vm_compute in resolve_report atlas4 q_tight.
Eval vm_compute in edge_diss ec123 1.
Eval vm_compute in bond_check (mk_bond 1 (3#2) (1#4) 0).
Eval vm_compute in edge_check e_good.
