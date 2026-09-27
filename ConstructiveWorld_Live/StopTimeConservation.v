(* ==========================================================================)
   StopTimeConservation.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：ud_le_add_r、bond、bond_check、edge_spec、edge_map、edge_diss、edge_ok、edge_bi、edge_tame。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpConstitution.
Require Import UpBudgetReal.
Require Import UpStopTime.

(* ================= §1 ud_le_add_r 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Local Open Scope Q_scope.

(* §1 Q 层微件（使用 UpConstitution 桥；补右加法弱不等式）            *)

Lemma ud_le_add_r : forall z w : Q, Qle 0 w -> Qle z (z + w).
Proof.
  intros z w Hw.
  apply (Qle_trans z (z + 0) (z + w)).
  - apply (uc_qeq_le_r z (z + 0) z).
    + ring.
    + apply Qle_refl.
  - apply Qplus_le_compat; [apply Qle_refl | exact Hw].
Qed.

(* §2 件 1：券 bond——界券组合的 Set 层类型                           *)
(*   币制本体：eps 假设位是严格性的量化资源（余量多少 eps）。           *)

Record bond : Set := mk_bond {
  bd_id : nat;        (* 命题 id *)
  bd_bound : Q;       (* 界值：不超过哪个上界 *)
  bd_eps : Q;         (* eps 假设位：严格性余量 *)
  bd_src : nat        (* 签发源：哪个度量/格式 *)
}.

(* 券面校验器（Defined 可执行；inr 带拒绝码，对照宪法形态） *)
Inductive bond_reject : Set :=
| br_eps.              (* eps 假设位为负：无严格性余量可让渡 *)

Definition bond_check (bd : bond)
  : Or (QleT' 0 (bd_eps bd)) (And (Id (Qle_bool 0 (bd_eps bd)) false) bond_reject) :=
  match Qle_bool 0 (bd_eps bd) as b
        return Or (Id b true) (And (Id b false) bond_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, br_eps)
  end.

(* §3 件 2：兑换边 edge——eps 仿射重参数化的转化定理                   *)
(*   eps_out = a·eps_in + b，a > 0（斜率正 ⟹ 保严格序）。           *)

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

(* 正则边保持 eps 假设位严格正（严格性不因兑换湮灭） *)
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

(* 券沿边兑换：eps 假设位按仿射映射重参数化 *)
Definition bond_exchange (e : edge_spec) (bd : bond) : bond :=
  mk_bond (bd_id bd) (bd_bound bd) (edge_map e (bd_eps bd)) (ed_dst e).

Lemma bond_exchange_eps : forall (e : edge_spec) (bd : bond),
  bd_eps (bond_exchange e bd) == edge_map e (bd_eps bd).
Proof. intros e bd. exact (Qeq_refl (edge_map e (bd_eps bd))). Qed.

(* 币制守恒（券级实例）：入参 eps = 出参 eps + 耗散 *)
Theorem bond_exchange_conservation : forall (e : edge_spec) (bd : bond),
  bd_eps bd == bd_eps (bond_exchange e bd) + edge_diss e (bd_eps bd).
Proof.
  intros e bd. rewrite bond_exchange_eps.
  unfold edge_diss, edge_map. ring.
Qed.

(* 兑换保严格性：正则边 ⟹ 兑换后 eps 假设位仍严格正 *)
Theorem bond_exchange_pos : forall (e : edge_spec) (bd : bond),
  Id (edge_bi e) true -> QltT 0 (bd_eps bd) ->
  QltT 0 (bd_eps (bond_exchange e bd)).
Proof.
  intros e bd Hbi Hx.
  unfold bond_exchange.
  exact (edge_map_pos e (bd_eps bd) Hx Hbi).
Qed.


(* §4 件 3（主件）：edge_compound_affine——边复合 = eps 仿射复合      *)
(*   复合边斜率 = a2·a1 > 0（恒正线性可判定）；                      *)
(*   路径合法性 = 仿射复合恒正，布尔判定器 path2_ok 线性判定。        *)

Definition edge_comp (e2 e1 : edge_spec) : edge_spec :=
  mk_edge (ed_id e1) (ed_src e1) (ed_dst e2)
          (ed_a e2 * ed_a e1) (ed_a e2 * ed_b e1 + ed_b e2).

Lemma edge_comp_slope : forall e1 e2 : edge_spec,
  ed_a (edge_comp e2 e1) == ed_a e2 * ed_a e1.
Proof. intros e1 e2. exact (Qeq_refl (ed_a e2 * ed_a e1)). Qed.

Lemma edge_comp_b : forall e1 e2 : edge_spec,
  ed_b (edge_comp e2 e1) == ed_a e2 * ed_b e1 + ed_b e2.
Proof. intros e1 e2. exact (Qeq_refl (ed_a e2 * ed_b e1 + ed_b e2)). Qed.

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
  intros e1 e2 H1 H2.
  exact (Qlt_to_QltT 0 (ed_a (edge_comp e2 e1))
    (Qmult_lt_0_compat (ed_a e2) (ed_a e1)
      (QltT_to_Qlt 0 (ed_a e2) H2) (QltT_to_Qlt 0 (ed_a e1) H1))).
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

(* 温和边的复合仍温和（斜率乘积 ≤ 1）——耗散核算沿路径封闭 *)
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

(* §5 件 4：耗散核算 path_dissipation                                *)
(*   币制语义：eps 是守恒量——每次兑换 eps_in = eps_out + 耗散；        *)
(*   耗散沿路径可加（记录无重计/无凭空铸造）；                        *)
(*   温和边（a≤1）的耗散对入参 eps 单调（大额兑换耗散更大）。          *)

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

(* §6 件 5：借据 iou——查询未命中签发缺口义务（可再入）                 *)
(*   对照宪法 check_claim 的 inr 拒绝码形态：resolve 的 inr 载荷即借据。*)
(*   命中 = 可执行证书链（格式接续 + 斜率正 + 耗散在预算内 + 出参正）；  *)
(*   未命中 = 借据（缺口 from→to、耗散预算 δ、eps 假设位、回指查询 id）。  *)

Record query : Set := mk_query {
  qr_id : nat;        (* 查询 id *)
  qr_from : nat;      (* 持有格式 *)
  qr_to : nat;        (* 需求格式 *)
  qr_eps : Q;         (* 入参 eps（持券假设位） *)
  qr_delta : Q        (* 耗散预算 δ *)
}.

Record iou : Set := mk_iou {
  iou_from : nat;     (* 缺口源格式 *)
  iou_to : nat;       (* 缺口目标格式 *)
  iou_eps : Q;        (* 待重演的 eps 假设位 *)
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

(* 件 5b：借据再入——redeem（证成）与 reissue（义务持久）              *)
(*   redeem io e = e 若闭 io 的缺口则发证书（新边可长入图谱）；        *)
(*   兑换不过门则借据原样再入（义务不灭，可携新边重试）。              *)

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

(* 判定报文（非依赖形态：无 sigT，可整体提取；vm_compute 友好）        *)

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

(* §7 件 6：vm_compute 数值自测——3 边图谱 eps/2→eps/4→eps/8 链        *)
(*   图谱 = 3 条原始半耗散边 + 2 条复合边（复合封闭性使寻路可达）。      *)

(* 原始边：fmt0→fmt1→fmt2→fmt3，每段 eps 减半（a=1/2, b=0，零注入） *)
Definition e_h1 : edge_spec := mk_edge 1 0 1 (1#2) 0.
Definition e_h2 : edge_spec := mk_edge 2 1 2 (1#2) 0.
Definition e_h3 : edge_spec := mk_edge 3 2 3 (1#2) 0.

(* 复合边长入图谱：ec12 : fmt0→fmt2 斜率 1/4；ec123 : fmt0→fmt3 斜率 1/8 *)
Definition ec12 : edge_spec := edge_comp e_h2 e_h1.
Definition ec123 : edge_spec := edge_comp e_h3 ec12.

Definition atlas3 : list edge_spec := e_h1 :: e_h2 :: e_h3 :: ec12 :: ec123 :: nil.

(* 查询 7：持 fmt0、eps 假设位 1，要 fmt3，耗散预算 δ=1 —— 命中 ec123 *)
Definition q_chain : query := mk_query 7 0 3 1 1.
(* 查询 8：fmt3→fmt0 无任何边 —— 未命中，签发借据 *)
Definition q_back : query := mk_query 8 3 0 1 1.
(* 查询 9：fmt0→fmt3 但预算 δ=1/2 —— 耗散 7/8 超预算，借据（缺口义务） *)
Definition q_tight : query := mk_query 9 0 3 1 (1#2).

(* 链命中：出参 eps = 1/8（eps→eps/8），证书可执行 *)
Theorem demo_chain_hit : Id (resolve_report atlas3 q_chain) (rv_hit ec123 (1#8)).
Proof. vm_compute. reflexivity. Qed.

(* 路径耗散值：1 − 1/8 = 7/8（可加核算：1/2 + (3/4) 段耗散之和） *)
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

(* 件 5b 数值自测：借据再入——好边兑换闭合缺口，新边长入图谱          *)

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

(* 再入形态数值实例：坏边（负截距吞掉 eps 假设位）证不成，借据原样返回 *)
Definition e_bad : edge_spec := mk_edge 5 0 3 (15#16) (-1).

Theorem demo_redeem_reissue :
  sigT (fun r => Id (dis_redeem demo_io_tight e_bad) (inr r)).
Proof.
  exists (iou_issue (iou_query demo_io_tight)).
  unfold dis_redeem. vm_compute. reflexivity.
Qed.

(* §8 判定报文输出（G3 自测样例源）                                  *)

Eval vm_compute in resolve_report atlas3 q_chain.
Eval vm_compute in resolve_report atlas3 q_back.
Eval vm_compute in resolve_report atlas3 q_tight.
Eval vm_compute in resolve_report atlas4 q_tight.
Eval vm_compute in edge_diss ec123 1.
Eval vm_compute in bond_check (mk_bond 1 (3#2) (1#4) 0).
Eval vm_compute in edge_check e_good.
(* ================= §2 honest_stop 族 ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat.

Local Open Scope Q_scope.

(* §0 核算对象：诚实停时 + 链侧累计耗散                              *)

(* 诚实停时：停时 τ 对链 ch 诚实 = 观测深度不越过链头预算            *)
(*   （可选停时的离散形态：τ 是链生产窗口内的合法观测点）。            *)
Definition honest_stop (tau : nat) (ch : GChain) : Set :=
  NatLe tau (gchain_budget ch).

(* 链侧累计耗散：每步耗散 = 本节点头预算 − 下一节点头预算，            *)
(*   触底节点（gstop）计数归零、耗散记零（清零制口径，与 gbudget_at 同）。 *)
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

(* §1 A 件侧支撑：停时前缀长度件 + 无界预算恒等件 + 前缀耗散显式公式件  *)

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

(* §2 nat 核算主件：停时处预算守恒                                   *)

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

(* §3 B 件侧装配：eps 迭代兑换账（有限步链的显式守恒，n 步归纳形）       *)

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

(* B 装配件：两段路径上的核算守恒 = B1（复合边一次核算）× B2（耗散分解）   *)
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

(* §4 合成主件：可选停时型守恒核算（A×B 同一停时双账封平）               *)

(* 合成主件：给定诚实停时 τ（GuardedChain 停时，A1/A2 口径），           *)
(*   nat 预算账：停时剩余 + 累计耗散 = 初始预算 b（击破时刻总量守恒）；    *)
(*   Q  eps  账：初始 eps = τ 步复合边兑换后余量 + τ 步累计耗散          *)
(*              （B1 逐边守恒沿 τ 步迭代闭合）。                        *)
(*   同一 τ 同时封平两本账——可选停时守恒核算的完整形态。                 *)
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
