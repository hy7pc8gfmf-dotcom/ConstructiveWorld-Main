(* 五字段指针｜模块：LW0LeibSeparation。使命：本件形式化 π_geom 对每一有理数的
   无条件显式距离分离——LW0PiIrrational.v 主语句 lw0_pi_irrational（:13830 矛盾
   前件形，空转实锤见 _tlw550 正本 §〇）的升级面：去永假前提，改「Q 层可判定三
   分出闸的双支引擎」。本切片（S0 语句冻结＋S2 中间交付）闭合外侧支全链：
   Qcompare bool 出闸门 → Q 内核外侧支（窗距三点不等式）→ 升桥（π_L 度量投影
   ＋π_geom 跨岸传输）→ α 守卫形定理（守卫前提显式位，结论与 550 案一终形逐字
   同构，见证 c 由守卫真算非空转）。内侧支（Niven 松量链 G4a-d）语句面冻结于
   §4 注释，S3-S5 切片续作；本切片不落未闭合 statement，零承认式。
  依赖：S01_BaseRing（NatLe_drop/NatLe_lift）、S02_CauchyComplete（QltT/QleT'/
   Real/real_eq/real_lt/real_const/QltT_to_Qlt/Qlt_to_QltT）、S03_QExp
   （real_metric/q_abs_abs_triangle）、S10_KVQuantTrig（real_pi_geom/
   cauchy_real_pi_leibniz/real_pi_leibniz_proj）、PiEnvelope、
   UpReqIrrationalCriterion（lic_tail_bounded/lic_metric_proj）、LW2TrigBridge
   （lw2_channel_f1_closed）、LW0MLicBridge（lw0m_xL/lw0m_e/lw0m_tail_bounded_pi/
   lw0m_metric_congr）。S3-S5 预留：LW0PiIrrational（lw0_pi_contra_gate :6212/
   lw0_K_integer :5369/w0_lt1_core :5664/n_select :5521 系）。
  对标：_tlw550_无条件分离正本 §二.一 案一/案二、§三 段 A/B/C、§六红线；
   UpReqIrrationalCriterion.v :237/:242/:247/:277；LW0LicAdapt.v :58/:98（下游两
   定点适配件：新定理就位后删 Hp 实参一行即升无条件形，550 §四.4）。
  构造性：零公理声明／零承认式（闭合件件尾 Print Assumptions 全 Closed）；语句
   面全 Set 层零 Prop 泄露（sigT/And/QltT/real_lt 均 Set 值，Id false true 消去
   入 Set 合法——550 §六.2 口径）；证内 Prop（Qlt/Qle）仅脚手架，出口位一律
   Qlt_to_QltT 回 Set。外侧支见证 c := c0 依赖 (a,b,N,c0) 由 bool 出闸门真算，
   禁以任何永假前提消去产出见证（550 §六.4 特条）。
  编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" ""
   LW0LeibSeparation.v（工作位 Live_X；cpu_guard 包裹＋python 列表传参单一入口）。
  命名：leibsep_ 前缀（三树 grep -w 查重零占用实测）。 *)
(* 对标行：UpReqIrrationalCriterion.v :237-280｜LW0MLicBridge.v :16/:20/:28/:72｜
   LW2TrigBridge.v :132｜S10_KVQuantTrig.v :3038/:8559｜S02_CauchyComplete.v :465/:534/:929。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.
Require Import UpReqAltSumPos.
Require Import LW2TrigBridge.
Require Import LW0MLicBridge.
Require Import LW0PiIrrational.

Section LW0LeibSeparationSkel.

(* ============================================================ *)
(* §0 出闸门与 Qabs 消除微件（外侧支 Q 可判定面）                     *)
(* ============================================================ *)

(* 出闸门：外侧支开闸判定＝Qcompare 三分取 Lt（窗距 e N 加倍精度 2*c0           *)
(* 严格小于点距 |xL N − q|；bool 值，可判定，可 vm_compute 实例核对）。          *)
Definition leibsep_gate_open (q : Q) (N : nat) (c0 : Q) : bool :=
  match (lw0m_e N + 2 * c0) ?= Qabs ((lw0m_xL N - q)%Q) with
  | Lt => true
  | _ => false
  end.

(* 门真 ⟹ 守卫前提成立（Set 层 QltT）。路线：QltT 系 Set 值（S02 Id 形），       *)
(* CompareSpec 消去入 Set 非法（首发改红实测）——改 comparison 本体小归纳直接     *)
(* destruct：Eq/Gt 支门真假设自相矛盾 discriminate 直闭，Lt 支按 Qlt 定义式还原   *)
(* ============================================================ *)
(* §0' 纯构造 Q 线性序工具族（微件消除面：换岸桥＋正性字面＋opp 换岸 *)
(*   ＋求和器＋nat 正性族；全部经 _probe581 检验预验证形）。        *)
(* ============================================================ *)

Lemma leibsep_qlt_wd2 : forall a b c e : Q,
  a == c -> b == e -> Qlt a b -> Qlt c e.
Proof.
  intros a b c e Hac Hbe H.
  rewrite <- Hac. rewrite <- Hbe. exact H.
Qed.

Lemma leibsep_qle_wd2 : forall a b c e : Q,
  a == c -> b == e -> Qle a b -> Qle c e.
Proof.
  intros a b c e Hac Hbe H.
  rewrite <- Hac. rewrite <- Hbe. exact H.
Qed.

Lemma leibsep_qlt_minus : forall x y : Q, Qlt x y -> Qlt 0 (y - x).
Proof. intros x y H. exact (proj1 (Qlt_minus_iff x y) H). Qed.

Lemma leibsep_qlt_of_minus : forall x y : Q, Qlt 0 (y - x) -> Qlt x y.
Proof. intros x y H. exact (proj2 (Qlt_minus_iff x y) H). Qed.

Lemma leibsep_qle_minus : forall x y : Q, Qle x y -> Qle 0 (y - x).
Proof. intros x y H. exact (proj1 (Qle_minus_iff x y) H). Qed.

Lemma leibsep_qle_of_minus : forall x y : Q, Qle 0 (y - x) -> Qle x y.
Proof. intros x y H. exact (proj2 (Qle_minus_iff x y) H). Qed.

Lemma leibsep_qlt_1 : Qlt 0 1.
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_half : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_half_1 : Qlt (1 # 2) 1.
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_5 : Qlt 0 (5 # 1).
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_84 : Qlt 0 (84 # 1).
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qle_half : Qle 0 (1 # 2).
Proof. unfold Qle. simpl. discriminate. Qed.

Lemma leibsep_qle_one : Qle 0 1.
Proof. unfold Qle. simpl. discriminate. Qed.

Lemma leibsep_qlt_of_half : forall x : Q, Qlt 0 x -> Qlt 0 ((1 # 2) * x).
Proof.
  intros x Hx.
  pose proof (Qmult_lt_compat_r 0 (1 # 2) x Hx leibsep_qlt_half) as Hp.
  rewrite (Qmult_0_l x) in Hp. exact Hp.
Qed.

Lemma leibsep_qle_opp_swap : forall b s : Q, Qle (- b) s -> Qle (- s) b.
Proof.
  intros b s H.
  apply (leibsep_qle_wd2 (Qopp s) (Qopp (Qopp b)) (Qopp s) b
           (Qeq_refl (Qopp s)) (Qopp_involutive b)).
  exact (Qopp_le_compat (Qopp b) s H).
Qed.

Lemma leibsep_qlt_sum_weak : forall X Y : Q, Qlt 0 X -> Qle 0 Y -> Qlt 0 (X + Y).
Proof.
  intros X Y HX HY.
  assert (Ecomm : (Y + X)%Q == (X + Y)%Q) by ring.
  apply (leibsep_qlt_wd2 0 (Y + X)%Q 0 (X + Y)%Q (Qeq_refl 0) Ecomm).
  apply (Qlt_le_trans 0 X (Y + X)%Q HX).
  apply (leibsep_qle_wd2 (0 + X)%Q (Y + X)%Q X (Y + X)%Q
           (Qplus_0_l X) (Qeq_refl (Y + X)%Q)).
  exact (proj2 (Qplus_le_l 0 Y X) HY).
Qed.

Lemma leibsep_qlt_sum : forall X Y : Q, Qlt 0 X -> Qlt 0 Y -> Qlt 0 (X + Y).
Proof.
  intros X Y HX HY.
  apply leibsep_qlt_sum_weak; [ exact HX | apply Qlt_le_weak; exact HY ].
Qed.

Lemma leibsep_nat_pos_add : forall k X : nat, (1 <= k)%nat -> (0 < k + X)%nat.
Proof.
  intros k X Hk.
  apply (Nat.le_trans 1 k (k + X)%nat Hk (Nat.le_add_r k X)).
Qed.

Lemma leibsep_nat_pos2 : forall a : nat, (0 < 2 * a + 2)%nat.
Proof.
  intros a. rewrite Nat.add_comm.
  apply (leibsep_nat_pos_add 2 (2 * a)).
  apply Nat.le_succ_diag_r.
Qed.

Lemma leibsep_nat_pos3 : forall a : nat, (0 < 2 * a + 3)%nat.
Proof.
  intros a. rewrite Nat.add_comm.
  apply (leibsep_nat_pos_add 3 (2 * a)).
  apply (Nat.le_trans 1 2 3 (Nat.le_succ_diag_r 1) (Nat.le_succ_diag_r 2)).
Qed.

Lemma leibsep_nat_pos23 : forall a b : nat, (0 < 2 * a + 2 * b + 3)%nat.
Proof.
  intros a b. rewrite Nat.add_comm.
  apply (leibsep_nat_pos_add 3 (2 * a + 2 * b)%nat).
  apply (Nat.le_trans 1 2 3 (Nat.le_succ_diag_r 1) (Nat.le_succ_diag_r 2)).
Qed.

Lemma leibsep_nat_pos24 : forall a b : nat, (0 < 2 * a + 2 * b + 4)%nat.
Proof.
  intros a b. rewrite Nat.add_comm.
  apply (leibsep_nat_pos_add 4 (2 * a + 2 * b)%nat).
  apply (Nat.le_trans 1 2 4 (Nat.le_succ_diag_r 1)
           (Nat.le_trans 2 3 4 (Nat.le_succ_diag_r 2) (Nat.le_succ_diag_r 3))).
Qed.

(* 后 Qlt_to_QltT 升 Set。                                                       *)
Lemma leibsep_gate_open_true : forall (q : Q) (N : nat) (c0 : Q),
  leibsep_gate_open q N c0 = true ->
  QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)).
Proof.
  intros q N c0 H. unfold leibsep_gate_open in H.
  destruct (lw0m_e N + 2 * c0 ?= Qabs ((lw0m_xL N - q)%Q))%Q eqn:Hcmp.
  - discriminate H.
  - apply Qlt_to_QltT. apply Qlt_alt. exact Hcmp.
  - discriminate H.
Qed.

(* Qabs 上界 ⟹ 单侧下界（窗件 leiblw_S_tail_two_sided 内 Habs2 段同法提件）。 *)
Lemma leibsep_qabs_low : forall d t : Q, Qlt (Qabs d) t -> Qlt (- t) d.
Proof.
  intros d t H.
  destruct (Qlt_le_dec d 0) as [Hd | Hd].
  - assert (Habs : Qabs d == (- d)%Q)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hd).
    assert (Hdlt : Qlt (- d) t)
      by (apply (leibsep_qlt_wd2 (Qabs d) t (- d) t
                  Habs (Qeq_refl t) H)).
    assert (Hdpos : Qlt 0 (- d)%Q)
      by (apply (leibsep_qlt_wd2 0 (0 - d)%Q 0 (- d)%Q
                  (Qeq_refl 0) (Qplus_0_l (- d)%Q)
                  (leibsep_qlt_minus d 0 Hd))).
    exact (q_abs_gt_neg d t (Qlt_trans 0 (- d) t Hdpos Hdlt) H).
  - assert (Habs : Qabs d == d) by (apply Qabs_pos; exact Hd).
    assert (Hdlt : Qlt d t)
      by (apply (leibsep_qlt_wd2 (Qabs d) t d t Habs (Qeq_refl t) H)).
    exact (q_abs_gt_neg d t (Qle_lt_trans 0 d t Hd Hdlt) H).
Qed.

(* ============================================================ *)
(* §1 段 A：Q 内核外侧支（550 正本 §三 段 A 微证链）                  *)
(*   守卫 e N + 2*c0 < |xL N − q| ＋ 尾控 |xL m − xL N| < e N (m ≥ N ≥ 1)      *)
(*   ⟹ 三角收拢 |xL m − q| > 2*c0（对一切 m ≥ N；见证 N 本身）。               *)
(* ============================================================ *)

Lemma leibsep_q_kernel_guarded :
  forall (q : Q) (N : nat) (c0 : Q),
    (1 <= N)%nat ->
    QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)) ->
    sigT (fun M : nat => forall m : nat, NatLe M m ->
      QltT (2 * c0)%Q (Qabs ((lw0m_xL m - q)%Q))).
Proof.
  intros q N c0 HN1 Hguard.
  exists N. intros m Hm.
  apply Qlt_to_QltT.
  assert (Htail : Qlt (Qabs ((lw0m_xL m - lw0m_xL N)%Q)) (lw0m_e N)).
  { apply QltT_to_Qlt.
    exact (lw0m_tail_bounded_pi N m HN1 (NatLe_drop _ _ Hm)). }
  assert (Hgr : Qlt (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)))
    by (apply QltT_to_Qlt; exact Hguard).
  (* 三角：xL N − q ＝ (xL m − q) ＋ (xL N − xL m) 取绝对值收拢 *)
  assert (Htri0 : Qle (Qabs (((lw0m_xL m - q) + (lw0m_xL N - lw0m_xL m))%Q))
                      (Qabs ((lw0m_xL m - q)%Q)
                       + Qabs ((lw0m_xL N - lw0m_xL m)%Q)))
    by apply Qabs_triangle.
  assert (HabsEq : Qabs (((lw0m_xL m - q) + (lw0m_xL N - lw0m_xL m))%Q)
                   == Qabs ((lw0m_xL N - q)%Q))
    by (apply Qabs_wd; ring).
  rewrite HabsEq in Htri0.
  (* 尾控对齐：Qabs_Qminus（eq 基，UpReqIrrationalCriterion :271 在盘判例） *)
  rewrite (Qabs_Qminus (lw0m_xL N) (lw0m_xL m)) in Htri0.
  pose proof (Qlt_le_trans _ _ _ Hgr Htri0) as H1.
  pose proof (proj2 (Qplus_lt_r (Qabs ((lw0m_xL m - lw0m_xL N)%Q))
                      (lw0m_e N) (Qabs ((lw0m_xL m - q)%Q))) Htail) as H2.
  pose proof (leibsep_qlt_minus _ _ (Qlt_trans _ _ _ H1 H2)) as Hp.
  assert (E : ((Qabs ((lw0m_xL m - q)%Q)
                + lw0m_e N)
               - (lw0m_e N + 2 * c0))%Q
              == (Qabs ((lw0m_xL m - q)%Q) - 2 * c0)%Q) by ring.
  rewrite E in Hp.
  exact (leibsep_qlt_of_minus _ _ Hp).
Qed.

(* ============================================================ *)
(* §2 段 B：升桥（550 正本 §三 段 B；缺口 G2 在此销）                  *)
(*   ① π_L 度量投影：projT1 (real_metric π_L (const q)) k ＝ |xL k − q|        *)
(*     （lic_metric_proj 通用件＋real_pi_leibniz_proj 定义性投影）。           *)
(*   ② π_geom 跨岸传输：real_eq π_geom π_L（lw2_channel_f1_closed 零前提）      *)
(*     经 lw0m_metric_congr 逐 eps 点态化。                                    *)
(* ============================================================ *)

Lemma leibsep_piL_metric_proj : forall (q : Q) (k : nat),
  projT1 (real_metric cauchy_real_pi_leibniz (real_const q)) k
    == Qabs ((lw0m_xL k - q)%Q).
Proof.
  intros q k.
  rewrite (lic_metric_proj cauchy_real_pi_leibniz q k).
  rewrite real_pi_leibniz_proj.
  reflexivity.
Qed.

Lemma leibsep_metric_pi_transport : forall (q eps : Q), QltT 0 eps ->
  sigT (fun Nr : nat => forall m : nat, NatLe Nr m ->
    QltT (Qabs (projT1 (real_metric real_pi_geom (real_const q)) m
                  - Qabs ((lw0m_xL m - q)%Q))) eps).
Proof.
  intros q eps Heps.
  destruct (lw0m_metric_congr real_pi_geom cauchy_real_pi_leibniz
              (real_const q) lw2_channel_f1_closed eps Heps) as [Nr HNr].
  exists Nr. intros m Hm.
  (* 定理性闭合：projT1 (real_metric π_L (const q)) m ≡ Qabs (lw0m_xL m − q)      *)
(* 系 lic_metric_proj＋real_pi_leibniz_proj 的定义性恒等（两件均 reflexivity     *)
(* 闭合），HNr 与本件语句可转换——exact 直闭，零 rewrite 打 QltT 型索引面。       *)
  exact (HNr m Hm).
Qed.

(* ============================================================ *)
(* §3 α 守卫形中间交付定理（550 正本缺口 G0＝本切片验收物）              *)
(*   结论与案一终形逐字同构（sigT c，QltT 0 c ∧ real_lt c (|π_geom − a/b|)）；  *)
(*   守卫假设＝出闸条件显式前提位，S3-S5 内侧支闭合后由 β 链销守卫升无条件形。  *)
(*   见证 c := c0：精度 (1#2)*c0 位取自传输 eps，Q 层全链纯构造闭，出口回 Set。  *)
(* ============================================================ *)

Theorem leibsep_pi_sep_alpha_guarded :
  forall (a b : Q) (N : nat) (c0 : Q),
    QltT 0 (Qabs b) ->
    (1 <= N)%nat ->
    QltT 0 c0 ->
    QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - a / b)%Q)) ->
    sigT (fun c : Q => And (QltT 0 c)
            (real_lt (real_const c)
               (real_metric real_pi_geom (real_const (a / b))))).
Proof.
  intros a b N c0 Hb HN1 Hc0 Hguard.
  destruct (leibsep_q_kernel_guarded (a / b)%Q N c0 HN1 Hguard) as [M HM].
  assert (Heps2 : QltT 0 ((1 # 2) * c0)%Q).
  { apply Qlt_to_QltT.
    assert (Hc0' : Qlt 0 c0) by (apply QltT_to_Qlt; exact Hc0).
    pose proof (leibsep_qlt_of_half c0 Hc0') as Hp. exact Hp. }
  destruct (leibsep_metric_pi_transport (a / b)%Q ((1 # 2) * c0)%Q Heps2)
    as [Nr HNr].
  exists c0. split.
  - exact Hc0.
  - exists ((1 # 2) * c0)%Q. split.
    + exact Heps2.
    + exists (Nat.max M Nr). intros n Hn.
      assert (HMaxM : NatLe M n).
      { apply NatLe_lift.
        pose proof (NatLe_drop (Nat.max M Nr) n Hn) as Hmax.
        apply (Nat.le_trans M (Nat.max M Nr) n (Nat.le_max_l M Nr) Hmax). }
      assert (HMaxN : NatLe Nr n).
      { apply NatLe_lift.
        pose proof (NatLe_drop (Nat.max M Nr) n Hn) as Hmax.
        apply (Nat.le_trans Nr (Nat.max M Nr) n (Nat.le_max_r M Nr) Hmax). }
      pose proof (QltT_to_Qlt _ _ (HM n HMaxM)) as Hk.
      pose proof (QltT_to_Qlt _ _ (HNr n HMaxN)) as Ht.
      pose proof (leibsep_qabs_low _ _ Ht) as Htlo.
      (* 纯 c0 形陈述后 exact 靠转换闭合：projT1 (real_const c0) n ≡ c0          *)
      (* （real_const Defined 定义性；Qeq-rewrite 打 QltT 型索引面不通，同上）。   *)
      assert (Hfin : Qlt ((1 # 2) * c0)
                     (projT1 (real_metric real_pi_geom (real_const (a / b))) n
                      - c0)%Q).
      { pose proof (leibsep_qlt_minus _ _ Hk) as HX.
        pose proof (leibsep_qlt_minus _ _ Htlo) as HY0.
        assert (EY : ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                       - Qabs ((lw0m_xL n - (a / b)%Q)%Q))
                      - - ((1 # 2) * c0))%Q
                     == ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                          - Qabs ((lw0m_xL n - (a / b)%Q)%Q)) + (1 # 2) * c0)%Q) by ring.
        assert (ESUM : (Qabs ((lw0m_xL n - (a / b)%Q)%Q) - 2 * c0
                        + ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                           - Qabs ((lw0m_xL n - (a / b)%Q)%Q)) + (1 # 2) * c0))%Q
                       == ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                            - c0) - (1 # 2) * c0)%Q) by ring.
        assert (HS : Qlt 0 ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                             - c0) - (1 # 2) * c0)%Q).
        { apply (leibsep_qlt_wd2 0
                   (Qabs ((lw0m_xL n - (a / b)%Q)%Q) - 2 * c0
                    + ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                        - Qabs ((lw0m_xL n - (a / b)%Q)%Q)) + (1 # 2) * c0))%Q
                   0
                   ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                     - c0) - (1 # 2) * c0)%Q
                   (Qeq_refl 0) ESUM).
          apply (leibsep_qlt_sum (Qabs ((lw0m_xL n - (a / b)%Q)%Q) - 2 * c0)%Q
                   ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                     - Qabs ((lw0m_xL n - (a / b)%Q)%Q)) + (1 # 2) * c0)%Q).
          - exact HX.
          - exact (leibsep_qlt_wd2 0
                     ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                       - Qabs ((lw0m_xL n - (a / b)%Q)%Q))
                      - - ((1 # 2) * c0))%Q
                     0
                     ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                       - Qabs ((lw0m_xL n - (a / b)%Q)%Q)) + (1 # 2) * c0)%Q
                     (Qeq_refl 0) EY HY0). }
        exact (proj2 (Qlt_minus_iff ((1 # 2) * c0)
                        ((projT1 (real_metric real_pi_geom (real_const (a / b))) n
                          - c0)%Q)) HS). }
      apply Qlt_to_QltT. exact Hfin.
Qed.

(* 出闸门真开实例两件（vm_compute 抽查：见证链真算非空转的机核背书；          *)
(* q := 0：e 1 ＝ 5/3 < |xL 1 − 0| ＝ 304/105，c0 := 1/10；                   *)
(* q := 3：N := 25，e 25 ＝ 5/51，|xL 25 − 3| ≈ 0.134 > 5/51 + 1/500）。       *)
Lemma leibsep_gate_sample_zero :
  leibsep_gate_open 0%Q 1%nat (1 # 10)%Q = true.
Proof. vm_compute. reflexivity. Qed.

Lemma leibsep_gate_sample_three :
  leibsep_gate_open 3%Q 25%nat (1 # 1000)%Q = true.
Proof. vm_compute. reflexivity. Qed.

End LW0LeibSeparationSkel.

(* ============================================================ *)
(* §4 内侧支分区（段 C：Niven 松量链——S3-S5 切片施工域，语句面冻结）    *)
(* ============================================================ *)
(* 双支引擎外壳（550 正本 §二.三/§三）：出闸判定 Qcompare (|xL N − q|)          *)
(* (e N + 2*c0) 三分——外侧支(Lt)已闭合如上；内侧支(≤)由 Niven 松量链推出        *)
(* Id false true 消去入同一 sigT 目标（该链前提 |π − q| ≤ δ 系可判定分支内     *)
(* 假设，其矛盾为数学引擎产出，非全局永假式引用——550 §六.4 响亮声明）。        *)
(*                                                                            *)
(* 〔S5 落地面一：案一终形（550 §二.一 逐字；落地定名 leibsep_pi_rational_     *)
(*   unconditional；由 β 销守卫后与本件 §3 定理合流）〕                        *)
(*   Theorem leibsep_pi_rational_unconditional :                              *)
(*     forall a b : Q,                                                        *)
(*       QltT 0 (Qabs b) ->                                                   *)
(*       sigT (fun c : Q => And (QltT 0 c)                                    *)
(*               (real_lt (real_const c)                                      *)
(*                  (real_metric real_pi_geom (real_const (a / b))))).        *)
(*                                                                            *)
(* 〔S5 落地面二：案二内核无条件形（550 §二.一 逐字改前缀；终形之内引擎）〕     *)
(*   Theorem leibsep_q_kernel :                                               *)
(*     forall q : Q,                                                          *)
(*       sigT (fun c : Q => And (QltT 0 c)                                    *)
(*         (sigT (fun N : nat => forall m : nat, NatLe N m ->                 *)
(*           QltT c (Qabs ((lw0m_xL m - q)%Q))))).                            *)
(*                                                                            *)
(* 〔S5 随件三：案三 lic 接口形（LW0LicAdapt lw0m_escape_at_cond :98 去前提     *)
(*   版；一行移植即升无条件形，550 §二.一 案三/§四.4）〕                       *)
(*   Lemma leibsep_escape_window_at :                                         *)
(*     forall a b : Q,                                                        *)
(*       QltT 0 (Qabs b) ->                                                   *)
(*       sigT (fun n : nat => And ((1 <= n)%nat)                              *)
(*               (QltT (lw0m_e n) (Qabs ((a / b - lw0m_xL n)%Q)))).           *)
(*                                                                            *)
(* 〔缺口移交清单（S3-S5 输入；坐标＝550 正本 §一/§三 实测）〕                 *)
(*  G4a pin 松量件：|sin q| ≤ δ′／cos q ≤ −1 + δ′（lw0_pi_pin_sin_zero :9814/ *)
(*    _pin_cos_neg_one :9825 的 slack 化；S10 cauchy_real_sin 尾件族＋         *)
(*    lw0_pitB_conv_sin_tail :7610＋lw0_sin_plus_eq_compat :746）。            *)
(*  G4b W 带 (10/3+δ) 松量族：lw0_Wb :1336 族 decr/ratio_bound/lt01/           *)
(*    altseq_cauchy 四件 slack 版（:2096/:1614/:1704/:1955）。                 *)
(*  G3 q 带零前提重供（G4b 前置）：real_pi_geom_gt_three S10 :9375＋           *)
(*    real_pi_geom_lt_ten_thirds S10 :9392＋lw0_real_lt_const_Qlt :5385 换岸。 *)
(*  G4c IBP 望远镜松量件（全单核心）：lw0_pitB_bridge :7138、                  *)
(*    lw0_pi_transport_Wb_K :13797 基线、lw0_pi_transport_Wb_K_ht_gap :9786    *)
(*    承载、lw0_pitB_pair_telescope :10010；GAPASUME 假设位 :9788-9792 消为    *)
(*    定理（若两切片不闭：降级 α 守卫形＋假设位显式承载续载，550 §五退路）。   *)
(*  G4d 双岸挤压闸：lw0_K_integer :5369 整数性＋lw0_pi_contra_gate :6212      *)
(*    （零前提直用）＋lw0_pi_w0_lt1_core :5664 併 d0 放大＋lw0_n_select :5521  *)
(*    系；1 − Λ(δ,n) < K/q_fact n < Λ(δ,n)、Λ < 1/2 ⟹ Id false true。        *)
(*  G6 规范对微件族：lw0_pi_b_den_pos :9679／lw0_pi_qdiv_one_self :9686 直代。 *)
(*  G5 leiblw 列 ↔ π_L 列桥（可选，仅注脚联动）：leiblw_S_SS :171＋lp_pair。   *)
(*  已销：G1（lw0m_metric_congr 在盘）、G2（§2 leibsep_piL_metric_proj）、     *)
(*    G0（§3 α 守卫形）。                                                     *)
(* ============================================================ *)

(* ============================================================ *)
(* §5 缺口 G3：q 带零前提重供（550 正本 §三 缺口 G3；555 移交清单第 3 项） *)
(*   q 带 (3−δ, 10/3+δ) 不再依赖 real_eq 守卫前提：仅取用 S10 零前提 π    *)
(*   双岸界（real_pi_geom_gt_three :9375／real_pi_geom_lt_ten_thirds      *)
(*   :9392）与「q 的度量带」假设（终入围包 eps-def 形；:5.丁 窗桥给出其   *)
(*   自 Q 层出闸数据的零前提供达形）。基线对照＝主件 lw0_pi_asm_q_bounds  *)
(*   :5442（real_eq 前提污染族，弃用不触碰）；换岸件 lw0_real_lt_const_   *)
(*   Qlt :5385 同款 cbn 配方在证内复用。                                  *)
(* ============================================================ *)

(* Qabs 上界双岸抽取（§0 leibsep_qabs_low 的 ≤ 版对偶件）。 *)
Lemma leibsep_qabs_le_two : forall d t : Q,
  Qle (Qabs d) t -> And (QleT' d t) (QleT' (- t) d).
Proof.
  intros d t H.
  destruct (Qlt_le_dec d 0) as [Hd | Hd].
  - assert (Habs : Qabs d == (- d)%Q)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hd).
    rewrite Habs in H. split.
    + exact (Qle_to_QleT' _ _ (Qle_trans d (- d)%Q t
               (Qle_trans d 0 (- d)%Q (Qlt_le_weak d 0 Hd)
                  (Qopp_le_compat d 0 (Qlt_le_weak d 0 Hd))) H)).
    + exact (Qle_to_QleT' _ _ (leibsep_qle_wd2 (Qopp t) (Qopp (Qopp d)) (Qopp t) d
               (Qeq_refl (Qopp t)) (Qopp_involutive d)
               (Qopp_le_compat (- d)%Q t H))).
  - assert (Habs : Qabs d == d) by (apply Qabs_pos; exact Hd).
    rewrite Habs in H. split.
    + exact (Qle_to_QleT' _ _ H).
    + exact (Qle_to_QleT' _ _ (Qle_trans (- t)%Q 0 d
               (Qopp_le_compat 0 t (Qle_trans 0 d t Hd H)) Hd)).
Qed.

(* 〔G3 主件〕度量带 ⟹ q 双岸带。lw0_pi_asm_q_bounds :5442 的去前提     *)
(* slack 形：左岸 3−δ < q、右岸 q < 10/3+δ；π 双岸界在盘零前提，度量带   *)
(* 系可判定分支内假设形（550 §六.4 响亮声明口径），见证逐点取四指标 max。*)
Lemma leibsep_q_band :
  forall (q delta : Q),
    QltT 0 delta ->
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m : nat, NatLe N m ->
        QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) (delta + eps)%Q)) ->
    And (QltT (3 - delta)%Q q) (QltT q (10 / 3 + delta)%Q).
Proof.
  intros q delta Hdel Hband.
  destruct real_pi_geom_gt_three as [eps3 [Heps3 [N3 HN3]]].
  destruct real_pi_geom_lt_ten_thirds as [eps10 [Heps10 [N10 HN10]]].
  assert (He3 : Qlt 0 (eps3 * (1 # 2))%Q).
  { assert (H3 : Qlt 0 eps3) by (apply QltT_to_Qlt; exact Heps3).
    pose proof (leibsep_qlt_of_half eps3 H3) as Hp.
    exact (leibsep_qlt_wd2 0 ((1 # 2) * eps3) 0 (eps3 * (1 # 2))
             (Qeq_refl 0) (Qmult_comm (1 # 2) eps3) Hp). }
  destruct (Hband (eps3 * (1 # 2))%Q) as [Nb1 Hb1].
  { apply Qlt_to_QltT. exact He3. }
  assert (He10 : Qlt 0 (eps10 * (1 # 2))%Q).
  { assert (H10 : Qlt 0 eps10) by (apply QltT_to_Qlt; exact Heps10).
    pose proof (leibsep_qlt_of_half eps10 H10) as Hp.
    exact (leibsep_qlt_wd2 0 ((1 # 2) * eps10) 0 (eps10 * (1 # 2))
             (Qeq_refl 0) (Qmult_comm (1 # 2) eps10) Hp). }
  destruct (Hband (eps10 * (1 # 2))%Q) as [Nb2 Hb2].
  { apply Qlt_to_QltT. exact He10. }
  assert (HMb1 : (Nb1 <= Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))%nat).
  { apply (Nat.le_trans Nb1 (Nat.max Nb1 N3)
             (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
             (Nat.le_max_l Nb1 N3)
             (Nat.le_max_l (Nat.max Nb1 N3) (Nat.max Nb2 N10))). }
  assert (HM3 : (N3 <= Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))%nat).
  { apply (Nat.le_trans N3 (Nat.max Nb1 N3)
             (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
             (Nat.le_max_r Nb1 N3)
             (Nat.le_max_l (Nat.max Nb1 N3) (Nat.max Nb2 N10))). }
  assert (HMb2 : (Nb2 <= Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))%nat).
  { apply (Nat.le_trans Nb2 (Nat.max Nb2 N10)
             (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
             (Nat.le_max_l Nb2 N10)
             (Nat.le_max_r (Nat.max Nb1 N3) (Nat.max Nb2 N10))). }
  assert (HM10 : (N10 <= Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))%nat).
  { apply (Nat.le_trans N10 (Nat.max Nb2 N10)
             (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
             (Nat.le_max_r Nb2 N10)
             (Nat.le_max_r (Nat.max Nb1 N3) (Nat.max Nb2 N10))). }
  pose proof (HN3 (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
              (NatLe_lift _ _ HM3)) as Hpi3.
  cbn [projT1 real_const] in Hpi3.
  pose proof (QltT_to_Qlt _ _ Hpi3) as Hpi3'.
  pose proof (QltT_to_Qlt _ _ Heps3) as Heps3'.
  destruct (leibsep_qabs_le_two _ _
             (QleT'_to_Qle _ _
                (Hb1 (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
                   (NatLe_lift _ _ HMb1)))) as [Hb1a Hb1b].
  pose proof (HN10 (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
              (NatLe_lift _ _ HM10)) as Hpi10.
  cbn [projT1 real_const] in Hpi10.
  pose proof (QltT_to_Qlt _ _ Hpi10) as Hpi10'.
  pose proof (QltT_to_Qlt _ _ Heps10) as Heps10'.
  destruct (leibsep_qabs_le_two _ _
             (QleT'_to_Qle _ _
                (Hb2 (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))
                   (NatLe_lift _ _ HMb2)))) as [Hb2a Hb2b].
  split.
  - apply Qlt_to_QltT.
    apply (leibsep_qlt_of_minus (3 - delta)%Q q).
    pose proof (leibsep_qlt_minus _ _ Hpi3') as HX.
    pose proof (leibsep_qle_minus _ _ (QleT'_to_Qle _ _ Hb1a)) as HY.
    pose proof (leibsep_qlt_of_half eps3 Heps3') as Hh.
    assert (E1 : ((1 # 2) * eps3
                  + (((projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - 3) - eps3)
                     + (delta + eps3 * (1 # 2)
                        - (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q))))%Q
                 == (q - (3 - delta))%Q) by ring.
    apply (leibsep_qlt_wd2 0
             ((1 # 2) * eps3
              + (((projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - 3) - eps3)
                 + (delta + eps3 * (1 # 2)
                    - (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q))))%Q
             0 (q - (3 - delta))%Q (Qeq_refl 0) E1).
    exact (leibsep_qlt_sum _ _ Hh (leibsep_qlt_sum_weak _ _ HX HY)).
  - apply Qlt_to_QltT.
    apply (leibsep_qlt_of_minus q (10 / 3 + delta)%Q).
    pose proof (leibsep_qlt_minus _ _ Hpi10') as HX.
    assert (Hb2b' : Qle (q - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)))%Q
                      (delta + eps10 * (1 # 2))%Q).
    { assert (H1 : Qle (- (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q))
                     (delta + eps10 * (1 # 2))%Q)
        by exact (leibsep_qle_opp_swap (delta + eps10 * (1 # 2))
                    (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q)%Q (QleT'_to_Qle _ _ Hb2b)).
      assert (E0 : (Qopp (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q))%Q
                   == (q - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)))%Q) by ring.
      exact (leibsep_qle_wd2 (Qopp (projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10)) - q))
               (delta + eps10 * (1 # 2))%Q
               (q - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))) (delta + eps10 * (1 # 2))%Q
               E0 (Qeq_refl (delta + eps10 * (1 # 2))%Q) H1). }
    pose proof (leibsep_qle_minus _ _ Hb2b') as HY.
    pose proof (leibsep_qlt_of_half eps10 Heps10') as Hh.
    assert (E2 : ((1 # 2) * eps10
                  + (((10 / 3 - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))) - eps10)
                     + (delta + eps10 * (1 # 2)
                        - (q - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))))))%Q
                 == ((10 / 3 + delta) - q)%Q) by ring.
    apply (leibsep_qlt_wd2 0
             ((1 # 2) * eps10
              + (((10 / 3 - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))) - eps10)
                 + (delta + eps10 * (1 # 2)
                    - (q - projT1 real_pi_geom (Nat.max (Nat.max Nb1 N3) (Nat.max Nb2 N10))))))%Q
             0 ((10 / 3 + delta) - q)%Q (Qeq_refl 0) E2).
    exact (leibsep_qlt_sum _ _ Hh (leibsep_qlt_sum_weak _ _ HX HY)).
Qed.

(* G3 右岸降形（G4b 取用位）：q < 10/3+δ ⟹ QleT' q (10/3+δ)。 *)
Lemma leibsep_q_band_upper_QleT' : forall (q delta : Q),
  QltT 0 delta ->
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m : nat, NatLe N m ->
      QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) (delta + eps)%Q)) ->
  QleT' q (10 / 3 + delta)%Q.
Proof.
  intros q delta Hdel Hband.
  destruct (leibsep_q_band q delta Hdel Hband) as [_ Hhi].
  apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hhi.
Qed.

(* G3 左岸推论（正性半件）：δ < 3 时度量带 ⟹ q > 0。 *)
Lemma leibsep_q_band_pos : forall (q delta : Q),
  QltT delta 3 -> QltT 0 delta ->
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m : nat, NatLe N m ->
      QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) (delta + eps)%Q)) ->
  QltT 0 q.
Proof.
  intros q delta Hd3 Hdel Hband.
  destruct (leibsep_q_band q delta Hdel Hband) as [Hlo _].
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hlo) as Hlo'.
  pose proof (QltT_to_Qlt _ _ Hd3) as Hd3'.
  exact (Qlt_trans 0 (3 - delta)%Q q (leibsep_qlt_minus _ _ Hd3') Hlo').
Qed.

(* 〔G3 窗桥〕Q 层列点窗＋尾控（lw0m_tail_bounded_pi 零前提）⟹ 度量带：   *)
(* G3 主件假设位的零前提供达形——内/外侧支出闸数据均可直供。               *)
Lemma leibsep_metric_band_of_window : forall (q w : Q) (N : nat),
  (1 <= N)%nat ->
  QltT (Qabs ((lw0m_xL N - q)%Q)) w ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun N2 : nat => forall m : nat, NatLe N2 m ->
    QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) (w + lw0m_e N + eps)%Q).
Proof.
  intros q w N HN1 Hwin eps Heps.
  destruct (leibsep_metric_pi_transport q eps Heps) as [Nr HNr].
  exists (Nat.max N Nr). intros m Hm.
  assert (HmN : (N <= m)%nat).
  { pose proof (NatLe_drop (Nat.max N Nr) m Hm) as Hmax.
    apply (Nat.le_trans N (Nat.max N Nr) m (Nat.le_max_l N Nr) Hmax). }
  assert (HmNr : (Nr <= m)%nat).
  { pose proof (NatLe_drop (Nat.max N Nr) m Hm) as Hmax.
    apply (Nat.le_trans Nr (Nat.max N Nr) m (Nat.le_max_r N Nr) Hmax). }
  pose proof (HNr m (NatLe_lift _ _ HmNr)) as Htr.
  pose proof (QltT_to_Qlt _ _ Htr) as Htr'.
  pose proof (QltT_to_Qlt _ _ Hwin) as Hwin'.
  assert (Htail : Qlt (Qabs ((lw0m_xL m - lw0m_xL N)%Q)) (lw0m_e N)).
  { apply QltT_to_Qlt. exact (lw0m_tail_bounded_pi N m HN1 HmN). }
  assert (Htri : Qle (Qabs ((lw0m_xL m - q)%Q)) (w + lw0m_e N)%Q).
  { assert (Ht0 : Qle (Qabs (((lw0m_xL N - q) + (lw0m_xL m - lw0m_xL N))%Q))
                      (Qabs ((lw0m_xL N - q)%Q)
                       + Qabs ((lw0m_xL m - lw0m_xL N)%Q)))
      by apply Qabs_triangle.
    assert (HabsEq : Qabs (((lw0m_xL N - q) + (lw0m_xL m - lw0m_xL N))%Q)
                   == Qabs ((lw0m_xL m - q)%Q))
      by (apply Qabs_wd; ring).
    rewrite HabsEq in Ht0.
    pose proof (proj2 (Qplus_le_l (Qabs ((lw0m_xL N - q)%Q)) w
                        (Qabs ((lw0m_xL m - lw0m_xL N)%Q)))
                 (Qlt_le_weak _ _ Hwin')) as H3a.
    pose proof (proj2 (Qplus_lt_r (Qabs ((lw0m_xL m - lw0m_xL N)%Q))
                        (lw0m_e N) w) Htail) as H3b.
    exact (Qlt_le_weak _ _
             (Qle_lt_trans (Qabs ((lw0m_xL m - q)%Q)) _ _
               Ht0 (Qle_lt_trans _ _ _ H3a H3b))). }
  apply (qleT'_trans (Qabs ((projT1 real_pi_geom m - q)%Q))
                     (projT1 (real_metric real_pi_geom (real_const q)) m)
                     (w + lw0m_e N + eps)%Q).
  - apply qeq_leT'. symmetry. apply (lic_metric_proj real_pi_geom q m).
  - apply Qle_to_QleT'.
    destruct (leibsep_qabs_le_two
                (projT1 (real_metric real_pi_geom (real_const q)) m
                 - Qabs ((lw0m_xL m - q)%Q))%Q eps (Qlt_le_weak _ _ Htr')) as [Hd1 Hd2].
    pose proof (leibsep_qle_minus _ _ (QleT'_to_Qle _ _ Hd1)) as Hp.
    assert (E : ((Qabs ((lw0m_xL m - q)%Q) + eps)
                 - projT1 (real_metric real_pi_geom (real_const q)) m)%Q
                == (eps - (projT1 (real_metric real_pi_geom (real_const q)) m
                           - Qabs ((lw0m_xL m - q)%Q)))%Q) by ring.
    apply (Qle_trans _ (Qabs ((lw0m_xL m - q)%Q) + eps)%Q _).
    + apply (leibsep_qle_of_minus _ _). rewrite E. exact Hp.
    + exact (proj2 (Qplus_le_l (Qabs ((lw0m_xL m - q)%Q))
                     (w + lw0m_e N)%Q eps) Htri).
Qed.

(* ============================================================ *)
(* §6 缺口 G4b：W 带 (10/3+δ) 松量族（550 正本 §三 段 C.2；555 移交第 4 项） *)
(*   基线 lw0_Wb_ratio_bound :1614／_lt01 :1704／_seq_dec_strict 的        *)
(*   q ≤ 10/3 全部放宽为 q ≤ 10/3+δ，率常数 25/27 换显式 ρ(δ) :=           *)
(*   (10/3+δ)²·(5/84)（可算闭式；δ=0 时 ρ = 125/189 < 25/27，界更紧）。    *)
(*   交叉相乘的 nat 多项式事实 84·(n+2j+2)(n+2j+3) ≤                       *)
(*   5·(2j+2)(2j+3)(2n+2j+3)(2n+2j+4)（n ≥ 2；(n,j)=(2,0) 取等）经 nia     *)
(*   闭合后 q_of_nat 单调升 Q。altseq 装配位＝泛件 lw0_altseq_cauchy       *)
(*   :1955（vanish 系显式假设槽，G4c/S4 取用），本件不重复落。             *)
(* ============================================================ *)

Lemma leibsep_qnat_mul : forall a b : nat,
  lw0_q_of_nat (a * b)%nat == lw0_q_of_nat a * lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qmult, Qeq.
  rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma leibsep_Wb_poly_nat : forall (n j : nat), (2 <= n)%nat ->
  (84 * (n + 2*j+2) * (n+2*j+3) <=
   5 * (2*j+2) * (2*j+3) * (2*n+2*j+3) * (2*n+2*j+4))%nat.
Proof.
  intros n j Hn. destruct n as [|[|u]];
    [ destruct (Nat.nle_succ_0 1 Hn)
    | destruct (Nat.nle_succ_0 0 (proj2 (Nat.succ_le_mono 1 0) Hn)) | ].
  nia.
Qed.

(* 率上界核：q²·X·84 ≤ Y·Qd²·5（q ≤ Qd ＋ nat 多项式事实两因子相乘）。 *)
Lemma leibsep_Wb_cross : forall (q Qd : Q) (n j : nat),
  QltT 0 q -> QleT' q Qd -> (2 <= n)%nat ->
  QleT' (q * q * lw0_q_of_nat (n + 2*j+2) * lw0_q_of_nat (n + 2*j+3) * (84 # 1))
        (lw0_q_of_nat (2*j+2) * lw0_q_of_nat (2*j+3) * lw0_q_of_nat (2*n+2*j+3)
         * lw0_q_of_nat (2*n+2*j+4) * (Qd * Qd) * (5 # 1))%Q.
Proof.
  intros q Qd n j Hq Hband Hn.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Hqq : QleT' (q * q) (Qd * Qd)).
  { apply (lw0_qcompat4 q Qd q Qd); assumption. }
  assert (Hpoly : QleT' (lw0_q_of_nat (84 * (n + 2*j+2) * (n+2*j+3)))
                        (lw0_q_of_nat
                          (5 * (2*j+2) * (2*j+3) * (2*n+2*j+3) * (2*n+2*j+4))))
    by (apply lw0_q_of_nat_le_mono; apply (leibsep_Wb_poly_nat n j Hn)).
  assert (Hnn1 : QleT' 0 (q * q)).
  { apply Qle_to_QleT'. apply Qlt_le_weak.
    apply Qmult_lt_0_compat; apply QltT_to_Qlt; exact Hq. }
  assert (Hnn2 : QleT' 0 (lw0_q_of_nat (84 * (n + 2*j+2) * (n+2*j+3))))
    by (apply lw0_q_of_nat_nonneg).
  pose proof (lw0_qcompat4 (q * q) (Qd * Qd)
               (lw0_q_of_nat (84 * (n + 2*j+2) * (n+2*j+3)))
               (lw0_q_of_nat
                 (5 * (2*j+2) * (2*j+3) * (2*n+2*j+3) * (2*n+2*j+4)))
               Hnn1 Hqq Hnn2 Hpoly) as Hcomb.
  assert (EnL : (q * q * lw0_q_of_nat (n + 2*j+2) * lw0_q_of_nat (n + 2*j+3)
                 * (84 # 1))%Q ==
                ((q * q) * lw0_q_of_nat (84 * (n + 2*j+2) * (n+2*j+3)))%Q).
  { rewrite !leibsep_qnat_mul.
    assert (Eq84 : lw0_q_of_nat 84 == (84 # 1)) by reflexivity.
    rewrite Eq84. ring. }
  assert (EnR : ((Qd * Qd)
                 * lw0_q_of_nat (5 * (2*j+2) * (2*j+3) * (2*n+2*j+3) * (2*n+2*j+4)))%Q ==
                (lw0_q_of_nat (2*j+2) * lw0_q_of_nat (2*j+3) * lw0_q_of_nat (2*n+2*j+3)
                 * lw0_q_of_nat (2*n+2*j+4) * (Qd * Qd) * (5 # 1))%Q).
  { rewrite !leibsep_qnat_mul.
    assert (Eq5 : lw0_q_of_nat 5 == (5 # 1)) by reflexivity.
    rewrite Eq5. ring. }
  apply (qleT'_trans
          (q * q * lw0_q_of_nat (n + 2*j+2) * lw0_q_of_nat (n + 2*j+3) * (84 # 1))
          ((q * q) * lw0_q_of_nat (84 * (n + 2*j+2) * (n+2*j+3)))).
  - apply qeq_leT'. exact EnL.
  - apply (qleT'_trans _
            ((Qd * Qd)
             * lw0_q_of_nat (5 * (2*j+2) * (2*j+3) * (2*n+2*j+3) * (2*n+2*j+4)))).
    + exact Hcomb.
    + apply qeq_leT'. exact EnR.
Qed.

(* G4b·件一 率界 slack 版（基线 lw0_Wb_ratio_bound :1614 差分改写）。 *)
Lemma leibsep_Wb_ratio_bound_slack : forall (b q d : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (Datatypes.S j))
        (lw0_Wb b q n j * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))%Q.
Proof.
  intros b q d n j Hb0 Hq Hband Hn.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (HQd : QleT' 0 (10 / 3 + d)%Q)
    by (apply (qleT'_trans (0 # 1) q); assumption).
  assert (HQd2 : QleT' 0 ((10 / 3 + d) * (10 / 3 + d))%Q).
  { apply (qleT'_trans (0 # 1) (0 * (10 / 3 + d))%Q).
    - apply qeq_leT'. ring.
    - apply (lw0_qcompat_r); [exact HQd | exact HQd]. }
  assert (HRho0 : QleT' 0 (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))).
  { apply (qleT'_trans (0 # 1) (0 * Qinv (84 # 1))).
    - apply qeq_leT'. ring.
    - apply (lw0_qcompat_r (0 # 1) ((10 / 3 + d) * (10 / 3 + d) * (5 # 1))
               (Qinv (84 # 1))).
      + apply (qleT'_trans (0 # 1) (0 * (5 # 1))).
        * apply qeq_leT'. ring.
        * apply (lw0_qcompat_r (0 # 1) ((10 / 3 + d) * (10 / 3 + d)) (5 # 1)).
          -- exact HQd2.
          -- apply Qle_to_QleT'. apply Qlt_le_weak. exact leibsep_qlt_5.
      + apply Qle_to_QleT'. apply Qlt_le_weak. apply Qinv_lt_0_compat.
        exact leibsep_qlt_84. }
  assert (Hden : QltT 0 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply qmult_ltT_0_compat.
      + apply qmult_ltT_0_compat; apply lw0_q_of_nat_lt0T;
          [ apply leibsep_nat_pos2 | apply leibsep_nat_pos3 ].
      + apply lw0_q_of_nat_lt0T. apply leibsep_nat_pos23.
    - apply QltT_to_Qlt. apply lw0_q_of_nat_lt0T. apply leibsep_nat_pos24. }
  assert (Hnnqq : QleT' 0 (q * q)).
  { apply Qle_to_QleT'. apply Qlt_le_weak.
    apply Qmult_lt_0_compat; apply QltT_to_Qlt; exact Hq. }
  assert (Hnum0 : QleT' 0 ((q * q * lw0_q_of_nat (n + 2*j + 2))
                           * lw0_q_of_nat (n + 2*j + 3))).
  { apply (qleT'_trans (0 # 1) (0 * lw0_q_of_nat (n + 2*j + 3))).
    - apply qeq_leT'. ring.
    - apply (lw0_qcompat_r).
      + apply (qleT'_trans (0 # 1) (0 * lw0_q_of_nat (n + 2*j + 2))).
        * apply qeq_leT'. ring.
        * apply (lw0_qcompat_r); [exact Hnnqq | apply lw0_q_of_nat_nonneg].
      + apply lw0_q_of_nat_nonneg. }
  assert (Hratio0 : QleT' 0 (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)
                       / (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                          lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))).
  { apply (qleT'_trans (0 # 1)
            (0 * Qinv (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                       lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))).
    - apply qeq_leT'. ring.
    - apply (lw0_qcompat_r).
      + exact Hnum0.
      + apply Qle_to_QleT'. apply Qlt_le_weak. apply Qinv_lt_0_compat.
        apply QltT_to_Qlt. exact Hden. }
  apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j))
          (lw0_Wb b q n j *
           (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)
            / (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
               lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))).
  - apply qeq_leT'. apply (lw0_Wb_ratio_eq b q n j).
  - apply (qleT'_trans
            (lw0_Wb b q n j *
             (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)
              / (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                 lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))
            (lw0_Wb b q n j *
             (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))).
    + apply (lw0_qcompat_l
              (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)
               / (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                  lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))
              (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
              (lw0_Wb b q n j)).
      * apply (lw0_frac_le
                 (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
                 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                  lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))
                 (((10 / 3 + d) * (10 / 3 + d)) * (5 # 1)) (84 # 1)).
        -- exact Hden.
        -- apply Qlt_to_QltT. exact leibsep_qlt_84.
        -- apply (qleT'_trans
                   (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)
                    * (84 # 1))
                   (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                    lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) *
                    ((10 / 3 + d) * (10 / 3 + d)) * (5 # 1))
                   (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                    lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) *
                    (((10 / 3 + d) * (10 / 3 + d)) * (5 # 1)))).
           ++ apply (leibsep_Wb_cross q (10 / 3 + d)%Q n j Hq Hband Hn).
           ++ apply qeq_leT'. ring.
      * exact (lw0_Wb_nonneg b q n j Hb0 Hq0).
      * exact Hratio0.
    + apply qeq_leT'. reflexivity.
Qed.

(* G4b·件二 首对严格 slack 版（基线 lw0_Wb_lt01 :1704；ρ < 1 显式前提）。 *)
Lemma leibsep_Wb_lt01_slack : forall (b q d : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  QltT (lw0_Wb b q n 1) (lw0_Wb b q n 0).
Proof.
  intros b q d n Hb0 Hq Hband Hn Hrho1.
  apply Qlt_to_QltT.
  assert (Hb : QleT' (lw0_Wb b q n 1)
                     (lw0_Wb b q n 0 * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))))
    by (apply leibsep_Wb_ratio_bound_slack;
        [apply lw0_QltT_le; exact Hb0 | exact Hq | exact Hband | exact Hn]).
  assert (HW0pos : Qlt 0 (lw0_Wb b q n 0))
    by (apply QltT_to_Qlt; apply lw0_Wb_pos; assumption).
  assert (Hlt : Qlt (lw0_Wb b q n 0 * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
                    (lw0_Wb b q n 0))
    by (apply lw0_mul_lt_one; [exact HW0pos | apply QltT_to_Qlt; exact Hrho1]).
  apply (Qle_lt_trans (lw0_Wb b q n 1)
          (lw0_Wb b q n 0 * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
          (lw0_Wb b q n 0)).
  - apply QleT'_to_Qle. exact Hb.
  - exact Hlt.
Qed.

(* G4b·件三 逐项严格递减 slack 版（基线 lw0_Wb_seq_dec_strict）。 *)
Lemma leibsep_Wb_seq_dec_strict_slack : forall (b q d : Q) (n j : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  QltT (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j).
Proof.
  intros b q d n j Hb0 Hq Hband Hn Hrho1.
  apply Qlt_to_QltT.
  assert (Hb : QleT' (lw0_Wb b q n (Datatypes.S j))
                     (lw0_Wb b q n j * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))))
    by (apply leibsep_Wb_ratio_bound_slack;
        [apply lw0_QltT_le; exact Hb0 | exact Hq | exact Hband | exact Hn]).
  assert (HWjpos : Qlt 0 (lw0_Wb b q n j))
    by (apply QltT_to_Qlt; apply lw0_Wb_pos; assumption).
  assert (Hlt : Qlt (lw0_Wb b q n j * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
                    (lw0_Wb b q n j))
    by (apply lw0_mul_lt_one; [exact HWjpos | apply QltT_to_Qlt; exact Hrho1]).
  apply (Qle_lt_trans (lw0_Wb b q n (Datatypes.S j))
          (lw0_Wb b q n j * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
          (lw0_Wb b q n j)).
  - apply QleT'_to_Qle. exact Hb.
  - exact Hlt.
Qed.

(* ============================================================ *)
(* §7 缺口 G4a：pin 松量件（550 正本 §三 段 C.1；555 移交清单第 2 项）    *)
(*   Niven 链端值 slack 化的定量核：sin/cos 部分和对位移 q−p 的逐点       *)
(*   Lipschitz——基线 lw0_pi_pin_sin_zero :9814／_cos_neg_one :9825 的     *)
(*   eq 端值，slack 化所需的 |sin q − sin p| ≤ |q−p|·Σ B^{2j}/(2j)! 与    *)
(*   cos 对应族，逐项差分界取自 S10 sc_sin_term_diff :1854／               *)
(*   sc_cos_term_diff :1907（批 2 轮 2 在盘件），本件求和组装。常数       *)
(*   leibsep_abssum/_cos 系显式可算 Fixpoint（vm_compute 实例核对位）。   *)
(*   取用接口注记：sin_partial/cos_partial 即 cauchy_real_sin/cos 投影    *)
(*   （S10 :2420/:2426 投影件），Niven 链（G4c/S4）在 n_sel 处实例化。    *)
(* ============================================================ *)

Fixpoint leibsep_abssum (B : Q) (n : nat) : Q :=
  match n with
  | 0%nat => q_pow B (2 * 0)%nat / q_fact (2 * 0)%nat
  | Datatypes.S m => leibsep_abssum B m
                     + (q_pow B (2 * Datatypes.S m)%nat / q_fact (2 * Datatypes.S m)%nat)
  end.

Fixpoint leibsep_abssum_cos (B : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => leibsep_abssum_cos B m
                     + (q_pow B (Datatypes.S (2 * m))%nat / q_fact (Datatypes.S (2 * m))%nat)
  end.

(* G4a·件一 sin 部分和逐点 Lipschitz（pin 松量核·正弦面）。 *)
Lemma leibsep_sin_partial_lipschitz : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sin_partial n x - sin_partial n y))
        (Qabs (x - y) * leibsep_abssum B n)%Q.
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HB) as HB'.
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hy) as Hy'.
  induction n as [| n IH].
  - simpl. apply (sc_sin_term_diff x y B 0); assumption.
  - simpl sin_partial. simpl leibsep_abssum.
    apply (Qle_trans _ (Qabs (sin_partial n x - sin_partial n y)
                        + Qabs (sin_term (Datatypes.S n) x
                                - sin_term (Datatypes.S n) y))).
    + assert (Halg : (Qabs ((sin_partial n x + sin_term (Datatypes.S n) x)
                            - (sin_partial n y + sin_term (Datatypes.S n) y)))%Q ==
                     (Qabs ((sin_partial n x - sin_partial n y)
                            + (sin_term (Datatypes.S n) x
                               - sin_term (Datatypes.S n) y)))%Q)
        by (apply Qabs_wd; ring).
      rewrite Halg. apply Qabs_triangle.
    + assert (Heq : (Qabs (x - y) * leibsep_abssum B (Datatypes.S n))%Q ==
                    (Qabs (x - y) * leibsep_abssum B n
                     + Qabs (x - y)
                       * (q_pow B (2 * Datatypes.S n) / q_fact (2 * Datatypes.S n)))%Q)
        by (simpl; ring).
      rewrite Heq. apply Qplus_le_compat.
      * exact IH.
      * apply (sc_sin_term_diff x y B (Datatypes.S n)); assumption.
Qed.

(* G4a·件二 cos 部分和逐点 Lipschitz（pin 松量核·余弦面，端值 −1 松量化）。 *)
Lemma leibsep_cos_partial_lipschitz : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (cos_partial n x - cos_partial n y))
        (Qabs (x - y) * leibsep_abssum_cos B n)%Q.
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HB) as HB'.
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hy) as Hy'.
  induction n as [| n IH].
  - simpl leibsep_abssum_cos.
    assert (Hz : cos_term 0 x - cos_term 0 y == 0)
      by (unfold cos_term; simpl; ring).
    rewrite Hz. rewrite Qmult_0_r. apply Qle_refl.
  - simpl cos_partial. simpl leibsep_abssum_cos.
    apply (Qle_trans _ (Qabs (cos_partial n x - cos_partial n y)
                        + Qabs (cos_term (Datatypes.S n) x
                                - cos_term (Datatypes.S n) y))).
    + assert (Halg : (Qabs ((cos_partial n x + cos_term (Datatypes.S n) x)
                            - (cos_partial n y + cos_term (Datatypes.S n) y)))%Q ==
                     (Qabs ((cos_partial n x - cos_partial n y)
                            + (cos_term (Datatypes.S n) x
                               - cos_term (Datatypes.S n) y)))%Q)
        by (apply Qabs_wd; ring).
      rewrite Halg. apply Qabs_triangle.
    + assert (Heq : (Qabs (x - y) * leibsep_abssum_cos B (Datatypes.S n))%Q ==
                    (Qabs (x - y) * leibsep_abssum_cos B n
                     + Qabs (x - y)
                       * (q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))))%Q)
        by (simpl; ring).
      rewrite Heq. apply Qplus_le_compat.
      * exact IH.
      * apply (sc_cos_term_diff x y B n); assumption.
Qed.

(* 出口核对 *)
Check leibsep_gate_open_true.
Check leibsep_q_kernel_guarded.
Check leibsep_piL_metric_proj.
Check leibsep_metric_pi_transport.
Check leibsep_pi_sep_alpha_guarded.
Check leibsep_qabs_le_two.
Check leibsep_q_band.
Check leibsep_q_band_upper_QleT'.
Check leibsep_q_band_pos.
Check leibsep_metric_band_of_window.
Check leibsep_qnat_mul.
Check leibsep_Wb_poly_nat.
Check leibsep_Wb_cross.
Check leibsep_Wb_ratio_bound_slack.
Check leibsep_Wb_lt01_slack.
Check leibsep_Wb_seq_dec_strict_slack.
Check leibsep_abssum.
Check leibsep_abssum_cos.
Check leibsep_sin_partial_lipschitz.
Check leibsep_cos_partial_lipschitz.

(* 件尾 Print Assumptions（G4 关：闭合件全 Closed——承窗件 §12 面） *)
Print Assumptions leibsep_gate_open_true.
Print Assumptions leibsep_qabs_low.
Print Assumptions leibsep_q_kernel_guarded.
Print Assumptions leibsep_piL_metric_proj.
Print Assumptions leibsep_metric_pi_transport.
Print Assumptions leibsep_pi_sep_alpha_guarded.
Print Assumptions leibsep_gate_sample_zero.
Print Assumptions leibsep_gate_sample_three.
Print Assumptions leibsep_qabs_le_two.
Print Assumptions leibsep_q_band.
Print Assumptions leibsep_q_band_upper_QleT'.
Print Assumptions leibsep_q_band_pos.
Print Assumptions leibsep_metric_band_of_window.
Print Assumptions leibsep_qnat_mul.
Print Assumptions leibsep_Wb_poly_nat.
Print Assumptions leibsep_Wb_cross.
Print Assumptions leibsep_Wb_ratio_bound_slack.
Print Assumptions leibsep_Wb_lt01_slack.
Print Assumptions leibsep_Wb_seq_dec_strict_slack.
Print Assumptions leibsep_sin_partial_lipschitz.
Print Assumptions leibsep_cos_partial_lipschitz.

(* ============================================================ *)
(* §8 缺口 G4b-vanish ＋ 缺口 G4c：IBP 望远镜松量（550 正本 §三 段 C.3；  *)
(*   561 交接清单三增量全数用上）。勘形账（主件在盘供件，行号实测）：       *)
(*   lw0_geom_lin_lb :1743（Bernoulli 线性下界 c^j ≥ 1+j(c−1)）；          *)
(*   lw0_Wb_vanish :2320（eq 版消逝全配方：率 25/27 上取整见证＋倒数     *)
(*   比较 lw0_inv_le :1301＋阈值乘-through Qmult_lt_compat_r）；          *)
(*   lw0_altseq_rem_le :1932（泛 W 交错余项双侧窗｜acc ≤ W m）；          *)
(*   lw0_altseq_cauchy :1955（vanish 显式假设槽＝G4b-vanish 供件位）；    *)
(*   lw0_pitB_pair_telescope :10010（零前提 IBP 望远镜恒等）；            *)
(*   lw0_pitB_pair_rtail_vanish :13462（零 π 前提尾项消逝）；             *)
(*   S03 q_arch_geom :405（Set 层阿基米德——免 Qround 上取整）。           *)
(*   G4b-vanish＝0<ρ(d)<1 几何衰减见证泛形（率 25/27 换 ρ(d) :=           *)
(*   (10/3+d)²·5/84，d < √(84/5)−10/3 ≈ 1.094 时 ρ<1，引擎 δ=2eN+2c0→0   *)
(*   远在内——561 注记）。G4c＝逐项松量递推（W(j+k) ≤ W(j)·ρ^k，     *)
(*   分部积分递推的 Q 层显式形态）→ 望远镜求和闭合（Q 层有限和交错余    *)
(*   项双侧窗）→ G4c 主件＝GAPASUME 假设位 :9788-9792 的松量版定理：    *)
(*   端点修正项 |F(q)|·t + |F′(q)|·s 与零前提尾项窗进挤压——eq 版需       *)
(*   sin q=0／cos q=−1（π 前提），松量版以 s/t 显式槽承载端点松量        *)
(*   （S5 由 G4a Lipschitz＋度量带在 n_sel 处实例化），假设位自此消为    *)
(*   定理。响应亮声明：s/t 槽系可判定分支内假设形，非语句前提            *)
(*   （550 §六.4 口径）。                                                  *)
(* ============================================================ *)

(* 工具件·甲：Qabs 三项三角（G4c 主件三点不等式的泛形核）。 *)
Lemma leibsep_abs3_split : forall A B C : Q,
  QleT' (Qabs (A + B + C)) (Qabs A + Qabs B + Qabs C).
Proof.
  intros A B C. apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs A + Qabs (B + C))).
  - setoid_replace (A + B + C) with (A + (B + C)) by ring.
    apply Qabs_triangle.
  - setoid_replace (Qabs A + Qabs B + Qabs C)
      with (Qabs A + (Qabs B + Qabs C)) by ring.
    apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qabs_triangle.
Qed.

(* 工具件·乙：率 ρ(d) := (10/3+d)²·5/84 的非负／正性（561 件 9 证内     *)
(*   HRho0/HRho 段提件泛化——sq 面按 10/3+d 符号两支）。 *)
Lemma leibsep_rho_nonneg : forall d : Q,
  QleT' 0 (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))%Q.
Proof.
  intros d.
  assert (Hsq : QleT' 0 ((10 / 3 + d) * (10 / 3 + d))%Q).
  { destruct (Qlt_le_dec (10 / 3 + d) 0) as [Hn | Hp].
    - assert (H0 : QleT' (10 / 3 + d) 0)
        by (apply Qle_to_QleT'; apply Qlt_le_weak; exact Hn).
      assert (Hneg : QleT' 0 (-(10 / 3 + d))%Q).
      { pose proof (lw0_opp_le_swap (10 / 3 + d) 0 H0) as Hsw.
        apply (qleT'_trans 0 (- 0)%Q (-(10 / 3 + d))).
        + apply qeq_leT'. ring.
        + exact Hsw. }
      apply (qleT'_trans (0 # 1) (-(10 / 3 + d) * -(10 / 3 + d))%Q
                         ((10 / 3 + d) * (10 / 3 + d))%Q).
      + apply (lw0_qmul_le0T _ _ Hneg Hneg).
      + apply qeq_leT'. ring.
    - assert (Hpos : QleT' 0 (10 / 3 + d))
        by (apply Qle_to_QleT'; exact Hp).
      apply (lw0_qmul_le0T _ _ Hpos Hpos). }
  assert (Hfrac : QleT' 0 ((5 # 1) / (84 # 1))%Q).
  { apply Qle_to_QleT'. apply Qlt_le_weak. unfold Qdiv.
    apply Qmult_lt_0_compat.
    - exact leibsep_qlt_5.
    - apply Qinv_lt_0_compat. exact leibsep_qlt_84. }
  assert (Hrho0 : QleT' 0 (((10 / 3 + d) * (10 / 3 + d))%Q
                           * ((5 # 1) / (84 # 1))%Q))
    by exact (lw0_qmul_le0T _ _ Hsq Hfrac).
  apply (qleT'_trans (0 # 1) _ _ Hrho0).
  apply qeq_leT'. unfold Qdiv. apply Qmult_assoc.
Qed.

Lemma leibsep_rho_pos : forall d : Q, QltT 0 (10 / 3 + d)%Q ->
  QltT 0 (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))%Q.
Proof.
  intros d Hd. apply Qlt_to_QltT. unfold Qdiv. apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; apply QltT_to_Qlt; exact Hd.
    + exact leibsep_qlt_5.
  - apply Qinv_lt_0_compat. exact leibsep_qlt_84.
Qed.

(* 工具件·丙：q_pow 互倒恒等（lw0_Wb_vanish :2327 Hpowinv 的泛形提件）。 *)
Lemma leibsep_qpow_recip_mul : forall (x : Q) (k : nat),
  ~ (x == 0)%Q -> q_pow x k * q_pow (Qinv x) k == 1%Q.
Proof.
  intros x k Hx.
  rewrite (lw0_q_pow_mult x (Qinv x) k).
  assert (E : x * Qinv x == 1%Q) by (apply Qmult_inv_r; exact Hx).
  rewrite E. apply lw0_q_pow_one.
Qed.

(* G4b-vanish·核心：泛几何衰减见证（0<ρ<1，C ≥ 0，eps>0 ⟹ ∃N ∀j≥N，  *)
(*   C·ρ^j < eps）。lw0_Wb_vanish 配方泛化：率 25/27 换任意 ρ；上取整   *)
(*   见证换 S03 q_arch_geom（Set 层阿基米德，免 Qround）；倒数比较沿    *)
(*   lw0_inv_le；阈值乘-through 沿 Qmult_lt_compat_r＋lw0_div_lt。       *)
Lemma leibsep_geom_pow_vanish : forall (rho C eps : Q),
  QltT 0 rho -> QltT rho 1 -> QleT' 0 C -> QltT 0 eps ->
  sigT (fun N : nat => forall j : nat, (N <= j)%nat -> QltT (C * q_pow rho j) eps).
Proof.
  intros rho C eps Hr0 Hr1 HC0 Heps.
  assert (Hr0ne : ~ (rho == 0)%Q)
    by (intro Hc; exact (qltT_not_eq_zero rho Hr0 Hc)).
  assert (Hr1le : QleT' rho 1)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hr1).
  assert (Hinvpos : Qlt 0 (Qinv rho))
    by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; exact Hr0).
  assert (H01 : QltT 0 1) by (apply Qlt_to_QltT; exact leibsep_qlt_1).
  assert (Hc1 : QleT' 1 (Qinv rho)).
  { apply (qleT'_trans 1 (/ 1)%Q (Qinv rho)).
    - apply qeq_leT'. reflexivity.
    - exact (lw0_inv_le rho 1 Hr0 H01 Hr1le). }
  assert (Hc1lt : Qlt 1 (Qinv rho)).
  { pose proof (Qmult_lt_compat_r rho 1 (Qinv rho) Hinvpos
                  (QltT_to_Qlt _ _ Hr1)) as H.
    assert (E : rho * Qinv rho == 1%Q) by (apply Qmult_inv_r; exact Hr0ne).
    rewrite E in H. rewrite (Qmult_1_l (Qinv rho)) in H.
    exact H. }
  assert (Hcm1pos : QltT 0 (Qinv rho - 1)%Q)
    by (apply Qlt_to_QltT; exact (leibsep_qlt_minus _ _ Hc1lt)).
  assert (Hr1m : QltT 0 (1 - rho)%Q)
    by (apply Qlt_to_QltT;
        exact (leibsep_qlt_minus _ _ (QltT_to_Qlt _ _ Hr1))).
  assert (Hjnat : forall j' : nat, QltT 0 (lw0_q_of_nat (Datatypes.S j')))
    by (intros j'; apply lw0_q_of_nat_lt0T_S).
  assert (Hjq : forall j' : nat,
            QltT 0 (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))%Q).
  { intros j'; apply qmult_ltT_0_compat; [ apply Hjnat | exact Hcm1pos ]. }
  assert (Hcpos : forall j' : nat,
            QltT 0 (q_pow (Qinv rho) (Datatypes.S j'))).
  { intros j'; apply lw0_q_pow_pos; apply Qlt_to_QltT; exact Hinvpos. }
  assert (HD0 : QltT 0 ((1 - rho) * eps)%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat;
      [ apply QltT_to_Qlt; exact Hr1m | apply QltT_to_Qlt; exact Heps ]. }
  assert (HDne : ~ ((1 - rho) * eps == 0)%Q)
    by (intro Hc; exact (qltT_not_eq_zero ((1 - rho) * eps) HD0 Hc)).
  destruct (q_arch_geom (C * rho * Qinv ((1 - rho) * eps)%Q)) as [N0 HN0].
  exists (Datatypes.S N0)%nat. intros j Hj.
  destruct j as [| j']; [ destruct (Nat.nle_succ_0 N0 Hj) | ].
  assert (HjN : NatLe N0 j').
  { apply NatLe_lift. exact (proj2 (Nat.succ_le_mono N0 j') Hj). }
  specialize (HN0 j' HjN).
  assert (Ej : (j' + 1)%nat = Datatypes.S j') by (apply Nat.add_1_r).
  rewrite Ej in HN0.
  (* HN0 : QleT' (2·A) (j#1)，A := C·ρ·/D，D := (1−ρ)·eps *)
  assert (HN0a : QleT' (2 * (C * rho * Qinv ((1 - rho) * eps)))%Q
                       (lw0_q_of_nat (Datatypes.S j'))).
  { apply (qleT'_trans (2 * (C * rho * Qinv ((1 - rho) * eps)))
                       (Qmult (1 + 1)%Q (C * rho * Qinv ((1 - rho) * eps)))).
    - apply qeq_leT'. ring.
    - exact HN0. }
  assert (HD1 : QltT 0 (lw0_q_of_nat (Datatypes.S j') * (1 - rho))%Q).
  { apply qmult_ltT_0_compat; [ apply Hjnat | exact Hr1m ]. }
  assert (HeJp : QltT 0 (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))%Q).
  { apply qmult_ltT_0_compat; [ exact Heps | exact HD1 ]. }
  (* 乘-through：2·A·D == 2·C·ρ ⟹ 2·C·ρ ≤ j·D *)
  assert (HE1 : (2 * (C * rho * Qinv ((1 - rho) * eps))
                 * ((1 - rho) * eps))%Q == (2 * (C * rho))%Q).
  { rewrite <- (Qmult_assoc 2 (C * rho * Qinv ((1 - rho) * eps))
                             ((1 - rho) * eps)).
    rewrite <- (Qmult_assoc (C * rho) (Qinv ((1 - rho) * eps))
                         ((1 - rho) * eps)).
    rewrite (Qmult_comm (Qinv ((1 - rho) * eps)) ((1 - rho) * eps)).
    rewrite (Qmult_inv_r ((1 - rho) * eps) HDne). ring. }
  assert (HN2 : Qle (2 * (C * rho))%Q
                    (lw0_q_of_nat (Datatypes.S j') * ((1 - rho) * eps))%Q).
  { apply QleT'_to_Qle in HN0a.
    apply (Qle_trans _
            ((2 * (C * rho * Qinv ((1 - rho) * eps)) * ((1 - rho) * eps))%Q)).
    - rewrite <- HE1. apply Qle_refl.
    - apply Qmult_le_compat_r; [ exact HN0a
                               | apply Qlt_le_weak; apply QltT_to_Qlt
                               ; exact HD0 ]. }
  assert (HN3 : QleT' (2 * (C * rho))
                      (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))%Q).
  { apply (qleT'_trans (2 * (C * rho))
                       (lw0_q_of_nat (Datatypes.S j') * ((1 - rho) * eps))%Q).
    - apply Qle_to_QleT'. exact HN2.
    - apply qeq_leT'. ring. }
  (* 半阈值：C·ρ ≤ (1/2)·j·D < j·D *)
  assert (Hhalf : QleT' (C * rho)
                        ((1 # 2) * (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))))%Q).
  { apply (qleT'_trans (C * rho)
                       ((1 # 2) * (2 * (C * rho)))
                       ((1 # 2) * (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))))).
    - apply qeq_leT'. ring.
    - apply (lw0_qcompat_l (2 * (C * rho))
                           (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))
                           (1 # 2)).
      + exact HN3.
      + apply Qle_to_QleT'. exact leibsep_qle_half.
      + apply Qle_to_QleT'. apply Qmult_le_0_compat;
          [ exact leibsep_qle_half
          | apply Qmult_le_0_compat;
            [ exact (QleT'_to_Qle _ _ HC0)
            | apply QleT'_to_Qle; apply lw0_QltT_le; exact Hr0 ] ]. }
  assert (Hhalf2 : QltT ((1 # 2) * (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))))
                        (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))).
  { assert (Hm : Qlt ((eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))) * (1 # 2))
                     (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))))
      by (apply lw0_mul_lt_one;
            [ apply QltT_to_Qlt; exact HeJp | exact leibsep_qlt_half_1 ]).
    apply (lw0_leT'_ltT_trans _
            ((eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))) * (1 # 2))
            (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))).
    - apply qeq_leT'. ring.
    - apply Qlt_to_QltT. exact Hm. }
  assert (Hlt : QltT (C * rho)
                     (eps * (lw0_q_of_nat (Datatypes.S j') * (1 - rho))))
    by exact (lw0_leT'_ltT_trans _ _ _ Hhalf Hhalf2).
  (* 上界链：ρ^k == /c^k ≤ /(j·(c−1)) == ρ·/j(1−ρ)；c−1 与 ρ 的互倒代换 *)
  assert (kA : ((Qinv rho - 1) * rho == 1 - rho)%Q).
  { change (((Qinv rho + Qopp 1) * rho) == (1 + Qopp rho))%Q.
    rewrite Qmult_plus_distr_l.
    rewrite (Qmult_comm (Qinv rho) rho).
    rewrite (Qmult_inv_r rho Hr0ne).
    ring. }
  assert (Hrecip : q_pow (Qinv rho) (Datatypes.S j') * q_pow rho (Datatypes.S j') == 1%Q).
  { pose proof (leibsep_qpow_recip_mul (Qinv rho) (Datatypes.S j')) as HR.
    assert (Hne : ~ (Qinv rho == 0)%Q)
      by (intro Hc; apply Hr0ne; rewrite <- (Qinv_involutive rho); rewrite Hc; reflexivity).
    specialize (HR Hne).
    rewrite (Qinv_involutive rho) in HR. exact HR. }
  assert (HPne : ~ (q_pow (Qinv rho) (Datatypes.S j') == 0)%Q)
    by (intro Hc; exact (qltT_not_eq_zero _ (Hcpos j') Hc)).
  assert (EP : (q_pow rho (Datatypes.S j')
               == Qinv (q_pow (Qinv rho) (Datatypes.S j')))%Q).
  { apply (Qeq_trans _
            (q_pow rho (Datatypes.S j')
             * (q_pow (Qinv rho) (Datatypes.S j')
                * Qinv (q_pow (Qinv rho) (Datatypes.S j'))))).
    - rewrite (Qmult_inv_r (q_pow (Qinv rho) (Datatypes.S j')) HPne). ring.
    - rewrite Qmult_assoc.
      rewrite (Qmult_comm (q_pow rho (Datatypes.S j'))
                          (q_pow (Qinv rho) (Datatypes.S j'))).
      rewrite Hrecip. ring. }
  assert (Hlow : QleT' (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))
                       (q_pow (Qinv rho) (Datatypes.S j'))).
  { apply (qleT'_trans (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))
                       (1 + lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))
                       (q_pow (Qinv rho) (Datatypes.S j'))).
    - apply Qle_to_QleT'.
      apply (leibsep_qle_of_minus _
               (1 + lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))%Q).
      assert (E : ((1 + lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))
                   - lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))%Q
                  == (1 # 1)) by ring.
      rewrite E. exact leibsep_qle_one.
    - exact (lw0_geom_lin_lb (Qinv rho) (Datatypes.S j') Hc1). }
  assert (Hinv2 : QleT' (Qinv (q_pow (Qinv rho) (Datatypes.S j')))
                        (Qinv (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))))
    by exact (lw0_inv_le _ _ (Hjq j') (Hcpos j') Hlow).
  assert (F2 : (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))%Q
               == (lw0_q_of_nat (Datatypes.S j') * (1 - rho) * Qinv rho)%Q).
  { apply (Qeq_trans _
            ((lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1))
             * (rho * Qinv rho))%Q).
    - rewrite (Qmult_inv_r rho Hr0ne). ring.
    - rewrite <- (Qmult_assoc (lw0_q_of_nat (Datatypes.S j'))
                              (Qinv rho - 1) (rho * Qinv rho)).
      rewrite (Qmult_assoc (Qinv rho - 1) rho (Qinv rho)).
      rewrite kA. ring. }
  assert (Hup2 : QleT' (C * Qinv (q_pow (Qinv rho) (Datatypes.S j')))
                       (C * rho * Qinv (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))).
  { apply (qleT'_trans (C * Qinv (q_pow (Qinv rho) (Datatypes.S j')))
                       (C * Qinv (lw0_q_of_nat (Datatypes.S j') * (Qinv rho - 1)))
                       (C * rho * Qinv (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))).
    - exact (lw0_qcompat_l _ _ C Hinv2 HC0
               (Qle_to_QleT' _ _
                 (Qlt_le_weak _ _
                   (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (Hcpos j')))))).
    - apply qeq_leT'. rewrite F2. rewrite Qinv_mult_distr.
      rewrite (Qinv_involutive rho). ring. }
  apply (lw0_leT'_ltT_trans (C * q_pow rho (Datatypes.S j'))
                            (C * rho * Qinv (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))
                            eps).
  - apply (qleT'_trans (C * q_pow rho (Datatypes.S j'))
                       (C * Qinv (q_pow (Qinv rho) (Datatypes.S j')))
                       (C * rho * Qinv (lw0_q_of_nat (Datatypes.S j') * (1 - rho)))).
    + apply qeq_leT'. rewrite <- EP. reflexivity.
    + exact Hup2.
  - exact (lw0_div_lt (C * rho) eps
            (lw0_q_of_nat (Datatypes.S j') * (1 - rho)) HD1 Hlt).
Qed.

(* G4c·件一 IBP 逐项松量递推：分部积分递推的 Q 层显式形态——k 步 IBP    *)
(*   逐项松量 W(j+k) ≤ W(j)·ρ^k（561 件 9 一步率界的 k 步望远镜化）。    *)
Lemma leibsep_Wb_ibp_pow_slack : forall (b q d : Q) (n j k : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (j + k))
        (lw0_Wb b q n j
         * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) k)%Q.
Proof.
  intros b q d n j k Hb0 Hq Hband Hn.
  induction k as [| k IH].
  - assert (Ek : (j + 0)%nat = j) by (apply Nat.add_0_r). rewrite Ek.
    apply qeq_leT'. cbn [q_pow]. ring.
  - assert (Esk : (j + Datatypes.S k)%nat = Datatypes.S (j + k))
      by (apply Nat.add_succ_r).
    rewrite Esk.
    apply (qleT'_trans
            (lw0_Wb b q n (Datatypes.S (j + k)))
            (lw0_Wb b q n (j + k)
             * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
            (lw0_Wb b q n j
             * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
                     (Datatypes.S k))).
    + exact (leibsep_Wb_ratio_bound_slack b q d n (j + k) Hb0 Hq Hband Hn).
    + apply (qleT'_trans
              (lw0_Wb b q n (j + k)
               * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
              (lw0_Wb b q n j
               * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) k
               * (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
              (lw0_Wb b q n j
               * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
                       (Datatypes.S k))).
      * apply (lw0_qcompat_r _ _ _ IH).
        apply (leibsep_rho_nonneg d).
      * apply qeq_leT'.
        change (q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
                     (Datatypes.S k))
          with ((((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
                * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) k).
        ring.
Qed.

(* G4b-vanish·主件：0<ρ(d)<1 几何衰减见证——lw0_altseq_cauchy :1955      *)
(*   vanish 槽的松量版供件（561 新增移交缺口本件销账）。 *)
Lemma leibsep_Wb_vanish_slack : forall (b q d : Q) (n : nat) (eps : Q),
  QleT' 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  QltT 0 eps ->
  sigT (fun N : nat => forall j : nat, (N <= j)%nat -> QltT (lw0_Wb b q n j) eps).
Proof.
  intros b q d n eps Hb0 Hq Hband Hn Hrho1 Heps.
  assert (Hq0 : QltT 0 (10 / 3 + d)%Q)
    by exact (lw0_ltT_leT_trans 0%Q q (10 / 3 + d)%Q Hq Hband).
  assert (Hr0 : QltT 0 (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)))
    by exact (leibsep_rho_pos d Hq0).
  assert (HW0 : QleT' 0 (lw0_Wb b q n 0))
    by (apply lw0_Wb_nonneg; [ exact Hb0 | apply lw0_QltT_le; exact Hq ]).
  destruct (leibsep_geom_pow_vanish
              (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1))
              (lw0_Wb b q n 0) eps Hr0 Hrho1 HW0 Heps) as [N HN].
  exists N. intros j Hj.
  apply (lw0_leT'_ltT_trans (lw0_Wb b q n j)
            (lw0_Wb b q n 0
             * q_pow (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) j)
            eps).
  - pose proof (leibsep_Wb_ibp_pow_slack b q d n 0 j Hb0 Hq Hband Hn) as HP.
    assert (Ej : (0 + j)%nat = j) by (apply Nat.add_0_l).
    rewrite Ej in HP. exact HP.
  - exact (HN j Hj).
Qed.

(* G4b-vanish·装配：松量 W 族的交错部分和柯西见证——lw0_altseq_cauchy   *)
(*   三槽（非负 lw0_Wb_seq_nonneg／递减 561 件三／消逝本件主件）全数接入。 *)
Lemma leibsep_Wb_altseq_cauchy_slack : forall (b q d : Q) (n : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  cauchy (fun m : nat => altsum (lw0_Wb b q n) m).
Proof.
  intros b q d n Hb0 Hq Hband Hn Hrho1.
  apply (lw0_altseq_cauchy (lw0_Wb b q n)).
  - intros k. exact (lw0_Wb_seq_nonneg b q n k (lw0_QltT_le b Hb0) Hq).
  - intros k. apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt.
    exact (leibsep_Wb_seq_dec_strict_slack b q d n k Hb0 Hq Hband Hn Hrho1).
  - exact (fun eps Heps => leibsep_Wb_vanish_slack b q d n eps
                               (lw0_QltT_le b Hb0) Hq Hband
                               Hn Hrho1 Heps).
Qed.

(* G4c·件二 望远镜求和闭合（Q 层有限和）：交错余项双侧窗——窗件         *)
(*   leiblw_S_pair_abs_t :1611 的 Wb 族松量对应形（泛 lw0_altseq_rem_le  *)
(*   ＋松量递减接入；lw0_altsum_add :1863 拆和）。 *)
Lemma leibsep_telescope_pair_window : forall (b q d : Q) (n m r : nat),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  QleT' (Qabs (altsum (lw0_Wb b q n) (m + r) - altsum (lw0_Wb b q n) m))
        (lw0_Wb b q n m).
Proof.
  intros b q d n m r Hb0 Hq Hband Hn Hrho1.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Eadd : altsum (lw0_Wb b q n) (m + r) ==
                 altsum (lw0_Wb b q n) m
                 + altsum_acc (altsum_sgp m) (lw0_Wb b q n) m r)
    by (apply lw0_altsum_add).
  assert (Ed : (altsum (lw0_Wb b q n) (m + r) - altsum (lw0_Wb b q n) m)%Q ==
               altsum_acc (altsum_sgp m) (lw0_Wb b q n) m r)
    by (rewrite Eadd; ring).
  apply (qleT'_trans
          (Qabs (altsum (lw0_Wb b q n) (m + r) - altsum (lw0_Wb b q n) m))
          (Qabs (altsum_acc (altsum_sgp m) (lw0_Wb b q n) m r))
          (lw0_Wb b q n m)).
  - apply (qeq_leT' _ _ (Qabs_wd _ _ Ed)).
  - exact (lw0_altseq_rem_le (lw0_Wb b q n)
             (fun k => lw0_Wb_seq_nonneg b q n k (lw0_QltT_le b Hb0) Hq)
             (fun k => Qle_to_QleT' _ _ (Qlt_le_weak _ _
               (QltT_to_Qlt _ _
                 (leibsep_Wb_seq_dec_strict_slack b q d n k Hb0 Hq Hband Hn Hrho1))))
             m r).
Qed.

(* G4c·件二·推论：率形消逝窗——N 之后任意有限和段的窗宽全被 eps 压住。 *)
Lemma leibsep_telescope_vanish_window : forall (b q d : Q) (n : nat) (eps : Q),
  QltT 0 b -> QltT 0 q -> QleT' q (10 / 3 + d)%Q -> (2 <= n)%nat ->
  QltT (((10 / 3 + d) * (10 / 3 + d) * (5 # 1)) / (84 # 1)) 1 ->
  QltT 0 eps ->
  sigT (fun N : nat => forall m r : nat, (N <= m)%nat ->
    QltT (Qabs (altsum (lw0_Wb b q n) (m + r) - altsum (lw0_Wb b q n) m)) eps).
Proof.
  intros b q d n eps Hb0 Hq Hband Hn Hrho1 Heps.
  destruct (leibsep_Wb_vanish_slack b q d n eps (lw0_QltT_le b Hb0) Hq Hband
              Hn Hrho1 Heps) as [N HN].
  exists N. intros m r Hm.
  apply (lw0_leT'_ltT_trans
          (Qabs (altsum (lw0_Wb b q n) (m + r) - altsum (lw0_Wb b q n) m))
          (lw0_Wb b q n m) eps).
  - exact (leibsep_telescope_pair_window b q d n m r Hb0 Hq Hband Hn Hrho1).
  - exact (HN m Hm).
Qed.

(* G4c·件三 端点修正项三点不等式（松量版望远镜本体，零前提）：           *)
(*   lw0_pitB_pair_telescope :10010 恒等＋Qabs 三项三角——                *)
(*   |pair(f,σ_m)(q) − K| ≤ |F(q)|·|σ′_m(q)+1| + |F′(q)|·|σ_m(q)| + |尾项|。 *)
Lemma leibsep_pair_slack_bound : forall (q : Q) (n m : nat),
  QleT' (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                           (lw0_sin_qp m) q
                - lw0_K (Qnum q) (Zpos (Qden q)) n))
        (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
         * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
         + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
           * Qabs (qpoly_eval (lw0_sin_qp m) q)
         + Qabs (lw0_pitB_pair_rtail q n m))%Q.
Proof.
  intros q n m.
  pose proof (lw0_pitB_pair_telescope q n m) as HT.
  assert (HE : (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                            (lw0_sin_qp m) q
                - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q
               == ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                   + qpoly_eval (qpoly_deriv
                          (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q
                   + lw0_pitB_pair_rtail q n m)%Q)
    by (rewrite HT; ring).
  apply (qleT'_trans
          (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs ((-1)%Q
                  * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                  * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                 + qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                   * qpoly_eval (lw0_sin_qp m) q
                 + lw0_pitB_pair_rtail q n m))).
  - apply qeq_leT'. apply Qabs_wd. exact HE.
  - apply (qleT'_trans
            (Qabs ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                   + qpoly_eval (qpoly_deriv
                          (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q
                   + lw0_pitB_pair_rtail q n m))
            (Qabs ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * Qabs (qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))).
    + exact (leibsep_abs3_split _ _ _).
    + apply qeq_leT'.
      rewrite (Qabs_Qmult
                ((-1)%Q * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
                (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)).
      rewrite (Qabs_Qmult (-1)%Q
                (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)).
      rewrite (Qabs_Qmult
                (qpoly_eval (qpoly_deriv
                       (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
                (qpoly_eval (lw0_sin_qp m) q)).
      assert (E1 : Qabs (-1)%Q == 1%Q) by reflexivity.
      rewrite E1. ring.
Qed.

(* G4c·主件：GAPASUME 假设位（lw0_pi_transport_Wb_K_ht_gap :9788-9792   *)
(*   第二前提）的松量版定理——eq 版（lw0_pitB_pair_conv_K :13631）需     *)
(*   sin q=0／cos q=−1（π 前提）；松量版以端点松量槽 s/t 显式承载：      *)
(*   ∀eps>0 ∃M ∀m≥M，|pair(f,σ_m)(q) − K| ≤ |F(q)|·t + |F′(q)|·s + eps   *)
(*   （尾项消逝取 lw0_pitB_pair_rtail_vanish :13462 零 π 前提；端点槽    *)
(*   系可判定分支内假设形——550 §六.4 响亮声明口径）。 *)
Lemma leibsep_G4c_pair_slack_window : forall (q : Q) (n : nat) (s t : Q),
  (forall m : nat,
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat,
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QleT' (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)%Q).
Proof.
  intros q n s t Hs Ht eps Heps.
  destruct (lw0_pitB_pair_rtail_vanish q n eps Heps) as [Mt HMt].
  exists Mt. intros m Hm.
  pose proof (leibsep_pair_slack_bound q n m) as HB.
  apply (qleT'_trans
          (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * Qabs (qpoly_eval (lw0_sin_qp m) q)
           + Qabs (lw0_pitB_pair_rtail q n m))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)).
  - exact HB.
  - apply (qleT'_trans
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * Qabs (qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + eps)).
    + apply qleT'_plus_compat.
      * apply qleT'_plus_compat.
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q
                           + (1 # 1)%Q))
                    t
                    (Qabs (qpoly_eval
                             (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)
                             q))
                    (Ht m)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (lw0_sin_qp m) q))
                    s
                    (Qabs (qpoly_eval
                             (qpoly_deriv
                                (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n))
                             q))
                    (Hs m)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
      * apply qleT'_refl.
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt.
        exact (HMt m Hm).
Qed.

(* 出口核对（§8 新件九件＋工具三件） *)
Check leibsep_abs3_split.
Check leibsep_rho_nonneg.
Check leibsep_rho_pos.
Check leibsep_qpow_recip_mul.
Check leibsep_geom_pow_vanish.
Check leibsep_Wb_ibp_pow_slack.
Check leibsep_Wb_vanish_slack.
Check leibsep_Wb_altseq_cauchy_slack.
Check leibsep_telescope_pair_window.
Check leibsep_telescope_vanish_window.
Check leibsep_pair_slack_bound.
Check leibsep_G4c_pair_slack_window.

(* 件尾 Print Assumptions（§8 新件逐发全 Closed 断言） *)
Print Assumptions leibsep_abs3_split.
Print Assumptions leibsep_rho_nonneg.
Print Assumptions leibsep_rho_pos.
Print Assumptions leibsep_qpow_recip_mul.
Print Assumptions leibsep_geom_pow_vanish.
Print Assumptions leibsep_Wb_ibp_pow_slack.
Print Assumptions leibsep_Wb_vanish_slack.
Print Assumptions leibsep_Wb_altseq_cauchy_slack.
Print Assumptions leibsep_telescope_pair_window.
Print Assumptions leibsep_telescope_vanish_window.
Print Assumptions leibsep_pair_slack_bound.
Print Assumptions leibsep_G4c_pair_slack_window.
(* ============================================================ *)
(* §9 600 切片：G4c 尾限制改刀件＋逐点槽供给组（600 切片）        *)
(*   R5 结论【判否·如实】：G4c 原槽形 ∀m 一致界强制 s ≥ |σ₁(q)| ≈ |q|、       *)
(*   t ≥ |σ′₁(q)+1| = 2，而 |F_n(q)|/|F′_n(q)| 随 n 阶乘增长（vm_compute      *)
(*   实证 |F₂(1)| = 11 = 4!/2!−1、|F₂′(1)| = −6；F_n = Σ_k (−1)^k f_n^{(2k)}  *)
(*   首项 f^{(2n)}(q) 系数 (2n)!·(±1)/n! 结构性阶乘增长）——「O(1) 槽值＋超    *)
(*   指数压制」挤压缺口随 n 发散，R5 原路线不可行。改刀正形＝本切片三件：      *)
(*   ① B：G4c 槽改 m ≥ M0 尾限制形（squeeze 只在 m 大处取用槽，slot 界可     *)
(*     取 δ′ 小量——原 :1547 件保持不动（语句面冻结，历史注记位）。           *)
(*   ② C/C′：m ≥ M0 处 |σ_m(q)|/|σ′_m(q)+1| 的尾稳定界（基点值＋尾件），     *)
(*     供件链 lw0_sin_qp_eval :3561／lw0_pitB_conv_sin_tail :7610／          *)
(*     lw0_sin_qp_deriv_eval :3974／lw0_pitB_conv_cos_tail :8191 全 Check     *)
(*     已证（R3：cos 尾件界指数 2*M 非 S(2*M)，非逐字同文，本件按实形取用）。 *)
(*   后续入口（下一棒）：pin 半边（度量带 |π−q| ≤ δ′ ⟹ 槽小量，real 层       *)
(*   sin Lipschitz＋sin_series_real 尾件，勘形窗 S10）＋ F_n 显式阶乘上界件   *)
(*   ＋ δ′/n_sel 协同设计（δ′ ≲ room/|F_n(q)|，n_sel 取 q_fact(n)W₀<1/2）    *)
(*   ＋ β squeeze 组装（K 整数 lw0_K_integer＋lw0_pi_contra_gate 直代）。     *)
(*   预算内禁 lra/lia；命名 leibsep_ 前缀三新件零撞名。                       *)
(* ============================================================ *)

(* ===== B 件：G4c 尾限制改刀（m ≥ M0 槽形；R5 判否后的正形——squeeze 只在 m 大处取用槽） ===== *)
Lemma leibsep_G4c_pair_slack_window_from : forall (q : Q) (n : nat) (s t : Q) (M0 : nat),
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QleT' (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)%Q).
Proof.
  intros q n s t M0 Hs Ht eps Heps.
  destruct (lw0_pitB_pair_rtail_vanish q n eps Heps) as [Mt HMt].
  exists (Nat.max M0 Mt). intros m Hm.
  pose proof (NatLe_drop (Nat.max M0 Mt) m Hm) as Hmax.
  assert (HmM0 : (M0 <= m)%nat).
  { apply (Nat.le_trans M0 (Nat.max M0 Mt) m (Nat.le_max_l M0 Mt) Hmax). }
  assert (HmMt : (Mt <= m)%nat).
  { apply (Nat.le_trans Mt (Nat.max M0 Mt) m (Nat.le_max_r M0 Mt) Hmax). }
  pose proof (leibsep_pair_slack_bound q n m) as HB.
  apply (qleT'_trans
          (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * Qabs (qpoly_eval (lw0_sin_qp m) q)
           + Qabs (lw0_pitB_pair_rtail q n m))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)).
  - exact HB.
  - apply (qleT'_trans
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * Qabs (qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + eps)).
    + apply qleT'_plus_compat.
      * apply qleT'_plus_compat.
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q
                           + (1 # 1)%Q))
                    t
                    (Qabs (qpoly_eval
                             (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)
                             q))
                    (Ht m HmM0)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (lw0_sin_qp m) q))
                    s
                    (Qabs (qpoly_eval
                             (qpoly_deriv
                                (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n))
                             q))
                    (Hs m HmM0)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
      * apply qleT'_refl.
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt.
        exact (HMt m (NatLe_lift _ _ HmMt)).
Qed.

(* ===== C 件：sin_qp 尾稳定（m ≥ M 槽供给核心；lw0_sin_qp_eval :3561 换岸＋:7610 尾件） ===== *)
Lemma leibsep_sin_qp_tail_stable : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q))
        (Qabs (qpoly_eval (lw0_sin_qp M) q)
         + 2 * (q_pow (Qabs q) (Datatypes.S (2 * M))
                / q_fact (Datatypes.S (2 * M)))%Q)%Q.
Proof.
  intros q M D Hr.
  pose proof (lw0_pitB_conv_sin_tail q M D Hr) as Htail.
  assert (Htri : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q))
                       (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                        + Qabs (qpoly_eval (lw0_sin_qp M) q))).
  { apply Qle_to_QleT'.
    assert (Ht2 : Qle (Qabs ((qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                             + qpoly_eval (lw0_sin_qp M) q))
                      (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                             - qpoly_eval (lw0_sin_qp M) q)%Q
                       + Qabs (qpoly_eval (lw0_sin_qp M) q)))
      by apply Qabs_triangle.
    assert (Heq : (qpoly_eval (lw0_sin_qp (M + D)) q
                   - qpoly_eval (lw0_sin_qp M) q)%Q
                  + qpoly_eval (lw0_sin_qp M) q
                  == qpoly_eval (lw0_sin_qp (M + D)) q) by ring.
    rewrite Heq in Ht2. exact Ht2. }
  assert (Hbrg : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q)
                       (Qabs (sin_partial (M + D) q - sin_partial M q))).
  { apply qeq_leT'.
    rewrite (lw0_sin_qp_eval (M + D) q). rewrite (lw0_sin_qp_eval M q).
    reflexivity. }
  assert (Hswap : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                        + Qabs (qpoly_eval (lw0_sin_qp M) q))
                       (Qabs (qpoly_eval (lw0_sin_qp M) q)
                        + Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                               - qpoly_eval (lw0_sin_qp M) q)%Q)).
  { apply qeq_leT'. ring. }
  assert (Hstep : QleT' (Qabs (qpoly_eval (lw0_sin_qp M) q)
                         + Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                                - qpoly_eval (lw0_sin_qp M) q)%Q)
                        (Qabs (qpoly_eval (lw0_sin_qp M) q)
                         + 2 * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                / q_fact (Datatypes.S (2 * M)))%Q)).
  { apply qleT'_plus_compat.
    - apply qleT'_refl.
    - exact (qleT'_trans _ _ _ Hbrg Htail). }
  exact (qleT'_trans _ _ _ Htri (qleT'_trans _ _ _ Hswap Hstep)).
Qed.

(* ===== C' 件：cos_qp_deriv 尾稳定（R3 已证形：cos 尾件界指数 2*M 非 S(2*M)） ===== *)
Lemma leibsep_cos_qp_deriv_tail_stable : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q + (1 # 1)%Q))
        (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q)
         + 2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))%Q)%Q.
Proof.
  intros q M D Hr.
  pose proof (lw0_pitB_conv_cos_tail q M D Hr) as Htail.
  apply (qleT'_trans
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                 - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q
           + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q)
           + 2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))%Q)%Q).
  - apply Qle_to_QleT'.
    assert (Heq2 : Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                         + (1 # 1)%Q)
                   == Qabs ((qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                             - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)
                            + (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                               + (1 # 1)%Q))%Q)
      by (apply Qabs_wd; ring).
    rewrite Heq2. apply Qabs_triangle.
  - assert (Hbrg : QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                              - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q)
                           (Qabs (cos_partial (M + D) q - cos_partial M q))).
    { apply qeq_leT'.
      rewrite (lw0_sin_qp_deriv_eval (M + D) q).
      rewrite (lw0_sin_qp_deriv_eval M q). reflexivity. }
    assert (Hswap : QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                              - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q
                        + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                                + (1 # 1)%Q))
                       (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                              + (1 # 1)%Q)
                        + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                               - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q)).
    { apply qeq_leT'. ring. }
    apply (qleT'_trans _ _ _ Hswap).
    apply qleT'_plus_compat.
    + apply qleT'_refl.
    + exact (qleT'_trans _ _ _ Hbrg Htail).
Qed.

(* 出口核对（600 切片三新件） *)
Check leibsep_G4c_pair_slack_window_from.
Check leibsep_sin_qp_tail_stable.
Check leibsep_cos_qp_deriv_tail_stable.

(* 件尾 Print Assumptions（600 切片三新件逐发全 Closed 断言） *)
Print Assumptions leibsep_G4c_pair_slack_window_from.
Print Assumptions leibsep_sin_qp_tail_stable.
Print Assumptions leibsep_cos_qp_deriv_tail_stable.

(* ============================================================ *)
(* §10 605 切片：pin 半边双槽供给＋交错双岸＋β 挤压矛盾引擎          *)
(*   （S5/S6 汇总第二棒；G4d 挤压闸燃料面；案一/案二激活留下一棒）      *)
(*   定量面注记：leibsep_beta_contra 的 Hup/Hlow 两假设即 600 §三      *)
(*   定量自查公式的引擎侧——δ′/n_sel/N0 的显式选取与 Φ(n,|q|) 显式      *)
(*   阶乘上界件（勘形窗 lw0_qp_ai_abs_bound :4055 窗）为下一棒入口。    *)
(* ============================================================ *)
(* ---------- Abs 自支配两件（K2 双向提取核） ---------- *)

Lemma leibsep_abs_ge_self : forall x : Q, QleT' x (Qabs x).
Proof.
  intros x. apply (Qabs_case x (fun y => QleT' x y)).
  - intros _. apply qleT'_refl.
  - intros Hx0. apply (qleT'_trans x 0%Q (Qopp x)).
    + apply Qle_to_QleT'. exact Hx0.
    + apply (qleT'_trans (Qopp 0)%Q (Qopp x) (Qopp x)).
      * apply lw0_opp_le_swap. apply Qle_to_QleT'. exact Hx0.
      * apply qeq_leT'. ring.
Qed.

Lemma leibsep_abs_ge_opp : forall x : Q, QleT' (Qopp (Qabs x)) x.
Proof.
  intros x. apply (Qabs_case x (fun y => QleT' (Qopp y) x)).
  - intros Hx0. apply (qleT'_trans (Qopp x) (Qopp 0)%Q x).
    + apply lw0_opp_le_swap. apply Qle_to_QleT'. exact Hx0.
    + apply (qleT'_trans (Qopp 0)%Q 0%Q x).
      * apply qeq_leT'. ring.
      * apply Qle_to_QleT'. exact Hx0.
  - intros Hx0. apply qeq_leT'. ring.
Qed.

(* ---------- P1·sin 槽供给：度量带逐点形 → ∀m≥M2 |σ_m(q)| 小量 ---------- *)
Lemma leibsep_sin_slot_from_band : forall (q w : Q) (N M : nat),
  QltT 0 w ->
  (N <= M)%nat ->
  (forall m : nat, (N <= m)%nat ->
     QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) w) ->
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M2 : nat => forall m : nat, (M2 <= m)%nat ->
    QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q))
          (Qabs ((q - projT1 real_pi_geom M2)%Q)
           * leibsep_abssum (Qabs q + w) M2
           + eps
           + 2 * (q_pow (Qabs q) (Datatypes.S (2 * M2))
                  / q_fact (Datatypes.S (2 * M2)))%Q)%Q).
Proof.
  intros q w N M Hw HNM Hband Hratio eps Heps.
  destruct (pi_geom_sin_pi_zero eps Heps) as [N1 HN1].
  exists (Nat.max M N1). intros m Hm.
  assert (HmM2 : (M <= Nat.max M N1)%nat) by apply Nat.le_max_l.
  assert (HmN1 : (N1 <= Nat.max M N1)%nat) by apply Nat.le_max_r.
  assert (HmN : (N <= Nat.max M N1)%nat)
    by exact (Nat.le_trans N M (Nat.max M N1) HNM HmM2).
  pose proof (Hband (Nat.max M N1) HmN) as Hbx.
  assert (HB0 : QleT' 0 (Qabs q + w)%Q).
  { apply (qleT'_trans 0%Q ((0 + 0)%Q) ((Qabs q + w)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply Qle_to_QleT'. apply Qabs_nonneg.
      + apply lw0_QltT_le. exact Hw. }
  assert (HBq : QleT' (Qabs q) (Qabs q + w)%Q).
  { apply (qleT'_trans (Qabs q) ((Qabs q + 0)%Q) ((Qabs q + w)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply qleT'_refl.
      + apply lw0_QltT_le. exact Hw. }
  assert (HBx : QleT' (Qabs (projT1 real_pi_geom (Nat.max M N1)))
                      (Qabs q + w)%Q).
  { apply (qleT'_trans (Qabs (projT1 real_pi_geom (Nat.max M N1)))
                       (Qabs ((projT1 real_pi_geom (Nat.max M N1) - q + q)%Q))
                       ((Qabs q + w)%Q)).
    - apply qeq_leT'. apply Qabs_wd. ring.
    - apply (qleT'_trans
              (Qabs ((projT1 real_pi_geom (Nat.max M N1) - q + q)%Q))
              ((Qabs ((projT1 real_pi_geom (Nat.max M N1) - q)%Q)
                + Qabs q)%Q)
              ((Qabs q + w)%Q)).
      + apply Qle_to_QleT'. apply Qabs_triangle.
      + apply (qleT'_trans
                ((Qabs ((projT1 real_pi_geom (Nat.max M N1) - q)%Q)
                  + Qabs q)%Q)
                ((w + Qabs q)%Q)
                ((Qabs q + w)%Q)).
        * apply qleT'_plus_compat; [exact Hbx | apply qleT'_refl].
        * apply qeq_leT'. ring. }
  assert (Hr2 : forall j : nat, (Nat.max M N1 <= j)%nat ->
    QleT' (2 * q_pow (Qabs q) 2)
          (lw0_q_of_nat (Datatypes.S (2 * j))
           * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { intros j Hj. apply Hratio. exact (Nat.le_trans M (Nat.max M N1) j HmM2 Hj). }
  assert (Hex : sigT (fun D : nat => m = (Nat.max M N1 + D)%nat)).
  { exists (m - Nat.max M N1)%nat. rewrite Nat.add_comm. symmetry.
    apply Nat.sub_add. exact Hm. }
  destruct Hex as [D HD]. subst m.
  apply (qleT'_trans
          (Qabs (qpoly_eval (lw0_sin_qp (Nat.max M N1 + D)) q))
          (Qabs (qpoly_eval (lw0_sin_qp (Nat.max M N1)) q)
           + 2 * (q_pow (Qabs q) (Datatypes.S (2 * Nat.max M N1))
                  / q_fact (Datatypes.S (2 * Nat.max M N1)))%Q)
          (Qabs ((q - projT1 real_pi_geom (Nat.max M N1))%Q)
           * leibsep_abssum (Qabs q + w) (Nat.max M N1)
           + eps
           + 2 * (q_pow (Qabs q) (Datatypes.S (2 * Nat.max M N1))
                  / q_fact (Datatypes.S (2 * Nat.max M N1)))%Q)).
  - exact (leibsep_sin_qp_tail_stable q (Nat.max M N1) D Hr2).
  - apply qleT'_plus_compat.
    + apply (qleT'_trans
              (Qabs (qpoly_eval (lw0_sin_qp (Nat.max M N1)) q))
              (Qabs ((sin_partial (Nat.max M N1) q
                      - sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
               + Qabs (sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))))
              (Qabs ((q - projT1 real_pi_geom (Nat.max M N1))%Q)
               * leibsep_abssum (Qabs q + w) (Nat.max M N1)
               + eps)%Q).
      * apply (qleT'_trans
                (Qabs (qpoly_eval (lw0_sin_qp (Nat.max M N1)) q))
                (Qabs ((sin_partial (Nat.max M N1) q
                        - sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                       + sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
                ((Qabs ((sin_partial (Nat.max M N1) q
                         - sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
                  + Qabs (sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))))%Q)).
        -- apply qeq_leT'.
          assert (HE2 : Qabs (qpoly_eval (lw0_sin_qp (Nat.max M N1)) q)
                        == Qabs ((sin_partial (Nat.max M N1) q
                                  - sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                                 + sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
            by (apply Qabs_wd; rewrite (lw0_sin_qp_eval (Nat.max M N1) q); ring).
          exact HE2.
        -- apply Qle_to_QleT'.
          exact (Qabs_triangle (sin_partial (Nat.max M N1) q
                                - sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                               (sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))).
      * apply Qle_to_QleT'.
        apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _
                    (leibsep_sin_partial_lipschitz q (projT1 real_pi_geom (Nat.max M N1))
                       (Qabs q + w)%Q (Nat.max M N1) HB0 HBq HBx)).
        -- apply Qlt_le_weak.
           apply (leibsep_qlt_wd2
                   (Qabs (projT1 (cauchy_real_sin real_pi_geom) (Nat.max M N1)
                          - projT1 real_zero (Nat.max M N1)))
                   eps
                   (Qabs (sin_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))))
                   eps).
           ++ apply Qabs_wd. rewrite real_sin_proj.
              cbn [projT1 real_zero]. ring.
           ++ apply Qeq_refl.
           ++ apply QltT_to_Qlt.
              exact (HN1 (Nat.max M N1) (NatLe_lift _ _ HmN1)).
    + apply qleT'_refl.
Qed.

(* ---------- P2·cos 槽供给（同构形；R3 实形尾指数 2*M2） ---------- *)
Lemma leibsep_cos_slot_from_band : forall (q w : Q) (N M : nat),
  QltT 0 w ->
  (N <= M)%nat ->
  (forall m : nat, (N <= m)%nat ->
     QleT' (Qabs ((projT1 real_pi_geom m - q)%Q)) w) ->
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M2 : nat => forall m : nat, (M2 <= m)%nat ->
    QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
          (Qabs ((q - projT1 real_pi_geom M2)%Q)
           * leibsep_abssum_cos (Qabs q + w) M2
           + eps
           + 2 * (q_pow (Qabs q) (2 * M2)
                  / q_fact (2 * M2))%Q)%Q).
Proof.
  intros q w N M Hw HNM Hband Hratio eps Heps.
  destruct (pi_geom_cos_pi_neg_one eps Heps) as [N1 HN1].
  exists (Nat.max M N1). intros m Hm.
  assert (HmM2 : (M <= Nat.max M N1)%nat) by apply Nat.le_max_l.
  assert (HmN1 : (N1 <= Nat.max M N1)%nat) by apply Nat.le_max_r.
  assert (HmN : (N <= Nat.max M N1)%nat)
    by exact (Nat.le_trans N M (Nat.max M N1) HNM HmM2).
  pose proof (Hband (Nat.max M N1) HmN) as Hbx.
  assert (HB0 : QleT' 0 (Qabs q + w)%Q).
  { apply (qleT'_trans 0%Q ((0 + 0)%Q) ((Qabs q + w)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply Qle_to_QleT'. apply Qabs_nonneg.
      + apply lw0_QltT_le. exact Hw. }
  assert (HBq : QleT' (Qabs q) (Qabs q + w)%Q).
  { apply (qleT'_trans (Qabs q) ((Qabs q + 0)%Q) ((Qabs q + w)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply qleT'_refl.
      + apply lw0_QltT_le. exact Hw. }
  assert (HBx : QleT' (Qabs (projT1 real_pi_geom (Nat.max M N1)))
                      (Qabs q + w)%Q).
  { apply (qleT'_trans (Qabs (projT1 real_pi_geom (Nat.max M N1)))
                       (Qabs ((projT1 real_pi_geom (Nat.max M N1) - q + q)%Q))
                       ((Qabs q + w)%Q)).
    - apply qeq_leT'. apply Qabs_wd. ring.
    - apply (qleT'_trans
              (Qabs ((projT1 real_pi_geom (Nat.max M N1) - q + q)%Q))
              ((Qabs ((projT1 real_pi_geom (Nat.max M N1) - q)%Q)
                + Qabs q)%Q)
              ((Qabs q + w)%Q)).
      + apply Qle_to_QleT'. apply Qabs_triangle.
      + apply (qleT'_trans
                ((Qabs ((projT1 real_pi_geom (Nat.max M N1) - q)%Q)
                  + Qabs q)%Q)
                ((w + Qabs q)%Q)
                ((Qabs q + w)%Q)).
        * apply qleT'_plus_compat; [exact Hbx | apply qleT'_refl].
        * apply qeq_leT'. ring. }
  assert (Hr2 : forall j : nat, (Nat.max M N1 <= j)%nat ->
    QleT' (2 * q_pow (Qabs q) 2)
          (lw0_q_of_nat (Datatypes.S (2 * j))
           * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { intros j Hj. apply Hratio. exact (Nat.le_trans M (Nat.max M N1) j HmM2 Hj). }
  assert (Hex : sigT (fun D : nat => m = (Nat.max M N1 + D)%nat)).
  { exists (m - Nat.max M N1)%nat. rewrite Nat.add_comm. symmetry.
    apply Nat.sub_add. exact Hm. }
  destruct Hex as [D HD]. subst m.
  apply (qleT'_trans
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max M N1 + D))) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max M N1))) q + (1 # 1)%Q)
           + 2 * (q_pow (Qabs q) (2 * Nat.max M N1)
                  / q_fact (2 * Nat.max M N1))%Q)
          (Qabs ((q - projT1 real_pi_geom (Nat.max M N1))%Q)
           * leibsep_abssum_cos (Qabs q + w) (Nat.max M N1)
           + eps
           + 2 * (q_pow (Qabs q) (2 * Nat.max M N1)
                  / q_fact (2 * Nat.max M N1))%Q)).
  - exact (leibsep_cos_qp_deriv_tail_stable q (Nat.max M N1) D Hr2).
  - apply qleT'_plus_compat.
    + apply (qleT'_trans
              (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max M N1))) q + (1 # 1)%Q))
              (Qabs ((cos_partial (Nat.max M N1) q
                      - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
               + Qabs (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                       + (1 # 1)%Q))
              (Qabs ((q - projT1 real_pi_geom (Nat.max M N1))%Q)
               * leibsep_abssum_cos (Qabs q + w) (Nat.max M N1)
               + eps)%Q).
      * apply (qleT'_trans
                (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max M N1))) q + (1 # 1)%Q))
                (Qabs ((cos_partial (Nat.max M N1) q
                        - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                       + (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                          + (1 # 1)%Q))%Q)
                ((Qabs ((cos_partial (Nat.max M N1) q
                         - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
                  + Qabs (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                          + (1 # 1)%Q))%Q)).
        -- apply qeq_leT'.
          assert (HE2 : Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max M N1))) q
                              + (1 # 1)%Q)
                        == Qabs ((cos_partial (Nat.max M N1) q
                                  - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                                 + (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                                    + (1 # 1)%Q))%Q)
            by (apply Qabs_wd; rewrite (lw0_sin_qp_deriv_eval (Nat.max M N1) q); ring).
          exact HE2.
        -- assert (Htri : Qle (Qabs ((cos_partial (Nat.max M N1) q
                               - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))
                              + (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                                 + (1 # 1)%Q))%Q)
                          (Qabs ((cos_partial (Nat.max M N1) q
                                  - cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1)))%Q)
                           + Qabs (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                                   + (1 # 1)%Q)%Q))
            by apply Qabs_triangle.
          apply Qle_to_QleT'. exact Htri.
      * apply Qle_to_QleT'.
        apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _
                    (leibsep_cos_partial_lipschitz q (projT1 real_pi_geom (Nat.max M N1))
                       (Qabs q + w)%Q (Nat.max M N1) HB0 HBq HBx)).
        -- apply Qlt_le_weak.
           apply (leibsep_qlt_wd2
                   (Qabs (projT1 (cauchy_real_cos real_pi_geom) (Nat.max M N1)
                          - projT1 (real_const (Qopp (1 # 1))%Q) (Nat.max M N1)))
                   eps
                   (Qabs (cos_partial (Nat.max M N1) (projT1 real_pi_geom (Nat.max M N1))
                          + (1 # 1)%Q))
                   eps).
           ++ apply Qabs_wd. rewrite real_cos_proj.
              cbn [projT1 real_const]. ring.
           ++ apply Qeq_refl.
           ++ apply QltT_to_Qlt.
              exact (HN1 (Nat.max M N1) (NatLe_lift _ _ HmN1)).
    + apply qleT'_refl.
Qed.

(* ---------- K1·交错双岸微件 ---------- *)
Lemma leibsep_altsum_two_shore : forall W : nat -> Q,
  (forall k : nat, QleT' 0 (W k)) ->
  (forall k : nat, QleT' (W (Datatypes.S k)) (W k)) ->
  forall m : nat,
    And (QleT' (W 0%nat - W 1%nat)%Q (altsum W (Datatypes.S m)))
        (QleT' (altsum W (Datatypes.S m)) (W 0%nat)).
Proof.
  intros W H0 Hd m.
  pose proof (lw0_altsum_add W 1%nat m) as Hadd.
  assert (Eidx : (1 + m)%nat = Datatypes.S m) by reflexivity.
  rewrite Eidx in Hadd.
  assert (E01 : altsum W 1%nat == W 0%nat)
    by (cbn [altsum altsum_acc altsum_sgp]; now rewrite Qplus_0_r).
  assert (Esgp : altsum_sgp 1%nat = false) by reflexivity.
  rewrite Esgp in Hadd.
  destruct (lw0_acc_quad W H0 Hd m 1%nat) as [Q1 [Q2 [Q3 Q4]]].
  split.
  - apply (qleT'_trans (W 0%nat - W 1%nat)%Q
                       (W 0%nat + Qopp (W 1%nat))%Q
                       (altsum W (Datatypes.S m))).
    + apply qeq_leT'. ring.
    + apply (qleT'_trans (W 0%nat + Qopp (W 1%nat))%Q
                         (W 0%nat + altsum_acc false W 1%nat m)%Q
                         (altsum W (Datatypes.S m))).
      * apply qleT'_plus_compat; [apply qleT'_refl | exact Q4].
      * apply qeq_leT'. rewrite Hadd, E01. ring.
  - apply (qleT'_trans (altsum W (Datatypes.S m))
                       (W 0%nat + altsum_acc false W 1%nat m)%Q
                       (W 0%nat)).
    + apply qeq_leT'. rewrite Hadd, E01. reflexivity.
    + apply (qleT'_trans (W 0%nat + altsum_acc false W 1%nat m)%Q
                         (W 0%nat + 0)%Q (W 0%nat)).
      * apply qleT'_plus_compat; [apply qleT'_refl | exact Q3].
      * apply qeq_leT'. ring.
Qed.
(* ---------- K2·β 挤压矛盾引擎（抽象定量面） ---------- *)
Lemma leibsep_beta_contra : forall (q : Q) (n : nat) (s t : Q) (M0 : nat) (eps : Q),
  QltT 0 ((Zpos (Qden q) # 1)%Q) ->
  QltT 0 q ->
  QleT' q (10 / 3)%Q ->
  (2 <= n)%nat ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  QltT 0 eps ->
  QltT (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
        + (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
           + Qabs (qpoly_eval (qpoly_deriv
                    (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
           + eps)%Q) 1 ->
  QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
        + Qabs (qpoly_eval (qpoly_deriv
                 (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
        + eps)
       (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                    - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q ->
  Id false true.
Proof.
  intros q n s t M0 eps Hb Hq Hq103 Hn Hs Ht Heps Hup Hlow.
  pose (c := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
              + Qabs (qpoly_eval (qpoly_deriv
                       (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
              + eps)%Q).
  assert (Hb0 : QleT' 0 ((Zpos (Qden q) # 1)%Q))
    by (apply lw0_QltT_le; exact Hb).
  assert (Hnn : forall k : nat, QleT' 0 (lw0_Wb (Zpos (Qden q) # 1)%Q q n k)).
  { intros k. apply lw0_Wb_seq_nonneg; [exact Hb0 | exact Hq]. }
  assert (Hdc : forall k : nat,
    QleT' (lw0_Wb (Zpos (Qden q) # 1)%Q q n (Datatypes.S k))
          (lw0_Wb (Zpos (Qden q) # 1)%Q q n k)).
  { intros k. apply lw0_Wb_seq_decr;
      [exact Hb0 | exact Hq | exact Hq103 | exact Hn]. }
  destruct (leibsep_G4c_pair_slack_window_from q n s t M0 Hs Ht eps Heps) as [Mt HMt].
  pose proof (HMt Mt (NatLe_lift Mt Mt (Nat.le_refl Mt))) as Hg.
  assert (Hr0le : Qle 0%Q (q_fact n)).
  { apply Qlt_le_weak. exact (q_fact_pos n). }
  assert (Hr0 : ~ q_fact n == 0%Q).
  { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)). symmetry. exact Hc. }
  assert (HE0 : forall x : Q, ((1 / q_fact n) * x) * q_fact n == x).
  { intros x. unfold Qdiv.
    rewrite Qmult_1_l.
    rewrite (Qmult_comm (/ q_fact n) x).
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ q_fact n) (q_fact n)).
    rewrite (Qmult_inv_r (q_fact n) Hr0).
    apply Qmult_1_r. }
  destruct (leibsep_altsum_two_shore (lw0_Wb (Zpos (Qden q) # 1)%Q q n) Hnn Hdc Mt)
    as [HloA HhiA].
  pose proof (lw0_pitB_bridge Mt (Zpos (Qden q) # 1)%Q q n) as Hbr.
  assert (HA : QleT' (1 / q_fact n
                      * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                    (lw0_sin_qp Mt) q)%Q
                     (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
  { apply (qleT'_trans
            (1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                          (lw0_sin_qp Mt) q)%Q
            (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) (Datatypes.S Mt))
            (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
    - apply qeq_leT'. symmetry. exact Hbr.
    - exact HhiA. }
  assert (HB : QleT' ((1 / q_fact n
                       * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                     (lw0_sin_qp Mt) q) * q_fact n)%Q
                     (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat * q_fact n)%Q).
  { apply Qle_to_QleT'.
    apply Qmult_le_compat_r.
    - exact (QleT'_to_Qle _ _ HA).
    - exact Hr0le. }
  assert (HU : QleT' (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                           (lw0_sin_qp Mt) q)
                     (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
  { apply (qleT'_trans
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)
            ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp Mt) q) * q_fact n)%Q
            (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
    - apply qeq_leT'. symmetry. apply HE0.
    - apply (qleT'_trans
              ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                (lw0_sin_qp Mt) q) * q_fact n)%Q
              (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat * q_fact n)%Q
              (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
      + exact HB.
      + apply qeq_leT'. ring. }
  assert (HA2 : QleT' (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                       - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat)%Q
                      (1 / q_fact n
                       * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                     (lw0_sin_qp Mt) q)%Q).
  { apply (qleT'_trans
            (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
             - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat)%Q
            (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) (Datatypes.S Mt))
            (1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                          (lw0_sin_qp Mt) q)%Q).
    - exact HloA.
    - apply qeq_leT'. exact Hbr. }
  assert (HB2 : QleT' ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                        - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
                      ((1 / q_fact n
                        * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                      (lw0_sin_qp Mt) q) * q_fact n)%Q).
  { apply Qle_to_QleT'.
    apply Qmult_le_compat_r.
    - exact (QleT'_to_Qle _ _ HA2).
    - exact Hr0le. }
  assert (HL : QleT' (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                                  - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
                     (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q)).
  { apply (qleT'_trans
            (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                         - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
            ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
              - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
              ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                (lw0_sin_qp Mt) q) * q_fact n)%Q
              (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)).
      + exact HB2.
      + apply qeq_leT'. apply HE0. }
  assert (Hdom : QleT' ((lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp Mt) q
                        - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q) c).
  { exact (qleT'_trans _ _ _ (leibsep_abs_ge_self _) Hg). }
  assert (Hdom' : QleT' ((lw0_K (Qnum q) (Zpos (Qden q)) n
                          - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                        (lw0_sin_qp Mt) q)%Q) c).
  { apply (qleT'_trans
            ((lw0_K (Qnum q) (Zpos (Qden q)) n
              - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                            (lw0_sin_qp Mt) q)%Q)
            (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q
                   - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
            c).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                 (lw0_sin_qp Mt) q
                     - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
              (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                 (lw0_sin_qp Mt) q
                     - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
              c).
      + apply (qleT'_trans
                (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q
                       - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
                (Qopp (Qopp (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                                (lw0_sin_qp Mt) q
                                    - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)))
                (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q
                       - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)).
        * apply lw0_opp_le_swap.
          exact (leibsep_abs_ge_opp
                  (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q
                    - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q).
        * apply qeq_leT'. ring.
      + exact Hg. }
  assert (HPU1 : QleT' (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp Mt) q)
                       (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { apply (qleT'_trans
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)
            ((lw0_K (Qnum q) (Zpos (Qden q)) n
              + (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q
                 - lw0_K (Qnum q) (Zpos (Qden q)) n))%Q)
            (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat; [apply qleT'_refl | exact Hdom]. }
  assert (HKU : QleT' (lw0_K (Qnum q) (Zpos (Qden q)) n)
                      (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat + c)%Q).
  { apply (qleT'_trans
            (lw0_K (Qnum q) (Zpos (Qden q)) n)
            ((lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q
              + (lw0_K (Qnum q) (Zpos (Qden q)) n
                 - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q))%Q)
            (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat + c)%Q).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat; [exact HU | exact Hdom']. }
  assert (H1K : QltT (lw0_K (Qnum q) (Zpos (Qden q)) n) 1).
  { apply Qlt_to_QltT.
    exact (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ HKU) (QltT_to_Qlt _ _ Hup)). }
  assert (HLOW2 : QleT' (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                                     - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
                        (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { exact (qleT'_trans _ _ _ HL HPU1). }
  assert (Hlt1 : Qlt c (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { exact (Qlt_le_trans _ _ _ (QltT_to_Qlt _ _ Hlow) (QleT'_to_Qle _ _ HLOW2)). }
  assert (H0K : Qlt 0%Q (lw0_K (Qnum q) (Zpos (Qden q)) n)).
  { apply (leibsep_qlt_wd2 0%Q
             ((lw0_K (Qnum q) (Zpos (Qden q)) n + c) - c)%Q
             0%Q (lw0_K (Qnum q) (Zpos (Qden q)) n)).
    - apply Qeq_refl.
    - assert (HE : ((lw0_K (Qnum q) (Zpos (Qden q)) n + c) - c)%Q
                   == lw0_K (Qnum q) (Zpos (Qden q)) n) by ring.
      exact HE.
    - exact (proj1 (Qlt_minus_iff c
                      (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q) Hlt1). }
  destruct (lw0_K_integer (Qnum q) (Zpos (Qden q)) n) as [z Hz].
  exact (lw0_pi_contra_gate (lw0_K (Qnum q) (Zpos (Qden q)) n) z
           (Qlt_to_QltT _ _ H0K) H1K Hz).
Qed.

(* ===== 出口核对（605 切片六件） ===== *)
Check leibsep_abs_ge_self.
Check leibsep_abs_ge_opp.
Check leibsep_sin_slot_from_band.
Check leibsep_cos_slot_from_band.
Check leibsep_altsum_two_shore.
Check leibsep_beta_contra.

(* ===== 件尾 Print Assumptions（605 切片六件逐发全 Closed 断言） ===== *)
Print Assumptions leibsep_abs_ge_self.
Print Assumptions leibsep_abs_ge_opp.
Print Assumptions leibsep_sin_slot_from_band.
Print Assumptions leibsep_cos_slot_from_band.
Print Assumptions leibsep_altsum_two_shore.
Print Assumptions leibsep_beta_contra.
Require Import UpReqBanachAdd.
From Stdlib Require Import ArithRing.

(* ---------- 基础桥微件 ---------- *)

(* Qeq 到 Qle（stdlib Qeq_le 判否；Qle 目标普通 rewrite 可用） *)
Lemma leibsep_qeq_le : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. rewrite H. apply Qle_refl.
Qed.

Lemma leibsep_alt_abs_one : forall j : nat, Qabs (lw0_alt j) == 1%Q.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - cbn [lw0_alt]. rewrite Qabs_opp. exact IH.
Qed.

(* qsum 三角 *)
Lemma leibsep_qsum_abs_tri : forall (g : nat -> Q) (m : nat),
  QleT' (Qabs (lw0_qsum g m)) (lw0_qsum (fun j => Qabs (g j)) m).
Proof.
  intros g m. induction m as [|m IH].
  - cbn [lw0_qsum]. apply qleT'_refl.
  - apply (qleT'_trans
            (Qabs (lw0_qsum g m + g (Datatypes.S m)))
            (Qabs (lw0_qsum g m) + Qabs (g (Datatypes.S m)))
            (lw0_qsum (fun j => Qabs (g j)) (Datatypes.S m))).
    + apply Qle_to_QleT'. apply Qabs_triangle.
    + apply qleT'_plus_compat; [exact IH | apply qleT'_refl].
Qed.

(* qsum 逐项放界 *)
Lemma leibsep_qsum_le : forall (g h : nat -> Q) (m : nat),
  (forall j : nat, QleT' (g j) (h j)) ->
  QleT' (lw0_qsum g m) (lw0_qsum h m).
Proof.
  intros g h m H. induction m as [|m IH].
  - cbn [lw0_qsum]. apply H.
  - cbn [lw0_qsum]. apply qleT'_plus_compat; [exact IH | apply H].
Qed.

(* qsum 非负项对长度单调（尾项零延拓） *)
Lemma leibsep_qsum_mono_len : forall (g : nat -> Q) (m : nat),
  (forall j : nat, QleT' 0 (g j)) ->
  QleT' (lw0_qsum g m) (lw0_qsum g (Datatypes.S m)).
Proof.
  intros g m H. cbn [lw0_qsum].
  apply (qleT'_trans (lw0_qsum g m) (lw0_qsum g m + 0)
          (lw0_qsum g (Datatypes.S m))).
  - apply qeq_leT'. ring.
  - apply qleT'_plus_compat; [apply qleT'_refl | apply H].
Qed.

(* qsum 常数函数闭式 *)
Lemma leibsep_qsum_const : forall (u : Q) (m : nat),
  lw0_qsum (fun _ => u) m == lw0_q_of_nat (Datatypes.S m) * u.
Proof.
  intros u m. induction m as [|m IH].
  - cbn [lw0_qsum].
    assert (H1 : lw0_q_of_nat 1 == 1%Q) by reflexivity.
    rewrite H1. ring.
  - cbn [lw0_qsum].
    replace (Datatypes.S (Datatypes.S m))%nat
      with ((Datatypes.S m) + 1)%nat by lia.
    rewrite (lw0_pitS_qof_add (Datatypes.S m) 1).
    rewrite IH.
    assert (H1 : lw0_q_of_nat 1 == 1%Q) by reflexivity.
    rewrite H1.
    ring.
Qed.

(* qsum 首项分离（eval-coef 展开装配件） *)
Lemma leibsep_qsum_shift : forall (g h : nat -> Q) (a x : Q) (J : nat),
  g 0%nat == a ->
  (forall i : nat, g (Datatypes.S i) == x * h i) ->
  lw0_qsum g (Datatypes.S J) == a + x * lw0_qsum h J.
Proof.
  intros g h a x J H0 HS. induction J as [|J IH].
  - cbn [lw0_qsum]. rewrite H0, HS. cbn [lw0_qsum]. ring.
  - cbn [lw0_qsum]. rewrite IH, HS. cbn [lw0_qsum]. ring.
Qed.

(* eval 的 qsum-coef 展开（存在 J 形——免表长链） *)
Lemma leibsep_eval_qsum_coef : forall (p : qpoly) (x : Q),
  sigT (fun J : nat =>
    qpoly_eval p x == lw0_qsum (fun j => lw0_coef j p * q_pow x j) J).
Proof.
  intros p x. induction p as [|a p IH].
  - exists 1%nat.
    cbn [qpoly_eval lw0_qsum lw0_coef q_pow]. ring.
  - destruct IH as [J HJ]. exists (Datatypes.S J).
    cbn [qpoly_eval]. symmetry. rewrite HJ.
    apply (leibsep_qsum_shift
             (fun j => lw0_coef j (cons a p) * q_pow x j)
             (fun i => lw0_coef i p * q_pow x i) a x J).
    + cbn [lw0_coef q_pow]. ring.
    + intros i. cbn [lw0_coef q_pow]. ring.
Qed.

(* binom 非负 / 出界零 / 阶乘占优 *)
Lemma leibsep_binom_nonneg : forall n k : nat, QleT' 0 (bpa_binom n k).
Proof.
  induction n as [|n IH]; intros k.
  - destruct k as [|k'].
    + reflexivity.
    + cbn [bpa_binom]. apply qleT'_refl.
  - destruct k as [|k'].
    + reflexivity.
    + apply (qleT'_trans 0 (0 + 0)
              (bpa_binom n k' + bpa_binom n (Datatypes.S k'))).
      * apply qeq_leT'. ring.
      * apply qleT'_plus_compat; [apply IH | apply IH].
Qed.

Lemma leibsep_binom_out : forall n k : nat, (n < k)%nat -> bpa_binom n k == 0%Q.
Proof.
  induction n as [|n IH]; intros k Hk.
  - destruct k as [|k']; [lia | reflexivity].
  - destruct k as [|k']; [lia | ].
    cbn [bpa_binom].
    rewrite (IH k' ltac:(lia)).
    rewrite (IH (Datatypes.S k') ltac:(lia)).
    ring.
Qed.

(* nat→Q 的 S 形 ≥ 1 微件（Qcompare 消去刀：字面支 reflexivity、Gt 支 Z 层矛盾） *)
(* qofnat_ge_one ＝池内现成件 lw0_q_of_nat_ge_one :407 直代（V1 律），不重造 *)


(* q_fact ≥ 1 *)
Lemma leibsep_qfact_ge_one : forall n : nat, QleT' 1 (q_fact n).
Proof.
  induction n as [|n IH].
  - cbn [q_fact]. apply qleT'_refl.
  - apply (qleT'_trans 1 ((Z.of_nat (Datatypes.S n) # 1) * q_fact n)
            (q_fact (Datatypes.S n))).
    + apply Qle_to_QleT'.
      apply (Qmult_le_compat_nonneg 1
               (Z.of_nat (Datatypes.S n) # 1) 1 (q_fact n)).
      * split.
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg 1)).
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one n)).
      * split.
        -- exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg 1)).
        -- exact (QleT'_to_Qle _ _ IH).
    + apply qeq_leT'. rewrite (q_fact_succ n). ring.
Qed.

Lemma leibsep_binom_le_qfact : forall n k : nat, QleT' (bpa_binom n k) (q_fact n).
Proof.
  induction n as [|n IH]; intros k.
  - destruct k as [|k'].
    + cbn [bpa_binom q_fact]. apply qleT'_refl.
    + cbn [bpa_binom q_fact]. reflexivity.
  - destruct k as [|k'].
    + apply (qleT'_trans 1 ((Z.of_nat (Datatypes.S n) # 1) * q_fact n)
              (q_fact (Datatypes.S n))).
      * apply Qle_to_QleT'.
        apply (Qmult_le_compat_nonneg 1
                 (Z.of_nat (Datatypes.S n) # 1) 1 (q_fact n)).
        -- split.
           ++ exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg 1)).
           ++ exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one n)).
        -- split.
           ++ exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg 1)).
           ++ exact (QleT'_to_Qle _ _ (leibsep_qfact_ge_one n)).
      * apply qeq_leT'. rewrite (q_fact_succ n). ring.
    + cbn [bpa_binom].
      destruct n as [|m].
      * (* n=0：binom 0 k' + binom 0 1 ≤ 1 *)
        destruct k' as [|k''].
        -- cbn [bpa_binom]. cbn [q_fact]. reflexivity.
        -- cbn [bpa_binom]. cbn [q_fact]. reflexivity.
      * (* n = S m ≥ 1：q+q ≤ (S n)#1·q 系数链 *)
        apply (qleT'_trans
                (bpa_binom (Datatypes.S m) k'
                 + bpa_binom (Datatypes.S m) (Datatypes.S k'))
                (q_fact (Datatypes.S m) + q_fact (Datatypes.S m))
                (q_fact (Datatypes.S (Datatypes.S m)))).
        -- apply qleT'_plus_compat;
           [apply (IH k') | apply (IH (Datatypes.S k'))].
        -- apply (qleT'_trans
                  (q_fact (Datatypes.S m) + q_fact (Datatypes.S m))
                  ((Z.of_nat 2 # 1) * q_fact (Datatypes.S m))
                  (q_fact (Datatypes.S (Datatypes.S m)))).
           ++ apply qeq_leT'. ring.
           ++ apply (qleT'_trans
                     ((Z.of_nat 2 # 1) * q_fact (Datatypes.S m))
                     (q_fact (Datatypes.S m) * (Z.of_nat 2 # 1))
                     ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                       * q_fact (Datatypes.S m))).
              ** apply qeq_leT'. ring.
              ** apply (qleT'_trans
                        (q_fact (Datatypes.S m) * (Z.of_nat 2 # 1))
                        (q_fact (Datatypes.S m)
                          * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1))
                        ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)
                          * q_fact (Datatypes.S m))).
                 --- apply Qle_to_QleT'.
                     apply (lw0_q_mult_le_l (q_fact (Datatypes.S m))).
                     ++++ apply Qlt_le_weak. exact (q_fact_pos _).
                     ++++ exact (QleT'_to_Qle _ _
                              (lw0_q_of_nat_le_mono 2
                                 (Datatypes.S (Datatypes.S m)) ltac:(lia))).
                 --- apply qeq_leT'. ring.
Qed.

(* ---------- μ1：±1 幂绝对值恒一 ---------- *)
Lemma leibsep_qabs_pow_neg1 : forall i : nat, Qabs (q_pow (-1)%Q i) == 1%Q.
Proof.
  induction i as [|i IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qabs_Qmult.
    rewrite IH. reflexivity.
Qed.

(* ---------- μ1b：|x^k| == |x|^k ---------- *)
Lemma leibsep_qabs_pow : forall (x : Q) (k : nat),
  Qabs (q_pow x k) == q_pow (Qabs x) k.
Proof.
  intros x k. induction k as [|k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite Qabs_Qmult, IH. reflexivity.
Qed.

(* ---------- μ2：qsum 零尾延拓（差归纳形） ---------- *)
Lemma leibsep_qsum_ext0 : forall (g : nat -> Q) (m d : nat),
  (forall j : nat, (m < j)%nat -> (j <= m + d)%nat -> g j == 0%Q) ->
  lw0_qsum g (m + d) == lw0_qsum g m.
Proof.
  intros g m d. induction d as [|d IH].
  - intros H. rewrite Nat.add_0_r. reflexivity.
  - intros H.
    replace (m + Datatypes.S d)%nat with (Datatypes.S (m + d))%nat by lia.
    cbn [lw0_qsum].
    rewrite (IH (fun j Hj1 Hj2 =>
              H j Hj1 (Nat.le_trans j (m + d) (m + Datatypes.S d)
                         Hj2 ltac:(lia)))).
    rewrite (H (Datatypes.S (m + d)) ltac:(lia) ltac:(lia)).
    ring.
Qed.

(* ---------- μ3：qsum 非负多步单调 ---------- *)
Lemma leibsep_qsum_mono_len_multi : forall (g : nat -> Q) (m m' : nat),
  (forall j : nat, QleT' 0 (g j)) ->
  (m <= m')%nat ->
  QleT' (lw0_qsum g m) (lw0_qsum g m').
Proof.
  intros g m m' Hg Hmm.
  induction m' as [|m'' IH].
  - assert (Heq : m = 0%nat) by lia. subst m.
    apply qleT'_refl.
  - destruct (Nat.eq_dec m (Datatypes.S m'')) as [Heq | Hne].
    + subst m. apply qleT'_refl.
    + assert (Hlt : (m <= m'')%nat) by lia.
      specialize (IH Hlt).
      apply (qleT'_trans (lw0_qsum g m) (lw0_qsum g m'')
              (lw0_qsum g (Datatypes.S m''))).
      * exact IH.
      * cbn [lw0_qsum].
        apply (qleT'_trans (lw0_qsum g m'') (lw0_qsum g m'' + 0)
                (lw0_qsum g m'' + g (Datatypes.S m''))).
        -- apply qeq_leT'. ring.
        -- apply qleT'_plus_compat; [apply qleT'_refl | apply Hg].
Qed.

(* ---------- μ4：同底幂指数单调（1 ≤ B） ---------- *)
Lemma leibsep_q_pow_exp_mono : forall (B : Q) (k m : nat),
  QleT' 1 B -> (k <= m)%nat -> QleT' (q_pow B k) (q_pow B m).
Proof.
  intros B k m HB Hkm.
  induction m as [|m IH].
  - assert (Heq : k = 0%nat) by lia. subst k.
    apply qleT'_refl.
  - destruct (Nat.eq_dec k (Datatypes.S m)) as [Heq | Hne].
    + subst k. apply qleT'_refl.
    + assert (Hlt : (k <= m)%nat) by lia.
      specialize (IH Hlt).
      cbn [q_pow].
      apply (qleT'_trans (q_pow B k) (1 * q_pow B m)
              (B * q_pow B m)).
      * apply (qleT'_trans (q_pow B k) (q_pow B m) (1 * q_pow B m)).
        -- exact IH.
        -- apply qeq_leT'. ring.
      * apply Qle_to_QleT'.
        apply (Qmult_le_compat_nonneg 1 B (q_pow B m) (q_pow B m)).
        -- split.
           ++ apply Qlt_le_weak. apply QltT_to_Qlt.
              exact (lw0_q_of_nat_lt0T_S 0%nat).
           ++ exact (QleT'_to_Qle _ _ HB).
        -- split.
           ++ apply q_pow_nonneg.
              apply (Qle_trans 0 1 B).
              ** exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg 1)).
              ** exact (QleT'_to_Qle _ _ HB).
           ++ apply Qle_refl.
Qed.

(* ---------- μ8：q 正性与乘积非负 ---------- *)
Lemma leibsep_qpow_mul_nonneg : forall (x : Q) (k : nat) (y : Q),
  QleT' 0 x -> QleT' 0 y -> QleT' 0 (q_pow x k * y).
Proof.
  intros x k y Hx Hy.
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  * apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hx).
  * exact (QleT'_to_Qle _ _ Hy).
Qed.

(* ---------- gate=false 反形微件（对偶形；Qlt_le_dec 冲突法） ---------- *)
Lemma leibsep_gate_open_false : forall (q : Q) (N : nat) (c0 : Q),
  leibsep_gate_open q N c0 = false ->
  QleT' (Qabs ((lw0m_xL N - q)%Q)) (lw0m_e N + 2 * c0)%Q.
Proof.
  intros q N c0 H. unfold leibsep_gate_open in H.
  destruct (lw0m_e N + 2 * c0 ?= Qabs ((lw0m_xL N - q)%Q))%Q eqn:Hcmp.
  - (* Eq：e+2c0 == |x| ⟹ |x| ≤ e+2c0 *)
    apply Qle_to_QleT'.
    rewrite <- (proj2 (Qeq_alt (lw0m_e N + 2 * c0)%Q
                         (Qabs ((lw0m_xL N - q)%Q))) Hcmp).
    apply Qle_refl.
  - (* Lt：门真臂矛盾 *)
    discriminate H.
  - (* Gt：|x| < e+2c0 ⟹ ≤ *)
    apply Qle_to_QleT'.
    apply Qlt_le_weak.
    exact (proj2 (Qgt_alt (lw0m_e N + 2 * c0)%Q
                    (Qabs ((lw0m_xL N - q)%Q))) Hcmp).
Qed.

(* ---------- μ7：除法乘积消去（K2 HE0 模板两例） ---------- *)
Lemma leibsep_div_mul_cancel : forall (x : Q) (k : nat),
  (~ q_fact k == 0%Q) ->
  (q_pow x k / q_fact k * q_fact k)%Q == q_pow x k.
Proof.
  intros x k Hnz.
  unfold Qdiv.
  rewrite (Qmult_comm (q_pow x k * / q_fact k) (q_fact k)).
  rewrite Qmult_assoc.
  rewrite (Qmult_comm (q_fact k) (q_pow x k)).
  rewrite <- Qmult_assoc.
  rewrite (Qmult_inv_r (q_fact k) Hnz).
  ring.
Qed.

Lemma leibsep_div_mul : forall x y : Q,
  (~ y == 0%Q) -> (x / y * y)%Q == x.
Proof.
  intros x y H.
  unfold Qdiv.
  rewrite (Qmult_comm (x * / y) y).
  rewrite Qmult_assoc.
  rewrite (Qmult_comm y x).
  rewrite <- Qmult_assoc.
  rewrite (Qmult_inv_r y H).
  ring.
Qed.

(* ---------- μ7b：绝对值积式消去 ---------- *)
Lemma leibsep_qabs_div_mul : forall x y : Q,
  (~ y == 0%Q) -> Qabs (x / y) * Qabs y == Qabs x.
Proof.
  intros x y H.
  rewrite <- Qabs_Qmult.
  rewrite (leibsep_div_mul x y H).
  reflexivity.
Qed.

(* ---------- μ9：积式同调（Qeq 面 rewrite 正器配套） ---------- *)
Lemma leibsep_qmult_wd_l : forall (f a b : Q), a == b -> f * a == f * b.
Proof.
  intros f a b H. rewrite H. reflexivity.
Qed.

(* ---------- μ6：coef_niven 界件（使命 1 之系数核心；全 apply/transitivity 化） ---------- *)
Lemma leibsep_coef_niven_le : forall (q b : Q) (Bq : Q) (n j : nat),
  (1 <= n)%nat ->
  QleT' (Qabs q) Bq ->
  QleT' 1 Bq ->
  QleT' (Qabs (lw0_coef j (lw0_niven_f q b n)))
        (q_pow (Qabs b) n * q_pow Bq (2 * n))%Q.
Proof.
  intros q b Bq n j Hn Hq HBq.
  assert (H0 : QleT' 0 Bq).
  { apply (qleT'_trans 0 1 Bq).
    - apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt.
      exact (lw0_q_of_nat_lt0T_S 0%nat).
    - exact HBq. }
  assert (Hnz : ~ q_fact n == 0%Q).
  { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)). symmetry. exact Hc. }
  assert (Hfold : Qabs (q_pow b n / q_fact n) * q_fact n == Qabs (q_pow b n)).
  { transitivity (Qabs (q_pow b n / q_fact n) * Qabs (q_fact n)).
    - apply leibsep_qmult_wd_l.
      symmetry. apply Qabs_pos. apply Qlt_le_weak. exact (q_fact_pos n).
    - apply (leibsep_qabs_div_mul (q_pow b n) (q_fact n) Hnz). }
  destruct (le_gt_dec n j) as [Hnj | Hjn].
  - (* n ≤ j：主支 *)
    assert (Habs : Qabs (lw0_coef j (lw0_niven_f q b n)) ==
                   Qabs ((q_pow b n / q_fact n)
                          * (bpa_binom n (j - n) * q_pow (-1)%Q (j - n)
                              * q_pow q (n - (j - n))))).
    { unfold lw0_niven_f.
      rewrite (lw0_coef_scalar j (q_pow b n / q_fact n)
                 (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n))),
              (lw0_mul_comm (lw0_pi_mono n) (lw0_pi_qminus_pow q n) j),
              (lw0_coef_mul_congr (lw0_pi_qminus_pow q n) (lw0_pi_mono n)
                 (lw0_mono n) (lw0_pi_mono_z_bridge n) j),
              (lw0_mul_comm (lw0_pi_qminus_pow q n) (lw0_mono n) j),
              (lw0_coef_mul_congr (lw0_mono n) (lw0_pi_qminus_pow q n)
                 (lw0_qminus_pow q n) (lw0_pi_qminus_z_bridge q n) j),
              (lw0_coef_mul_mono_ge n j (lw0_qminus_pow q n) Hnj),
              (lw0_coef_qminus_pow n q (j - n)).
      reflexivity. }
    apply (qleT'_trans
            (Qabs (lw0_coef j (lw0_niven_f q b n)))
            (Qabs ((q_pow b n / q_fact n)
                    * (bpa_binom n (j - n) * q_pow (-1)%Q (j - n)
                        * q_pow q (n - (j - n)))))
            (q_pow (Qabs b) n * q_pow Bq (2 * n))).
    { apply (qeq_leT' _ _ Habs). }
    { apply Qle_to_QleT'.
      rewrite (Qabs_Qmult (q_pow b n / q_fact n)
                 ((bpa_binom n (j - n) * q_pow (-1)%Q (j - n))
                   * q_pow q (n - (j - n)))),
              (Qabs_Qmult (bpa_binom n (j - n) * q_pow (-1)%Q (j - n))
                 (q_pow q (n - (j - n)))),
              (Qabs_Qmult (bpa_binom n (j - n)) (q_pow (-1)%Q (j - n))),
              (leibsep_qabs_pow_neg1 (j - n)), Qmult_1_r,
              (leibsep_qabs_pow q (n - (j - n))),
              (Qabs_pos (bpa_binom n (j - n))
                 (QleT'_to_Qle _ _ (leibsep_binom_nonneg n (j - n)))).
      (* Qle 域放界：|a|·(binom·|q|^k) ≤ |b|^n·Bq^{2n}，中项取重写后实形
         q_pow (Qabs q) (n-(j-n))（非草稿旧形 Qabs (q_pow q k)） *)
      apply (Qle_trans
              _
              (q_pow (Qabs b) n * q_pow Bq (n - (j - n)))
              (q_pow (Qabs b) n * q_pow Bq (2 * n))).
      { apply (Qle_trans
                _
                (Qabs (q_pow b n / q_fact n)
                  * (q_fact n * q_pow (Qabs q) (n - (j - n))))
                (q_pow (Qabs b) n * q_pow Bq (n - (j - n)))).
        { apply (lw0_q_mult_le_l (Qabs (q_pow b n / q_fact n))).
          - apply Qabs_nonneg.
          - apply (Qle_trans
                    (bpa_binom n (j - n) * q_pow (Qabs q) (n - (j - n)))
                    (q_pow (Qabs q) (n - (j - n)) * bpa_binom n (j - n))
                    (q_fact n * q_pow (Qabs q) (n - (j - n)))).
            + apply leibsep_qeq_le. ring.
            + apply (Qle_trans
                      (q_pow (Qabs q) (n - (j - n)) * bpa_binom n (j - n))
                      (q_pow (Qabs q) (n - (j - n)) * q_fact n)
                      (q_fact n * q_pow (Qabs q) (n - (j - n)))).
              * apply (lw0_q_mult_le_l (q_pow (Qabs q) (n - (j - n)))).
                -- apply q_pow_nonneg. apply Qabs_nonneg.
                -- exact (QleT'_to_Qle _ _ (leibsep_binom_le_qfact n (j - n))).
              * apply leibsep_qeq_le. ring. }
        { apply (Qle_trans
                  (Qabs (q_pow b n / q_fact n)
                    * (q_fact n * q_pow (Qabs q) (n - (j - n))))
                  ((Qabs (q_pow b n / q_fact n) * q_fact n)
                    * q_pow (Qabs q) (n - (j - n)))
                  (q_pow (Qabs b) n * q_pow Bq (n - (j - n)))).
          { apply leibsep_qeq_le. ring. }
          { rewrite Hfold.
            rewrite (leibsep_qabs_pow b n).
            apply (lw0_q_mult_le_l (q_pow (Qabs b) n)).
            - apply q_pow_nonneg. apply Qabs_nonneg.
            - apply q_pow_mono.
              + apply Qabs_nonneg.
              + exact (QleT'_to_Qle _ _ Hq). } } }
      { apply (lw0_q_mult_le_l (q_pow (Qabs b) n)).
        - apply q_pow_nonneg. apply Qabs_nonneg.
        - exact (QleT'_to_Qle _ _
                   (leibsep_q_pow_exp_mono Bq (n - (j - n)) (2 * n) HBq
                      ltac:(lia))). } }
  - (* j < n：系数为零支 *)
    assert (Hz : lw0_coef j (lw0_niven_f q b n) == 0%Q).
    { unfold lw0_niven_f.
      rewrite (lw0_coef_scalar j (q_pow b n / q_fact n)
                 (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n))),
              (lw0_mul_comm (lw0_pi_mono n) (lw0_pi_qminus_pow q n) j),
              (lw0_coef_mul_congr (lw0_pi_qminus_pow q n) (lw0_pi_mono n)
                 (lw0_mono n) (lw0_pi_mono_z_bridge n) j),
              (lw0_mul_comm (lw0_pi_qminus_pow q n) (lw0_mono n) j),
              (lw0_coef_mul_congr (lw0_mono n) (lw0_pi_qminus_pow q n)
                 (lw0_qminus_pow q n) (lw0_pi_qminus_z_bridge q n) j),
              (lw0_coef_mul_mono_lt n j (lw0_qminus_pow q n) Hjn).
      ring. }
    assert (Haz : Qabs 0%Q == 0%Q) by reflexivity.
    apply (qleT'_trans
            (Qabs (lw0_coef j (lw0_niven_f q b n))) (Qabs 0%Q)
            (q_pow (Qabs b) n * q_pow Bq (2 * n))).
    { apply (qeq_leT' _ _). apply Qabs_wd. exact Hz. }
    { apply (qleT'_trans (Qabs 0%Q) 0%Q
              (q_pow (Qabs b) n * q_pow Bq (2 * n))).
      - apply (qeq_leT' _ _ Haz).
      - apply leibsep_qpow_mul_nonneg.
        + apply Qle_to_QleT'. apply Qabs_nonneg.
        + apply Qle_to_QleT'. apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0). }
Qed.

Print Assumptions leibsep_coef_niven_le.


(* ---------- 半量微件族：单步压缩 / 幂迭代 / 半量结论面 ---------- *)

(* 交叉乘转移：正分母两侧同乘后取消（取消向引理直代，积式恒等全外层 ring） *)
Lemma leibsep_w0n_xfer : forall A B C D : Q,
  Qlt 0 C -> Qlt 0 D ->
  QleT' (A * D) (B * C) ->
  QleT' (A * / C) (B * / D).
Proof.
  intros A B C D HC HD H.
  assert (Hpos : QltT 0 (C * D)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact HC.
    - exact HD. }
  assert (Hbr1 : ((A * / C) * (C * D))%Q == A * D).
  { transitivity ((A * (C * / C)) * D)%Q.
    - ring.
    - rewrite (Qmult_inv_r C (lw0_pitS_qne0_of_pos C (Qlt_to_QltT 0 C HC))). ring. }
  assert (Hbr3 : ((B * / D) * (C * D))%Q == B * C).
  { transitivity ((B * (D * / D)) * C)%Q.
    - ring.
    - rewrite (Qmult_inv_r D (lw0_pitS_qne0_of_pos D (Qlt_to_QltT 0 D HD))). ring. }
  apply (lw0_pitS_qmult_reg_r (A * / C) (B * / D) (C * D) Hpos).
  apply Qle_to_QleT'.
  apply (Qle_trans ((A * / C) * (C * D))%Q (A * D)%Q ((B * / D) * (C * D))%Q).
  - apply leibsep_qeq_le. exact Hbr1.
  - apply (Qle_trans (A * D)%Q (B * C)%Q ((B * / D) * (C * D))%Q).
    + exact (QleT'_to_Qle _ _ H).
    + apply leibsep_qeq_le. exact (Qeq_sym _ _ Hbr3).
Qed.

Lemma leibsep_w0n_step : forall (b q : Q) (d n : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (20 * d <= n)%nat ->
  QleT' (q_fact (Datatypes.S n) * lw0_Wb b q (Datatypes.S n) 0)%Q
        ((1 # 5) * (q_fact n * lw0_Wb b q n 0))%Q.
Proof.
  intros b q d n Hb Hq0 Hq103 Hbd Hn.
  unfold lw0_Wb.
  replace (2 * Datatypes.S n + 2 * 0 + 2)%nat
    with (Datatypes.S (Datatypes.S (2 * n + 2)))%nat by lia.
  replace (Datatypes.S n + 2 * 0 + 1)%nat
    with (Datatypes.S (Datatypes.S n))%nat by lia.
  replace (2 * n + 2 * 0 + 2)%nat with (2 * n + 2)%nat by lia.
  replace (n + 2 * 0 + 1)%nat with (Datatypes.S n)%nat by lia.
  replace (2 * 0 + 1)%nat with 1%nat by lia.
  assert (E1009 : ((10 / 3) * (10 / 3))%Q == (100 # 9)%Q) by reflexivity.
  assert (En2 : (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                == lw0_q_of_nat (Datatypes.S (Datatypes.S n))) by reflexivity.
  assert (Ed : (Z.of_nat d # 1) == lw0_q_of_nat d) by reflexivity.
  assert (En4 : (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                == lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * n + 2)))) by reflexivity.
  assert (En3 : (Z.of_nat (Datatypes.S (2 * n + 2)) # 1)
                == lw0_q_of_nat (Datatypes.S (2 * n + 2))) by reflexivity.
  assert (Enat : (9 * Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2)
                   = 18 * (2 * n + 3) * Datatypes.S (Datatypes.S n))%nat) by ring.
  assert (Hqp2 : QleT' (q * q) (100 # 9)).
  { apply (qleT'_trans (q * q) (q_pow q 2) (100 # 9)).
    - apply (qeq_leT' (q * q) (q_pow q 2)).
      rewrite (q_pow_succ q 1), (q_pow_succ q 0). cbn [q_pow]. ring.
    - apply (qleT'_trans (q_pow q 2) (q_pow (10 / 3) 2) (100 # 9)).
      + apply Qle_to_QleT'. apply q_pow_mono.
        * exact (QleT'_to_Qle _ _ Hq0).
        * exact (QleT'_to_Qle _ _ Hq103).
      + apply (qeq_leT' (q_pow (10 / 3) 2) (100 # 9)).
        rewrite (q_pow_succ (10 / 3) 1), (q_pow_succ (10 / 3) 0). cbn [q_pow].
        transitivity ((10 / 3) * (10 / 3))%Q.
        * ring.
        * exact E1009. }
  assert (HXY : QleT' (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
                      ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))).
  { apply (qleT'_trans
            (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
            ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (q * q))
            ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))).
    - apply qeq_leT'. ring.
    - apply Qle_to_QleT'.
      apply (lw0_q_mult_le_l (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)).
      + apply (Qlt_le_weak 0). apply QltT_to_Qlt.
        exact (lw0_q_of_nat_lt0T_S (Datatypes.S n)).
      + exact (QleT'_to_Qle _ _ Hqp2). }
  assert (Hl1 : QleT' (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                      ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
  { apply (qleT'_trans
            (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * b)
            ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * b)
              (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (Z.of_nat d # 1))
              ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
      + apply Qle_to_QleT'.
        apply (lw0_q_mult_le_l (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))).
        * apply Qmult_le_0_compat.
          -- apply Qmult_le_0_compat.
             ++ exact (QleT'_to_Qle _ _ Hq0).
             ++ exact (QleT'_to_Qle _ _ Hq0).
          -- apply (Qlt_le_weak 0). apply QltT_to_Qlt.
             exact (lw0_q_of_nat_lt0T_S (Datatypes.S n)).
        * exact (QleT'_to_Qle _ _ Hbd).
      + apply qeq_leT'. ring. }
  assert (Hl2 : QleT' ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                      ((Z.of_nat d # 1)
                       * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (Z.of_nat d # 1)).
    - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)).
    - exact (QleT'_to_Qle _ _ HXY). }
  assert (E500 : 500%Q == lw0_q_of_nat 500) by reflexivity.
  assert (Hbr500 : ((Z.of_nat d # 1)
                    * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)) * 45)%Q
                   == lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n))).
  { rewrite En2, Ed.
    transitivity ((500%Q * lw0_q_of_nat d)
                  * lw0_q_of_nat (Datatypes.S (Datatypes.S n)))%Q.
    - ring.
    - rewrite E500.
      rewrite <- (lw0_pitS_qof_mul 500 d).
      rewrite <- (lw0_pitS_qof_mul (500 * d) (Datatypes.S (Datatypes.S n))).
      reflexivity. }
  assert (E9 : 9%Q == lw0_q_of_nat 9) by reflexivity.
  assert (Hbr45 : (((1 # 5) * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                              * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q
                  == lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                                   * Datatypes.S (2 * n + 2)))).
  { rewrite En4, En3.
    transitivity (9%Q * (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * n + 2)))
                         * lw0_q_of_nat (Datatypes.S (2 * n + 2))))%Q.
    - ring.
    - rewrite E9.
      rewrite <- (lw0_pitS_qof_mul (Datatypes.S (Datatypes.S (2 * n + 2)))
                   (Datatypes.S (2 * n + 2))).
      rewrite <- (lw0_pitS_qof_mul 9
                   (Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2))).
      replace (9 * (Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2)))%nat
        with (9 * Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2))%nat
        by ring.
      reflexivity. }
  assert (Hl3 : QleT' ((Z.of_nat d # 1)
                       * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
                      ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                   * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
  { apply (lw0_pitS_qmult_reg_r
             ((Z.of_nat d # 1)
              * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
             ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                         * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) 45%Q).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply Qle_to_QleT'.
      apply (Qle_trans
              (((Z.of_nat d # 1)
                * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))) * 45)%Q
              (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
              (((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                             * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q).
      + apply leibsep_qeq_le. exact Hbr500.
      + apply (Qle_trans
                (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
                (lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                               * Datatypes.S (2 * n + 2)))
                (((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                             * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q).
        * assert (Hmono : QleT' (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
                                (lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                                               * Datatypes.S (2 * n + 2)))).
          { apply lw0_q_of_nat_le_mono.
            rewrite Enat.
            apply (Nat.le_trans _ (25 * n * Datatypes.S (Datatypes.S n)) _).
            -- apply Nat.mul_le_mono_r. lia.
            -- apply Nat.mul_le_mono_r. lia. }
          exact (QleT'_to_Qle _ _ Hmono).
        * apply leibsep_qeq_le. exact (Qeq_sym _ _ Hbr45). }
  assert (Hheart : QleT' (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                         ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                     * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
  { apply (qleT'_trans
            (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                        * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
    - exact Hl1.
    - apply (qleT'_trans
              ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
              ((Z.of_nat d # 1)
               * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
              ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                          * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
      + exact Hl2.
      + exact Hl3. }
  assert (HheartS : QleT'
    (q_fact (Datatypes.S n)
     * (q_fact (Datatypes.S n) * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))))
    (q_fact (Datatypes.S n)
     * (q_fact (Datatypes.S n)
         * ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                       * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (q_fact (Datatypes.S n))).
    - apply Qlt_le_weak. apply q_fact_pos.
    - apply (lw0_q_mult_le_l (q_fact (Datatypes.S n))).
      + apply Qlt_le_weak. apply q_fact_pos.
      + exact (QleT'_to_Qle _ _ Hheart). }
  assert (Hcommon : Qle 0
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2)))))).
  { apply Qmult_le_0_compat.
    - apply q_pow_nonneg. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Hb.
    - apply Qmult_le_0_compat.
      + apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hq0).
      + apply Qmult_le_0_compat.
        * apply Qlt_le_weak. apply q_fact_pos.
        * apply Qmult_le_0_compat.
          -- apply Qlt_le_weak. apply q_fact_pos.
          -- apply Qlt_le_weak. apply q_fact_pos. }
  assert (HheartC : QleT'
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
     * (q_fact (Datatypes.S n)
         * (q_fact (Datatypes.S n)
             * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
     * (q_fact (Datatypes.S n)
         * (q_fact (Datatypes.S n)
             * ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                           * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))))))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l
            (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2)))))).
    - exact Hcommon.
    - exact (QleT'_to_Qle _ _ HheartS). }
  assert (Hprem : QleT'
    ((q_fact (Datatypes.S n)
      * ((b * q_pow b n)
         * (q * (q * q_pow q (2 * n + 2))
             * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n)))))
     * (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
    ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
     * (q_fact (Datatypes.S n) * q_fact 1
               * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
  { apply (qleT'_trans
            ((q_fact (Datatypes.S n)
              * ((b * q_pow b n)
                 * (q * (q * q_pow q (2 * n + 2))
                     * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                        * q_fact (Datatypes.S n)))))
             * (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
            (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
             * (q_fact (Datatypes.S n)
                 * (q_fact (Datatypes.S n)
                     * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
            ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
             * (q_fact (Datatypes.S n) * q_fact 1
                       * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
               * (q_fact (Datatypes.S n)
                   * (q_fact (Datatypes.S n)
                       * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
              (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
               * (q_fact (Datatypes.S n)
                   * (q_fact (Datatypes.S n)
                       * ((1 # 5) * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                     * (Z.of_nat (Datatypes.S (2 * n + 2)) # 1))))))
              ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
               * (q_fact (Datatypes.S n) * q_fact 1
                         * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
      + exact HheartC.
      + apply qeq_leT'.
        rewrite (q_fact_succ (Datatypes.S (2 * n + 2))), (q_fact_succ (2 * n + 2)).
        ring. }
  assert (Hdso : Qlt 0 (q_fact (Datatypes.S n) * q_fact 1
                         * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply q_fact_pos.
      + apply q_fact_pos.
    - apply q_fact_pos. }
  assert (Hdno : Qlt 0 (q_fact n * q_fact 1 * q_fact (2 * n + 2))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply q_fact_pos.
      + apply q_fact_pos.
    - apply q_fact_pos. }
  apply (qleT'_trans
          (q_fact (Datatypes.S n)
           * (q_pow b (Datatypes.S n)
              * q_pow q (Datatypes.S (Datatypes.S (2 * n + 2)))
              * q_fact (Datatypes.S (Datatypes.S n))
              / (q_fact (Datatypes.S n) * q_fact 1
                 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))))
          ((q_fact (Datatypes.S n)
            * ((b * q_pow b n)
               * (q * (q * q_pow q (2 * n + 2))
                   * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                      * q_fact (Datatypes.S n)))))
           / (q_fact (Datatypes.S n) * q_fact 1
              * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
          ((1 # 5) * (q_fact n
                      * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n)
                         / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
  - apply qeq_leT'.
    unfold Qdiv.
    rewrite (q_pow_succ b n), (q_pow_succ q (Datatypes.S (2 * n + 2))),
            (q_pow_succ q (2 * n + 2)), (q_fact_succ (Datatypes.S n)).
    ring.
  - apply (qleT'_trans
            ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
            ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) * / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
            ((1 # 5) * (q_fact n * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n) / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
    + apply qeq_leT'.
      unfold Qdiv.
      ring.
    + apply (qleT'_trans
              ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) * / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
              (((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))) * / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
              ((1 # 5) * (q_fact n * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n) / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
      * exact (leibsep_w0n_xfer
                 (q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n)))))
                 ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n)))))
                 (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))
                 (q_fact n * q_fact 1 * q_fact (2 * n + 2))
                 Hdso Hdno Hprem).
      * apply qeq_leT'. unfold Qdiv. ring.
Qed.

Lemma leibsep_w0n_pow : forall (b q : Q) (d n j : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (20 * d <= n)%nat ->
  QleT' (q_fact (n + j) * lw0_Wb b q (n + j) 0)%Q
        (q_pow (1 # 5) j * (q_fact n * lw0_Wb b q n 0))%Q.
Proof.
  intros b q d n j Hb Hq0 Hq103 Hbd Hn.
  induction j as [| j IH].
  - replace (n + 0)%nat with n%nat by lia.
    apply (qeq_leT' (q_fact n * lw0_Wb b q n 0)
                    (q_pow (1 # 5) 0 * (q_fact n * lw0_Wb b q n 0))).
    cbn [q_pow]. ring.
  - replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j))%nat by lia.
    apply (qleT'_trans
            (q_fact (Datatypes.S (n + j)) * lw0_Wb b q (Datatypes.S (n + j)) 0)
            ((1 # 5) * (q_fact (n + j) * lw0_Wb b q (n + j) 0))
            (q_pow (1 # 5) (Datatypes.S j) * (q_fact n * lw0_Wb b q n 0))).
    + apply (leibsep_w0n_step b q d (n + j) Hb Hq0 Hq103 Hbd ltac:(lia)).
    + apply (qleT'_trans
              ((1 # 5) * (q_fact (n + j) * lw0_Wb b q (n + j) 0))
              ((1 # 5) * (q_pow (1 # 5) j * (q_fact n * lw0_Wb b q n 0)))
              (q_pow (1 # 5) (Datatypes.S j) * (q_fact n * lw0_Wb b q n 0))).
      * apply Qle_to_QleT'.
        apply (lw0_q_mult_le_l (1 # 5)%Q).
        -- unfold Qle. cbn [Qnum Qden]. lia.
        -- exact (QleT'_to_Qle _ _ IH).
      * apply qeq_leT'.
        rewrite (q_pow_succ (1 # 5) j). ring.
Qed.

Lemma leibsep_w0n_half : forall (b q : Q) (d k j : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (1 <= j)%nat ->
  QltT (q_fact (lw0_n_select (10 * d) k + j)
        * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)%Q (1 # 2)%Q.
Proof.
  intros b q d k j Hb Hq0 Hq103 Hbd Hj.
  assert (Hn0 : (20 * d <= lw0_n_select (10 * d) k)%nat).
  { unfold lw0_n_select. pose proof (Nat.le_max_r k (10 * d)). lia. }
  assert (Hlt1 : QltT (q_fact (lw0_n_select (10 * d) k)
                       * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1).
  { exact (lw0_pi_w0n_lt1 b q d k Hb Hq0 Hq103 Hbd). }
  assert (Hle1 : QleT' (q_fact (lw0_n_select (10 * d) k)
                        * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1).
  { apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt1. }
  assert (Hpow : QleT' (q_fact (lw0_n_select (10 * d) k + j)
                        * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
                       (q_pow (1 # 5) j
                        * (q_fact (lw0_n_select (10 * d) k)
                           * lw0_Wb b q (lw0_n_select (10 * d) k) 0))).
  { exact (leibsep_w0n_pow b q d (lw0_n_select (10 * d) k) j Hb Hq0 Hq103 Hbd Hn0). }
  assert (Hscal : QleT' (q_pow (1 # 5) j
                         * (q_fact (lw0_n_select (10 * d) k)
                            * lw0_Wb b q (lw0_n_select (10 * d) k) 0))
                        (q_pow (1 # 5) j * 1%Q)).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (q_pow (1 # 5) j)).
    - apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. lia.
    - exact (QleT'_to_Qle _ _ Hle1). }
  assert (Htail : QleT' (q_pow (1 # 5) j) (1 # 5)).
  { destruct j as [| m].
    - exfalso. lia.
    - apply (qleT'_trans (q_pow (1 # 5) (Datatypes.S m))
                         ((1 # 5) * q_pow (1 # 5) m)
                         (1 # 5)%Q).
      + apply (qeq_leT' (q_pow (1 # 5) (Datatypes.S m))
                        ((1 # 5) * q_pow (1 # 5) m)).
        rewrite (q_pow_succ (1 # 5) m). reflexivity.
      + apply (qleT'_trans ((1 # 5) * q_pow (1 # 5) m) ((1 # 5) * 1%Q) (1 # 5)%Q).
        * apply Qle_to_QleT'.
          apply (lw0_q_mult_le_l (1 # 5)%Q).
          -- unfold Qle. cbn [Qnum Qden]. lia.
          -- apply (Qle_trans (q_pow (1 # 5) m) (q_pow 1 m) 1).
             ++ apply (q_pow_mono (1 # 5) 1 m).
                ** unfold Qle. cbn [Qnum Qden]. lia.
                ** unfold Qle. cbn [Qnum Qden]. lia.
             ++ rewrite (q_pow_one m). apply Qle_refl.
        * apply qeq_leT'. ring. }
  apply (lw0_leT'_ltT_trans
          (q_fact (lw0_n_select (10 * d) k + j)
           * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
          (q_pow (1 # 5) j) (1 # 2)).
  - apply (qleT'_trans
            (q_fact (lw0_n_select (10 * d) k + j)
             * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
            (q_pow (1 # 5) j * 1%Q)
            (q_pow (1 # 5) j)).
    + apply (qleT'_trans
              (q_fact (lw0_n_select (10 * d) k + j)
               * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
              (q_pow (1 # 5) j
               * (q_fact (lw0_n_select (10 * d) k)
                  * lw0_Wb b q (lw0_n_select (10 * d) k) 0))
              (q_pow (1 # 5) j * 1%Q)).
      * exact Hpow.
      * exact Hscal.
    + apply qeq_leT'. ring.
  - apply (lw0_leT'_ltT_trans (q_pow (1 # 5) j) (1 # 5) (1 # 2) Htail).
    apply Qlt_to_QltT. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

Print Assumptions leibsep_w0n_step.
Print Assumptions leibsep_w0n_pow.
Print Assumptions leibsep_w0n_half.


(* ---------- Slice B, first half: slack tooth / closed-branch window bridge /
   shore landing (supplied by the S56 preprocessing recon sheet) ---------- *)

(* Brick A: non-strict upper bound plus a positive slack gives a strict window. *)
Lemma leibsep_leT'_add_ltT : forall x A s : Q,
  QleT' x A -> QltT 0 s -> QltT x (A + s)%Q.
Proof.
  intros x A s Hle Hs.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans x A (A + s)%Q).
  - exact (QleT'_to_Qle x A Hle).
  - apply (leibsep_qlt_wd2 (0 + A)%Q (s + A)%Q A (A + s)%Q).
    + apply Qplus_0_l.
    + ring.
    + apply (Qplus_lt_l 0 s A).
      apply QltT_to_Qlt. exact Hs.
Qed.

(* Brick B: gate=false branch window relay (non-strict form + Brick A tooth
   onto the metric band of the window bridge). *)
Lemma leibsep_closedband_of_gate_false :
  forall (q : Q) (N : nat) (c0 s eps : Q),
    (1 <= N)%nat ->
    leibsep_gate_open q N c0 = false ->
    QltT 0 s -> QltT 0 eps ->
    sigT (fun N2 : nat => forall m : nat, NatLe N2 m ->
      QleT' (Qabs ((projT1 real_pi_geom m - q)%Q))
            ((lw0m_e N + 2 * c0 + s + lw0m_e N + eps)%Q)).
Proof.
  intros q N c0 s eps HN1 Hgate Hs Heps.
  pose proof (leibsep_gate_open_false q N c0 Hgate) as Hwin0.
  destruct (leibsep_metric_band_of_window q
             ((lw0m_e N + 2 * c0) + s)%Q N HN1
             (leibsep_leT'_add_ltT _ _ _ Hwin0 Hs) eps Heps) as [N2 HN2].
  exists N2. exact HN2.
Qed.

(* Brick C: shore upper leg (band + budget account W <= eps0 give q <= 10/3;
   abs splitting via abs-ge-self plus plus-compat, no inversion on QleT'). *)
Lemma leibsep_shore_upper :
  forall (q W eps0 : Q) (m0 : nat),
    QleT' (Qabs ((projT1 real_pi_geom m0 - q)%Q)) W ->
    Qle (projT1 real_pi_geom m0) ((10 / 3)%Q - eps0)%Q ->
    QleT' W eps0 ->
    QleT' q (10 / 3)%Q.
Proof.
  intros q W eps0 m0 Hband Hpi HW.
  pose proof (QleT'_to_Qle _ _ Hband) as Hband'.
  pose proof (QleT'_to_Qle _ _ HW) as HW'.
  assert (Hneg : (q - projT1 real_pi_geom m0)%Q
                 == (-(projT1 real_pi_geom m0 - q))%Q) by ring.
  assert (Habsopp : Qabs ((q - projT1 real_pi_geom m0)%Q)
                    == Qabs ((projT1 real_pi_geom m0 - q)%Q)).
  { rewrite Hneg. apply Qabs_opp. }
  assert (Hz : ((10 / 3)%Q - eps0 + eps0)%Q == (10 / 3)%Q) by ring.
  assert (Hsplit : q == (projT1 real_pi_geom m0
                         + (q - projT1 real_pi_geom m0))%Q) by ring.
  assert (Hst1 : (projT1 real_pi_geom m0 + (q - projT1 real_pi_geom m0))%Q
                 <= (projT1 real_pi_geom m0
                     + Qabs ((projT1 real_pi_geom m0 - q)%Q))%Q).
  { apply (Qplus_le_compat (projT1 real_pi_geom m0) (projT1 real_pi_geom m0)
             (q - projT1 real_pi_geom m0)%Q
             (Qabs ((projT1 real_pi_geom m0 - q)%Q))).
    - apply Qle_refl.
    - apply (Qle_trans (q - projT1 real_pi_geom m0)%Q
               (Qabs ((q - projT1 real_pi_geom m0)%Q))
               (Qabs ((projT1 real_pi_geom m0 - q)%Q))).
      + exact (QleT'_to_Qle _ _ (leibsep_abs_ge_self
                                  (q - projT1 real_pi_geom m0)%Q)).
      + rewrite Habsopp. apply Qle_refl. }
  assert (Hst2 : (projT1 real_pi_geom m0
                  + Qabs ((projT1 real_pi_geom m0 - q)%Q))%Q
                 <= (projT1 real_pi_geom m0 + W)%Q).
  { apply (Qplus_le_compat (projT1 real_pi_geom m0) (projT1 real_pi_geom m0)
             (Qabs ((projT1 real_pi_geom m0 - q)%Q)) W).
    - apply Qle_refl.
    - exact Hband'. }
  assert (Hfin : (projT1 real_pi_geom m0 + W)%Q <= (10 / 3)%Q).
  { apply (Qle_trans _ ((10 / 3)%Q - eps0 + eps0)%Q).
    - apply (Qplus_le_compat (projT1 real_pi_geom m0)
               ((10 / 3)%Q - eps0)%Q W eps0).
      + exact Hpi.
      + exact HW'.
    - rewrite Hz. apply Qle_refl. }
  apply Qle_to_QleT'.
  rewrite Hsplit.
  apply (Qle_trans _
          (projT1 real_pi_geom m0
           + Qabs ((projT1 real_pi_geom m0 - q)%Q))%Q).
  - exact Hst1.
  - apply (Qle_trans _ (projT1 real_pi_geom m0 + W)%Q).
    + exact Hst2.
    + exact Hfin.
Qed.

(* Brick D: real-const projection fold on the strict gap witness
   (real_lt witness form to the Q-level gap). *)
Lemma leibsep_shore_gap_of_wit :
  forall (eps0 : Q) (N0 : nat),
    (forall n : nat, NatLe N0 n ->
       QltT eps0 (projT1 (real_const (10 / 3)) n
                  - projT1 real_pi_geom n)%Q) ->
    forall m : nat, (N0 <= m)%nat ->
    QltT eps0 ((10 / 3)%Q - projT1 real_pi_geom m)%Q.
Proof.
  intros eps0 N0 H m Hm.
  pose proof (H m (NatLe_lift N0 m Hm)) as Hq.
  change (projT1 (real_const (10 / 3)) m) with (10 / 3)%Q in Hq.
  exact Hq.
Qed.

Print Assumptions leibsep_leT'_add_ltT.
Print Assumptions leibsep_closedband_of_gate_false.
Print Assumptions leibsep_shore_upper.
Print Assumptions leibsep_shore_gap_of_wit.

(* ---------- Slice B, second half: shore assembly (S56 preprocessing recon
   sheet steps 7-9): window budget / gap bridge / landing of both legs ---------- *)

(* Brick E: window budget — vanish leg e N < eps0/4 forces the closed-branch
   total width W below eps0 (multiplicative Qmake literals throughout). *)
Lemma leibsep_shore_W_le : forall eN eps0 : Q,
  QltT eN (eps0 * (1 # 4))%Q ->
  QleT' (eN + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8)) + eN + (eps0 * (1 # 8)))%Q eps0.
Proof.
  intros eN eps0 H4.
  pose proof (QltT_to_Qlt eN (eps0 * (1 # 4))%Q H4) as H4'.
  assert (H2e : Qlt (eN + eN)%Q (eps0 * (1 # 4) + eps0 * (1 # 4))%Q)
    by exact (Qplus_lt_compat eN (eps0 * (1 # 4))%Q eN (eps0 * (1 # 4))%Q H4' H4').
  assert (H2lt : Qlt (2 * eN)%Q (eps0 * (1 # 2))%Q).
  { apply (leibsep_qlt_wd2 (eN + eN)%Q (eps0 * (1 # 4) + eps0 * (1 # 4))%Q
             (2 * eN)%Q (eps0 * (1 # 2))%Q).
    - ring.
    - ring.
    - exact H2e. }
  assert (Hstep : Qlt (2 * eN + eps0 * (1 # 2))%Q (eps0 * (1 # 2) + eps0 * (1 # 2))%Q).
  { apply (Qplus_lt_le_compat (2 * eN)%Q (eps0 * (1 # 2))%Q
             (eps0 * (1 # 2))%Q (eps0 * (1 # 2))%Q H2lt).
    apply Qle_refl. }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (2 * eN + eps0 * (1 # 2))%Q).
  - apply leibsep_qeq_le. ring.
  - apply (Qle_trans _ (eps0 * (1 # 2) + eps0 * (1 # 2))%Q).
    + apply Qlt_le_weak. exact Hstep.
    + apply leibsep_qeq_le. ring.
Qed.

(* Brick F: strict gap witness to the Q-level upper bound of the sequence point. *)
Lemma leibsep_shore_gap_upper : forall eps0 x y : Q,
  QltT eps0 (x - y)%Q -> Qle y (x - eps0)%Q.
Proof.
  intros eps0 x y H.
  pose proof (QltT_to_Qlt eps0 (x - y)%Q H) as Hq.
  assert (H1 : Qlt (eps0 + y)%Q ((x - y) + y)%Q)
    by exact (proj2 (Qplus_lt_l eps0 (x - y)%Q y) Hq).
  assert (H2 : Qlt (y + eps0)%Q x%Q).
  { apply (leibsep_qlt_wd2 (eps0 + y)%Q ((x - y) + y)%Q (y + eps0)%Q x%Q).
    - ring.
    - ring.
    - exact H1. }
  assert (H3 : Qlt (y + eps0)%Q ((x - eps0) + eps0)%Q).
  { apply (leibsep_qlt_wd2 (y + eps0)%Q x%Q (y + eps0)%Q ((x - eps0) + eps0)%Q).
    - apply Qeq_refl.
    - ring.
    - exact H2. }
  apply Qlt_le_weak.
  exact (proj1 (Qplus_lt_l y (x - eps0)%Q eps0) H3).
Qed.

(* Brick G: shore landing, upper leg — gap witness + vanish budget + closed
   gate-false window force q <= 10/3. *)
Lemma leibsep_shore_q_le_ten_thirds :
  forall (q eps0 : Q) (N0 Nv : nat),
    QltT 0 eps0 ->
    (forall n : nat, NatLe N0 n ->
       QltT eps0 (projT1 (real_const (10 / 3)) n - projT1 real_pi_geom n)%Q) ->
    (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
    leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q = false ->
    QleT' q (10 / 3)%Q.
Proof.
  intros q eps0 N0 Nv Hpos Hgap Hvan Hgate.
  assert (HNw1 : (1 <= Nat.max Nv 1)%nat) by lia.
  assert (Hpos8 : QltT 0 (eps0 * (1 # 8))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 8)%Q).
    - apply QltT_to_Qlt. exact Hpos.
    - compute. reflexivity. }
  destruct (leibsep_closedband_of_gate_false q (Nat.max Nv 1) (eps0 * (1 # 8))%Q
             (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q HNw1 Hgate Hpos8 Hpos8) as [N2 HN2].
  pose proof (Hvan (Nat.max Nv 1) (Nat.le_max_l Nv 1)) as HvNw.
  pose proof (leibsep_shore_W_le (lw0m_e (Nat.max Nv 1)) eps0 HvNw) as HW.
  assert (Hm2 : (N2 <= Nat.max N2 (Nat.max N0 1))%nat) by lia.
  assert (Hm0 : (N0 <= Nat.max N2 (Nat.max N0 1))%nat) by lia.
  pose proof (HN2 (Nat.max N2 (Nat.max N0 1))
              (NatLe_lift N2 (Nat.max N2 (Nat.max N0 1)) Hm2)) as Hband.
  pose proof (leibsep_shore_gap_of_wit eps0 N0 Hgap
              (Nat.max N2 (Nat.max N0 1)) Hm0) as Hgapm.
  pose proof (leibsep_shore_gap_upper eps0 (10 / 3)%Q
              (projT1 real_pi_geom (Nat.max N2 (Nat.max N0 1))) Hgapm) as Hpi.
  exact (leibsep_shore_upper q _ eps0 (Nat.max N2 (Nat.max N0 1)) Hband Hpi HW).
Qed.

(* Brick H: shore landing, lower leg — the same budget plus the 3 < pi bound
   forces 0 < q (gap witness itself pins eps0 < 3). *)
Lemma leibsep_shore_q_pos :
  forall (q eps0 : Q) (N0 Nv : nat),
    QltT 0 eps0 ->
    (forall n : nat, NatLe N0 n ->
       QltT eps0 (projT1 (real_const (10 / 3)) n - projT1 real_pi_geom n)%Q) ->
    (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
    leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q = false ->
    QltT 0 q.
Proof.
  intros q eps0 N0 Nv Hpos Hgap Hvan Hgate.
  destruct real_pi_geom_gt_three as [eps1 [Heps1 [N1 HN1]]].
  assert (HNw1 : (1 <= Nat.max Nv 1)%nat) by lia.
  assert (Hpos8 : QltT 0 (eps0 * (1 # 8))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 8)%Q).
    - apply QltT_to_Qlt. exact Hpos.
    - compute. reflexivity. }
  destruct (leibsep_closedband_of_gate_false q (Nat.max Nv 1) (eps0 * (1 # 8))%Q
             (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q HNw1 Hgate Hpos8 Hpos8) as [N2 HN2].
  pose proof (Hvan (Nat.max Nv 1) (Nat.le_max_l Nv 1)) as HvNw.
  pose proof (leibsep_shore_W_le (lw0m_e (Nat.max Nv 1)) eps0 HvNw) as HW.
  assert (Hm2 : (N2 <= Nat.max N2 (Nat.max (Nat.max N0 N1) 1))%nat) by lia.
  assert (Hm0 : (N0 <= Nat.max N2 (Nat.max (Nat.max N0 N1) 1))%nat) by lia.
  assert (Hm1 : (N1 <= Nat.max N2 (Nat.max (Nat.max N0 N1) 1))%nat) by lia.
  pose proof (HN2 (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
              (NatLe_lift N2 (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) Hm2)) as Hband.
  pose proof (leibsep_shore_gap_of_wit eps0 N0 Hgap
              (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) Hm0) as Hgapm.
  pose proof (HN1 (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
              (NatLe_lift N1 (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) Hm1)) as Hgt.
  change (projT1 (real_const 3) (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))
    with 3%Q in Hgt.
  pose proof (QltT_to_Qlt _ _ Hgapm) as Hgapq.
  pose proof (QltT_to_Qlt _ _ Hgt) as Hgtq.
  assert (Hgt3 : Qlt 3%Q (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q).
  { assert (Hgt2 : Qlt (3 + eps1)%Q
               (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q).
    { apply (leibsep_qlt_wd2 (eps1 + 3)%Q
               (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - 3%Q + 3%Q)%Q
               (3 + eps1)%Q
               (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q).
      - ring.
      - ring.
      - exact (proj2 (Qplus_lt_l eps1 _ 3%Q) Hgtq). }
    apply (Qlt_trans 3%Q (3 + eps1)%Q _).
    - apply (leibsep_qlt_wd2 (0 + 3)%Q (eps1 + 3)%Q 3%Q (3 + eps1)%Q).
      + ring.
      + ring.
      + exact (proj2 (Qplus_lt_l 0%Q eps1 3%Q) (QltT_to_Qlt _ _ Heps1)).
    - exact Hgt2. }
  assert (Hanti : Qlt ((10 / 3)%Q
                  - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q
                  ((10 / 3)%Q - 3%Q)%Q).
  { pose proof (Qopp_lt_compat 3%Q
        (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))) Hgt3) as Hopp.
    apply (leibsep_qlt_wd2 (Qopp (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))
                            + (10 / 3)%Q)%Q
               (Qopp 3%Q + (10 / 3)%Q)%Q
               ((10 / 3)%Q
                - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q
               ((10 / 3)%Q - 3%Q)%Q).
    - ring.
    - ring.
    - exact (proj2 (Qplus_lt_l _ _ (10 / 3)%Q) Hopp). }
  assert (Hep : Qlt eps0 ((10 / 3)%Q - 3%Q)%Q)
    by exact (Qlt_trans eps0 _ _ Hgapq Hanti).
  assert (Hnum : Qlt ((10 / 3)%Q - 3%Q)%Q 3%Q).
  { apply (leibsep_qlt_wd2 (1 # 3)%Q 3%Q ((10 / 3)%Q - 3%Q)%Q 3%Q).
    - field.
    - apply Qeq_refl.
    - compute. reflexivity. }
  assert (Hep3 : Qlt eps0 3%Q) by exact (Qlt_trans eps0 _ _ Hep Hnum).
  (* band lower side: 3 - eps0 <= pi m0 - W <= q *)
  assert (Hbandq : Qle (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q))
                       (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                        + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8)))%Q)
    by exact (QleT'_to_Qle _ _ Hband).
  assert (HWq : Qle (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                     + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8)))%Q eps0)
    by exact (QleT'_to_Qle _ _ HW).
  assert (T2abs : Qabs ((q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q)
                  == Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)).
  { assert (Hneg : (q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q
                   == (-(projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q))%Q) by ring.
    rewrite Hneg. apply Qabs_opp. }
  assert (Hlow1 : QleT' (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                         + Qopp (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)))%Q q).
  { assert (E1 : (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                  + Qopp (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)))%Q
                 == (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                  + Qopp (Qabs ((q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q)))%Q).
    { rewrite T2abs. reflexivity. }
    assert (E2 : (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                  + (q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q)%Q
                 == q%Q) by ring.
    apply (qleT'_trans _ (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
            + Qopp (Qabs ((q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q)))%Q).
    - apply qeq_leT'. exact E1.
    - apply (qleT'_trans _ (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
              + (q - projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q)%Q).
      + apply qleT'_plus_compat.
        * apply qleT'_refl.
        * apply leibsep_abs_ge_opp.
      + apply qeq_leT'. exact E2. }
  assert (S4 : QleT' (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                    + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                     + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q
                (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)))%Q).
  { apply qleT'_plus_compat.
    - apply qleT'_refl.
    - apply lw0_opp_le_swap. exact Hband. }
  pose proof (QleT'_to_Qle _ _ S4) as S4q.
  pose proof (QleT'_to_Qle _ _ Hlow1) as Hlow1q.
  assert (S1 : Qle (3%Q + Qopp eps0)%Q
                (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                  + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
  { apply (Qplus_le_compat 3%Q
             (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q).
    - apply Qlt_le_weak. exact Hgt3.
    - apply (QleT'_to_Qle _ _ (lw0_opp_le_swap _ _ HW)). }
  assert (S2 : Qle (3%Q - eps0)%Q (3%Q + Qopp eps0)%Q)
    by (apply leibsep_qeq_le; ring).
  assert (S3 : Qle (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                 + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q
                (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)))%Q)
    by exact S4q.
  assert (Salt : Qle (3%Q - eps0)%Q q).
  { apply (Qle_trans _ (3%Q + Qopp eps0)%Q).
    - exact S2.
    - apply (Qle_trans _ (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
               + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
      + exact S1.
      + apply (Qle_trans _ (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp (Qabs ((projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)) - q)%Q)))%Q).
        * exact S3.
        * exact Hlow1q. }
  assert (Hpos03 : Qlt 0%Q (3%Q - eps0)%Q).
  { assert (Hlt1 : Qlt (eps0 + Qopp 3%Q)%Q (3%Q + Qopp 3%Q)%Q)
      by exact (proj2 (Qplus_lt_l eps0 3%Q (Qopp 3%Q)) Hep3).
    assert (Hlt2 : Qlt (eps0 - 3%Q)%Q 0%Q).
    { apply (leibsep_qlt_wd2 (eps0 + Qopp 3%Q)%Q (3%Q + Qopp 3%Q)%Q
               (eps0 - 3%Q)%Q 0%Q); [ring | ring | exact Hlt1]. }
    pose proof (Qopp_lt_compat (eps0 - 3%Q)%Q 0%Q Hlt2) as Hneg.
    apply (leibsep_qlt_wd2 (Qopp 0%Q)%Q (Qopp (eps0 - 3%Q)%Q) 0%Q (3%Q - eps0)%Q).
    - ring.
    - ring.
    - exact Hneg. }
  assert (Hf1 : Qlt (3%Q - eps0)%Q
                 (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                  + Qopp eps0)%Q).
  { apply (leibsep_qlt_wd2 (3%Q + Qopp eps0)%Q
             (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
              + Qopp eps0)%Q
             (3%Q - eps0)%Q
             (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
              + Qopp eps0)%Q).
    - ring.
    - apply Qeq_refl.
    - exact (proj2 (Qplus_lt_l 3%Q
                      (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))
                      (Qopp eps0)) Hgt3). }
  assert (Hf2 : Qle (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp eps0)%Q
                (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1))
                 + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                  + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
  { apply (Qplus_le_compat (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q
             (projT1 real_pi_geom (Nat.max N2 (Nat.max (Nat.max N0 N1) 1)))%Q).
    - apply Qle_refl.
    - exact (QleT'_to_Qle _ _ (lw0_opp_le_swap _ _ HW)). }
  apply Qlt_to_QltT.
  exact (Qlt_trans 0%Q (3%Q - eps0)%Q _ Hpos03
          (Qlt_le_trans _ _ _ Hf1
             (Qle_trans _ _ _ Hf2 (Qle_trans _ _ _ S4q Hlow1q)))).
Qed.

Print Assumptions leibsep_shore_W_le.
Print Assumptions leibsep_shore_gap_upper.
Print Assumptions leibsep_shore_q_le_ten_thirds.
Print Assumptions leibsep_shore_q_pos.

(* ---------- P 槽 Hratio 前提的比率上界引理 ---------- *)

(* |q| ≤ q_of_nat d0 ⟹ j ≥ d0 时 2·|q|² ≤ (2j+1)(2j+2)：
   P1/P2 槽 Hratio 前提（M := d0）的直接可用形；nat 侧不等式走
   Nat.mul_le_mono 显式四参链（2d0² ≤ 2j² ≤ (2j)·j ≤ (2j+1)(2j+2)，
   线性分支 lia 收尾），无需 1 ≤ d0 前提。 *)
Lemma leibsep_ratio_slot : forall (q : Q) (d0 : nat),
  QleT' (Qabs q) (lw0_q_of_nat d0) ->
  forall j : nat, (d0 <= j)%nat ->
  QleT' (2 * q_pow (Qabs q) 2)%Q
        (lw0_q_of_nat (Datatypes.S (2 * j))
         * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q.
Proof.
  intros q d0 Habs j Hj.
  assert (Htwo : QleT' 0 2%Q).
  { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden]. lia. }
  assert (Hmono : QleT' (q_pow (Qabs q) 2) (q_pow (lw0_q_of_nat d0) 2)).
  { apply Qle_to_QleT'. apply q_pow_mono.
    - apply Qabs_nonneg.
    - apply QleT'_to_Qle. exact Habs. }
  assert (Hsq2 : q_pow (lw0_q_of_nat d0) 2 == lw0_q_of_nat d0 * lw0_q_of_nat d0).
  { cbn [q_pow]. ring. }
  assert (Hstep1 : QleT' (2 * q_pow (Qabs q) 2) (2 * q_pow (lw0_q_of_nat d0) 2)).
  { apply qleT'_mult_compat_l; [exact Htwo | exact Hmono]. }
  assert (Hstep2 : (2 * q_pow (lw0_q_of_nat d0) 2)%Q
                   == lw0_q_of_nat (2 * (d0 * d0))%nat).
  { rewrite Hsq2. change (2%Q) with (lw0_q_of_nat 2).
    rewrite (lw0_pitS_qof_mul 2 (d0 * d0)).
    rewrite (lw0_pitS_qof_mul d0 d0).
    reflexivity. }
  assert (Hstep3 : QleT' (lw0_q_of_nat (2 * (d0 * d0))%nat)
                         (lw0_q_of_nat (Datatypes.S (2 * j)
                                        * Datatypes.S (Datatypes.S (2 * j)))%nat)).
  { apply lw0_q_of_nat_le_mono.
    apply Nat.le_trans with (m := ((2 * j) * j)%nat).
    - apply Nat.le_trans with (m := (2 * (j * j))%nat).
      + apply Nat.mul_le_mono_l. exact (Nat.mul_le_mono d0 j d0 j Hj Hj).
      + rewrite (Nat.mul_assoc 2 j j). apply Nat.le_refl.
    - apply (Nat.mul_le_mono (2 * j) (Datatypes.S (2 * j)) j
               (Datatypes.S (Datatypes.S (2 * j)))); lia. }
  apply (qleT'_trans _ (lw0_q_of_nat (2 * (d0 * d0))%nat) _).
  - apply (qleT'_trans _ (2 * q_pow (lw0_q_of_nat d0) 2)%Q _).
    + exact Hstep1.
    + apply qeq_leT'. exact Hstep2.
  - apply (qleT'_trans _ (lw0_q_of_nat (Datatypes.S (2 * j)
                                        * Datatypes.S (Datatypes.S (2 * j)))%nat) _).
    + exact Hstep3.
    + apply qeq_leT'. apply lw0_pitS_qof_mul.
Qed.

(* ---------- select 下界引理 ---------- *)

(* select 展开 22 + 2·max k b ≥ 22 ⟹ 任意偏移步数下仍 ≥ 2：
   K2 前提 (2 ≤ n) 的直接可用形。 *)
Lemma leibsep_nsel_bound : forall (b k j : nat),
  (2 <= lw0_n_select b k + j)%nat.
Proof.
  intros b k j. unfold lw0_n_select. lia.
Qed.


(* ---------- K2 装配形（显式命名前提，双槽） ---------- *)

(* β 挤压矛盾引擎的 false 支装配形：q 的两界（QltT 0 q 与 q ≤ 10/3）
   与 P1/P2 槽结论（s/t/M0）为外部接口前提；半量界 Hup 由 w0n_half
   （j ≥ 1，b := q 的分母钉界）与修正项预算（槽 A）合成；
   Hlow（槽 B）为显式命名前提。两槽各由其定量供给逐段消去
   （槽 A 由 F 界预算消去，槽 B 由 K1/G4b 组装消去）。语句面逐字对齐
   leibsep_beta_contra 的 Hup/Hlow 形（lw0_F 双参：多项式与截断阶）。 *)
Lemma leibsep_false_branch_contra :
  forall (q : Q) (k j : nat) (s t : Q) (M0 : nat) (eps : Q),
  QltT 0 q ->
  QleT' q (10 / 3)%Q ->
  QltT 0 eps ->
  (1 <= j)%nat ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                           (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)) q) * t
         + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                  (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))) q) * s
         + eps)%Q
        (1 # 2)%Q ->
  QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                            (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                          (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)) q) * t
        + Qabs (qpoly_eval (qpoly_deriv
                 (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                   (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                 (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))) q) * s
        + eps)%Q
       (q_fact (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)
        * (lw0_Wb (Zpos (Qden q) # 1)%Q q
             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j) 0%nat
           - lw0_Wb (Zpos (Qden q) # 1)%Q q
             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j) 1%nat))%Q ->
  Id false true.
Proof.
  intros q k j s t M0 eps Hq Hq103 Heps Hj Hs Ht HCA HCB.
  pose (b := (Zpos (Qden q) # 1)%Q).
  pose (n0 := (lw0_n_select (10 * lw0_pi_d0_of b) k + j)%nat).
  pose (C := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b n0) n0) q) * t
             + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b n0) n0)) q) * s
             + eps)%Q).
  assert (Hbh : QltT 0 b) by apply lw0_pi_b_den_pos.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Hbabs : b == Qabs b).
  { symmetry. apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hbh. }
  assert (Hbd0 : QleT' b (lw0_q_of_nat (lw0_pi_d0_of b))).
  { apply (qleT'_trans _ (Qabs b) _).
    - apply qeq_leT'. exact Hbabs.
    - apply lw0_pi_d0_absorb. exact (qeq_ltT b (Qabs b) Hbabs Hbh). }
  assert (Hn : (2 <= n0)%nat).
  { unfold n0. unfold lw0_n_select. lia. }
  assert (Hv : QltT (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q).
  { exact (leibsep_w0n_half b q (lw0_pi_d0_of b) k j Hbh Hq0 Hq103 Hbd0 Hj). }
  assert (Hup : QltT (q_fact n0 * lw0_Wb b q n0 0 + C)%Q 1%Q).
  { apply Qlt_to_QltT.
    assert (Hvlt : Qlt (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by (apply QltT_to_Qlt; exact Hv).
    assert (HvC : Qlt (q_fact n0 * lw0_Wb b q n0 0 + C)%Q ((1 # 2) + C)%Q).
    { exact (proj2 (Qplus_lt_l (q_fact n0 * lw0_Wb b q n0 0) (1 # 2)%Q C) Hvlt). }
    assert (HleC : Qle ((1 # 2) + C)%Q 1%Q).
    { apply QleT'_to_Qle.
      apply (qleT'_trans _ ((1 # 2) + (1 # 2))%Q _).
      - apply qleT'_plus_compat; [apply qleT'_refl | exact HCA].
      - apply qeq_leT'. ring. }
    exact (Qlt_le_trans _ _ _ HvC HleC). }
  exact (leibsep_beta_contra q n0 s t M0 eps Hbh Hq Hq103 Hn Hs Ht Heps Hup HCB).
Qed.

Print Assumptions leibsep_ratio_slot.
Print Assumptions leibsep_nsel_bound.
Print Assumptions leibsep_false_branch_contra.

(* two-positivity sum for Qlt (auxiliary bookkeeping lemma) *)
(* two-positives sum for Qlt (auxiliary bookkeeping lemma) *)
Lemma qlt0_plus : forall a b : Q, Qlt 0 a -> Qlt 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  apply (Qlt_trans 0 b (a + b)%Q Hb).
  exact (leibsep_qlt_wd2 (0 + b)%Q (a + b)%Q b (a + b)%Q
           (Qplus_0_l b) (Qeq_refl (a + b)%Q)
           (proj2 (Qplus_lt_l 0 a b) Ha)).
Qed.

Lemma leibsep_q_kernel_gate_carrier :
  forall (q : Q) (eps0 : Q) (N0 Nv : nat) (s t : Q) (M0 : nat),
  QltT 0 eps0 ->
  (forall n : nat, NatLe N0 n ->
     QltT eps0 (projT1 (real_const (10 / 3)) n - projT1 real_pi_geom n)%Q) ->
  (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
     QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)) q) * t
          + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))) q) * s
          + eps0 * (1 # 8))%Q (1 # 2)%Q ->
     QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)) q) * t
          + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))) q) * s
          + eps0 * (1 # 8))%Q
         (q_fact ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)
        * (lw0_Wb (Zpos (Qden q) # 1)%Q q ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat) 0%nat
         - lw0_Wb (Zpos (Qden q) # 1)%Q q ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat) 1%nat))%Q ->
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun N : nat => forall m : nat, NatLe N m ->
      QltT c (Qabs ((lw0m_xL m - q)%Q))))).
Proof.
  intros q eps0 N0 Nv s t M0 Heps0 HN0 HNv Hs Ht HP1 HP2.
  assert (HN1 : (1 <= Nat.max Nv 1)%nat) by lia.
  assert (Hc8lt : Qlt 0 (eps0 * (1 # 8)))
    by (apply (Qmult_lt_0_compat eps0 (1 # 8));
        [ apply QltT_to_Qlt; exact Heps0 | vm_compute; reflexivity ]).
  assert (Hc8ltT : QltT 0 (eps0 * (1 # 8))%Q) by (apply Qlt_to_QltT; exact Hc8lt).
  assert (Hj01 : (1 <= 1)%nat) by lia.
  destruct (leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q) eqn:Egate.
  - (* gate true: guarded kernel with witness c := 2*c0 *)
    assert (Hcpos : QltT 0 (2 * (eps0 * (1 # 8)))%Q).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 (eps0 * (1 # 8)));
        [ vm_compute; reflexivity | exact Hc8lt ]. }
    assert (Hguard : QltT (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL (Nat.max Nv 1) - q)%Q)))
      by (apply leibsep_gate_open_true; exact Egate).
    destruct (leibsep_q_kernel_guarded q (Nat.max Nv 1) (eps0 * (1 # 8))%Q HN1 Hguard)
      as [M HM].
    exists (2 * (eps0 * (1 # 8)))%Q. split.
    + exact Hcpos.
    + exists M. exact HM.
  - (* gate false: shore double-landing + P1/P2 slots + w0n_half + slot A/B *)
    assert (Hq103 : QleT' q (10 / 3)%Q)
      by exact (leibsep_shore_q_le_ten_thirds q eps0 N0 Nv Heps0 HN0 HNv Egate).
    assert (Hq : QltT 0 q)
      by exact (leibsep_shore_q_pos q eps0 N0 Nv Heps0 HN0 HNv Egate).
    assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
    pose (b := (Zpos (Qden q) # 1)%Q).
    pose (n0 := ((lw0_n_select (10 * lw0_pi_d0_of b) 0 + 1)%nat)).
    assert (Hbh : QltT 0 b) by apply lw0_pi_b_den_pos.
    assert (Hbabs : b == Qabs b).
    { symmetry. apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hbh. }
    assert (Hbd0 : QleT' b (lw0_q_of_nat (lw0_pi_d0_of b))).
    { apply (qleT'_trans b (Qabs b) (lw0_q_of_nat (lw0_pi_d0_of b))).
      - apply qeq_leT'. exact Hbabs.
      - apply lw0_pi_d0_absorb. exact (qeq_ltT b (Qabs b) Hbabs Hbh). }
    assert (Hv : QltT (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by exact (leibsep_w0n_half b q (lw0_pi_d0_of b) 0 1 Hbh Hq0 Hq103 Hbd0 Hj01).
    (* upper composite C: the endpoint caps s and t enter as premises *)
    pose (C := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b n0) n0) q) * t
              + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b n0) n0)) q) * s
              + (eps0 * (1 # 8))%Q)%Q).
    assert (HCA : QleT' C (1 # 2)%Q)
      by exact HP1.
    assert (Hvlt : Qlt (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by (apply QltT_to_Qlt; exact Hv).
    assert (HvC : Qlt (q_fact n0 * lw0_Wb b q n0 0 + C)%Q ((1 # 2) + C)%Q)
      by exact (proj2 (Qplus_lt_l (q_fact n0 * lw0_Wb b q n0 0) (1 # 2)%Q C) Hvlt).
    assert (HleC : Qle ((1 # 2) + C)%Q 1%Q).
    { apply QleT'_to_Qle.
      apply (qleT'_trans ((1 # 2) + C)%Q ((1 # 2) + (1 # 2))%Q 1%Q).
      - apply qleT'_plus_compat; [apply qleT'_refl | exact HCA].
      - apply qeq_leT'. ring. }
    assert (Hup : QltT (q_fact n0 * lw0_Wb b q n0 0 + C)%Q 1%Q)
      by (apply Qlt_to_QltT; exact (Qlt_le_trans _ _ _ HvC HleC)).
    assert (HCB : QltT C (q_fact n0 * (lw0_Wb b q n0 0%nat - lw0_Wb b q n0 1%nat))%Q)
      by exact HP2.
    assert (Hcontra : Id false true).
    { exact (leibsep_false_branch_contra q 0 1 s t M0
             (eps0 * (1 # 8))%Q Hq Hq103 Hc8ltT Hj01 Hs Ht HCA HCB). }
    discriminate Hcontra || inversion Hcontra.
Qed.


Print Assumptions qlt0_plus.
Print Assumptions leibsep_q_kernel_gate_carrier.
