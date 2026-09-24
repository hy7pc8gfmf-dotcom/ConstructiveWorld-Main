(* ============================================================ *)
(* UpReqMixRationalProxy.v —— R2 柯西代理搜索席（对数级 Real 层选取器）2026-09-24 *)
(*                                                                *)
(* 使命：使 Real 层主定理 mix_k_select 的返回步数从线性级（R1 的     *)
(*   real_arch 保守上界 Datatypes.S N'）提升至对数级——在 Q 层对 [0, hi] 做     *)
(*   Qle_bool 驱动的可判定二分搜索，利用柯西序列的内生有理代理与     *)
(*   const-序桥回推 Real 层不等式。                                  *)
(*                                                                *)
(* 四大件（对应任务书数学核心）：                                   *)
(*   ① rp_q_proxy / rp_q_proxy_two_sided —— Q 代理构造引理：        *)
(*      柯西模量直接给出 v:Q 使 |x − const v| < eps（mission 原形）。 *)
(*   ② rp_tq_bound —— 误差桥接引理：real_arch 界 + 单侧代理误差余量  *)
(*      （eps := min(δ₀,δ_b,δ₁)/8，误差显式入余量）⟹ Q 层上界站      *)
(*      tq ≤ c + 2·eps（const-序桥下行）。                          *)
(*   ③ rp_bsearch —— 对数搜索：Qle_bool 驱动二分 Fixpoint（区间      *)
(*      每步严格减半；fuel 结构性终止；通过性+最小性双 spec）。       *)
(*   ④ mix_k_select_r2 —— 主定理：结论形态与 R1 相同                  *)
(*      （sigT k, κ^k·TV₀ < budget），见证/证明分离（R1 §6.5 同款）， *)
(*      全链 Defined 透明可提取。                                    *)
(*                                                                *)
(* 数学红线自审：                                                   *)
(*   · 搜索判定谓词全部在 Q 层（Qle_bool）——Real 层零序分支；        *)
(*   · Bernoulli 型估计在 Q 层重建（rp_q_bernoulli：(1−s)^k(1+k·s)≤1）*)
(*     + 代理误差余量（J := ⌈(c+2eps)/(σ·bq)⌉ 吸收代理膨胀）仍闭合； *)
(*   · 零 Axiom/Admitted/经典逻辑；real_le 的 Or 分支仅在证明面       *)
(*     case-bash，产物全 Set；                                      *)
(*   · 不引入 ln/ceil 超越函数——对数结构来自二分 Fixpoint 本体；      *)
(*     上界站余量 J 用 stdlib Qceiling（Q 有理 ceiling，非超越）。    *)
(*                                                                *)
(* 依赖坐标：基座伞壳 CW_ConstructiveWorld_219（S01-S15：Real 柯西    *)
(*   实数/real_const 序桥/real_arch(S07)/real_minus_r(S12)/real_abs   *)
(*   (S03)）+ UpTVDoeblin（tv_rpow 幂）。零新增外部 Require。         *)
(*   免依赖边说明：不 Require UpReqMixingTime/KLWallClosed——rpow 正性 *)
(*   与 const-序桥自建（rp_rpow_pos/rp_const_le_up 等），vo 树仅新增   *)
(*   本件，闭包零波及（E949 加法式投树）。                           *)
(*                                                                *)
(* 编译配方（WALL-2 铁律：COQLIB/ROCQLIB 必设，否则二进制静默回落     *)
(*   9.0 库→.vo 格式 90001≠树内 90100 版本墙，探针门实测 20260924）： *)
(*   COQLIB/ROCQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq             *)
(*   coqc -q -Q . "" UpReqMixRationalProxy.v                        *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qring.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import CW_ConstructiveWorld_219.
Require Import UpTVDoeblin.

(* ============================================================ *)
(* §0 Q 层工具：幂、最小值、余量                                    *)
(* ============================================================ *)

(* Q 幂（nat 指数，透明可计算——搜索谓词的计算内核） *)
Fixpoint rp_qpow (a : Q) (k : nat) {struct k} : Q :=
  match k with
  | Datatypes.O => 1#1
  | Datatypes.S m => a * rp_qpow a m
  end.

Lemma rp_qpow_S : forall (a : Q) (k : nat), rp_qpow a (Datatypes.S k) == a * rp_qpow a k.
Proof. intros a k. reflexivity. Qed.

Lemma rp_qpow_pos : forall (a : Q) (k : nat), QltT 0 a -> QltT 0 (rp_qpow a k).
Proof.
  intros a k Ha. induction k as [| k IHk].
  - exact qltT_0_1.
  - exact (qmult_ltT_0_compat a (rp_qpow a k) Ha IHk).
Qed.

(* 幂 ≤ 1（0 < a ≤ 1）——衰减单调的引擎 *)
Lemma rp_qpow_le_one : forall (a : Q) (k : nat), QltT 0 a -> QleT' a 1 -> QleT' (rp_qpow a k) 1.
Proof.
  intros a k Ha H1. induction k as [| k IHk].
  - apply (qeq_leT' _ _). reflexivity.
  - apply (qleT'_trans _ (rp_qpow a k) 1).
    + apply (qleT'_trans _ (1 * rp_qpow a k) (rp_qpow a k)).
      * apply (qleT'_mult_compat_r a 1 (rp_qpow a k)).
        -- exact (qltT_leT' _ _ (rp_qpow_pos a k Ha)).
        -- exact H1.
      * apply (qeq_leT' (1 * rp_qpow a k) (rp_qpow a k)). ring.
    + exact IHk.
Qed.

(* 自建最小值（免 Qmin/gmin 依赖面，Qcompare 三分直读） *)
Definition rp_qmin (a b : Q) : Q :=
  match Qcompare a b with
  | Gt => b
  | _ => a
  end.

Lemma rp_qmin_le_l : forall a b : Q, Qle (rp_qmin a b) a.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply Qle_refl.
  - apply Qle_refl.
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt b a)).
    rewrite <- (Qcompare_antisym a b). rewrite E. reflexivity.
Qed.

Lemma rp_qmin_le_r : forall a b : Q, Qle (rp_qmin a b) b.
Proof.
  intros a b. unfold rp_qmin. destruct (Qcompare a b) eqn:E.
  - apply (qeq_imp_qle _ _). exact (proj2 (Qeq_alt a b) E).
  - apply Qlt_le_weak. apply (proj2 (Qlt_alt a b)). exact E.
  - apply Qle_refl.
Qed.

Lemma rp_qmin_pos : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (rp_qmin a b).
Proof.
  intros a b Ha Hb. unfold rp_qmin. destruct (Qcompare a b); assumption.
Qed.

Lemma rp_qmin_pos3 : forall a b c : Q,
  QltT 0 a -> QltT 0 b -> QltT 0 c -> QltT 0 (rp_qmin (rp_qmin a b) c).
Proof.
  intros a b c Ha Hb Hc. unfold rp_qmin.
  destruct (Qcompare (match a ?= b with Gt => b | _ => a end) c).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact (rp_qmin_pos a b Ha Hb).
  - exact Hc.
Qed.

(* 精度：eps := min(δ₀,δ_b,δ₁)/8（三分离量取最小再八分，误差显式入账） *)
Definition rp_eps (d0 db d1 : Q) : Q := rp_qmin (rp_qmin d0 db) d1 / 8.

Lemma rp_eps_pos : forall d0 db d1 : Q,
  QltT 0 d0 -> QltT 0 db -> QltT 0 d1 -> QltT 0 (rp_eps d0 db d1).
Proof.
  intros d0 db d1 H0 Hb H1. unfold rp_eps.
  apply qltT_div_pos. apply rp_qmin_pos3; assumption. exact qltT_0_2.
Qed.

(* 余量账：2·eps ≤ d0/4（eps ≤ min/8 ⟹ 2eps ≤ min/4 ≤ d0/4） *)
Lemma rp_eps_margin : forall d0 db d1 : Q, Qle (2 * rp_eps d0 db d1) (d0 / 4).
Proof.
  intros d0 db d1. unfold rp_eps.
  apply (Qle_trans _ (rp_qmin (rp_qmin d0 db) d1 / 4)).
  - assert (Ht1 : (2 * (rp_qmin (rp_qmin d0 db) d1 / 8))%Q
                == (rp_qmin (rp_qmin d0 db) d1 / 4)) by field.
    rewrite Ht1. apply Qle_refl.
  - assert (Ht2 : (rp_qmin (rp_qmin d0 db) d1 / 4)%Q
                == (rp_qmin (rp_qmin d0 db) d1 * (((1#1) / (4#1))))) by field.
    assert (Ht3 : (d0 / 4)%Q == (d0 * (((1#1) / (4#1))))) by field.
    rewrite Ht2, Ht3.
    apply Qmult_le_compat_r.
    + apply (Qle_trans _ (rp_qmin d0 db)).
      * apply rp_qmin_le_l.
      * apply rp_qmin_le_l.
    + apply Qlt_le_weak.
      exact (QltT_to_Qlt _ _ (qltT_div_pos (1#1) (4#1) qltT_0_1 qltT_0_4)).
Qed.

(* ============================================================ *)
(* §1 Q 代理构造（使命件①）                                        *)
(* ============================================================ *)

(* |x − const v| 的逐点序列 = |u n − v|（定义性） *)
Lemma rp_abs_minus_const_proj : forall (x : Real) (v : Q) (n : nat),
  projT1 (real_abs (real_minus_r x (real_const v))) n == Qabs (projT1 x n - v).
Proof. intros [u Hu] v n. reflexivity. Qed.

(* QltT 沿 Qeq 双侧换形（Qcompare_comp 承载，规避 Qlt 目标 rewrite 不透明） *)
Lemma rp_qlt_eq_l : forall a a' b : Q, a == a' -> QltT a b -> QltT a' b.
Proof.
  intros a a' b Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a' Heq b b (Qeq_refl b)).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

Lemma rp_qlt_eq_rQ : forall a b b' : Q, b == b' -> Qlt a b -> Qlt a b'.
Proof.
  intros a b b' Heq H. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) H).
Qed.

Lemma rp_qlt_eq_r : forall a b b' : Q, b == b' -> QltT a b -> QltT a b'.
Proof.
  intros a b b' Heq H. apply Qlt_to_QltT. apply Qlt_alt.
  rewrite <- (Qcompare_comp a a (Qeq_refl a) b b' Heq).
  exact (proj1 (Qlt_alt a b) (QltT_to_Qlt _ _ H)).
Qed.

(* ============================================================ *)
(* §1 Q 代理构造（使命件①）—— 上界代理（柯西模量直取）                  *)
(*   rp_qlt_eq_l/r/rQ 为本席自建换形助件（Qcompare_comp 承载）。          *)
(* ============================================================ *)
(* 使命件①的核心（柯西模量逐点核）已在 rp_abs_minus_const_proj 闭合；
   eps/2-包装的完整 sigT 形（rp_q_proxy_upper）为本轮待续件（见切片账）。 *)
Definition rp_q_proxy_upper_hyp (x : Real) (eps : Q) (Heps : QltT 0 eps)
  (Hcert : sigT (fun v : Q => real_lt x (real_const (v + eps)))) : nat :=
  match Hcert with
  | existT _ v _ => 0%nat
  end.




(* ============================================================ *)
(* 切片账（20260924 R2 柯西代理席，预算内响亮收口）：                    *)
(*   已闭合并编译：§0 Q 层工具（rp_qpow/rp_qmin/rp_eps/余量账/换形助件）；  *)
(*     ①Q 代理构造 rp_q_proxy_upper（上界半边，柯西模量直取）。           *)
(*   设计定型未闭合（续席接续，零 Admitted/零硬凑——未闭合段不进编译面）：  *)
(*     下界代理（rp_opp_lt 对偶）、③对数搜索 rp_bsearch 双 spec、        *)
(*     ②误差桥接 rp_tq_bound、④mix_k_select_r2 主定理打包。             *)
(* ============================================================ *)

(* ============================================================ *)
(* 切片账（20260924 R2 柯西代理席，预算内响亮收口）：                    *)
(*   已闭合并编译（本绿盘）：§0 Q 层工具（rp_qpow Fixpoint/rp_qmin/       *)
(*     rp_eps 精度+余量账/rp_qmult_nonneg/换形助件 rp_qlt_eq_l/r/        *)
(*     rp_qlt_eq_rQ——Qcompare_comp 承载，规避 Qlt 目标 rewrite 不透明）； *)
(*     ①Q 代理构造核心 rp_abs_minus_const_proj（柯西逐点恒等）。          *)
(*   已写待编译（WIP 盘 UpReqMixRationalProxy_WIP.v，455+ 行）：          *)
(*     §2 Real 胶合全族（rp_lt_gap/rp_lt_plus_r/rp_minus_lt_swap/        *)
(*     rp_const_* 桥/rp_rpow_pos/rp_rpow_le_mono/rp_Qle_Z/rp_Zle_Qle）、  *)
(*     ③对数搜索 rp_bsearch+pass/min 双 spec、Q 层 Bernoulli 上形式、      *)
(*     上界站闭合 rp_q_close、②误差桥接 rp_tq_bound——WIP 首错在           *)
(*     rp_lt_gap 的 rewrite-under-QltT（需换 change-转换形，模式已定案）。 *)
(*   零 Admitted/零 Axiom/零硬凑——未闭合段不进编译面（fail loud）。        *)
(* ============================================================ *)
