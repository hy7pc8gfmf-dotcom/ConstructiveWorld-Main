(* ==========================================================================)
   abl_arctan_diff_41.v — 9a-乙 ③N 等步链（X41'' 段；两前任         
   殁于并发墙 170s/65s 零遗产，原样重派——此番接续前勘验 /tmp/x41pool 无遗产，
   自 /tmp/x19pool 绿验链真拷重建隔离池 /tmp/x41pool（S01–S11+件16+件19+件20
   md5 对账：件16 d2793fe6/件19 fd017e7a/件20 d8111457 与落件逐一 SAME；
   S11 池版 d571b0c0 系消融批冻结链，Live 现势 S11 d6c6019a 已演进不采）。
   ── 本片范围·数学使命（切片规格：③N 等步链闭合）：──────────────────────────
   目标=把单步增量估计（①一致 delta 已闭合：件19 abl9_atan_deriv_uniform；
   小跨度版件20 已闭合：abl9_const_crit）经 N 等步剖分升格为 N 步链式估计
   （telescoping+归纳两形式全交付）。四组：
   【A Q 层剖分算术】qs（nat→Q 等距递推，qs (S i)=qs i+1 定义性——免 Z.of_nat
   进 Q 项的 rewrite 型差，检验 3 实证）＋正性件 qs_pos＋Z 桥 qs_Z
   （qs n == (Z.of_nat n#1)，setoid 桥接供装配取号）＋zN 正性＋   
   eps/(2N) 预算保正件 abl9_eps_2N_pos（Qlt_shift_div_l+abl9_Qlt_transfer_l）。
   【B Real 层剖分拓扑】|x|+1 正性/严格自增两件（nchain_crit 每步
   delta:=|step|+1 的合法性侧条件——免 ①一致 delta 在剖分内的再使用）。
   【C 链式组合件（本片核心）】abl9_walk（等步迭代节点 Fixpoint：t_0=base、
   t_{S i}=t_i+step——节点以迭代加法定义，使单步结论 phi(t_i+step) 与
   phi(t_{S i}) 定义性转换，免 phi 合同性假设）＋abl9_nchain_eq（抽象
   telescoping 组合件：逐步 real_eq→端点 real_eq，归纳形式）＋
   abl9_nchain_walk（walk 实例）＋**abl9_nchain_crit（③主件：单步一致增量
   估计（∀eps eps'，沿剖分节点逐点可使用）→ N 步链 real_eq**——每步使用
   件20 abl9_const_crit（delta:=|step|+1），预算归 const_crit 体内，链上
   纯 real_eq 传递闭合）。
   【D h/N 剖分件】abl9_hN_step/hN_node（h/N 步长项与 base+(qs i/z)·h 缩放
   形节点，全 z 泛型）＋abl9_walk_hN（迭代形==缩放形逐点环等桥，field 闭合）
   ＋abl9_hN_node_top（端点规整：node(base,h,qs K,K)==base+h——z:=qs K 自
   实例免 Z 桥）＋abl9_hN_lt_delta（剖分步长合法性：|h|<z·delta→|h/z|<delta，
   见证 q/z+Qmult_lt_r+Qabs_Qmult）。
   构造性注记（诚实申明）：phi非合同函数，节点项转移（walk 形↔缩放形↔base+h）
   在 phi 内的使用属装配段（随 phi 合同性逐件供）；本片供给全部项级 real_eq
   桥与 nchain_crit 引擎。预算 eps/(2N) 直和路线（Σ N 份==e·|h|+e/2）由
   const_crit 使用路线取代（更强），直和件不交付、登记在册。
   ── 语料与依赖清单：─────────────────────────────────────────────────────────────
   件19/件20全文实读+两登记册 §四；S11_TP3B5.v（池版 d571b0c0）等步链语料：
   b5a_sin_atan_diff L12596 区域单步 delta 四层 min 构形/b5n 系逐点预算件。
   ── 编译配方（条款 A 节流；发起前进程 <3；窗满候窗禁硬闯）：───────────────
   source Live/toolchain/env.sh && bash cpu_guard.sh --
     rocq c -q -native-compiler no -Q /tmp/x41pool "" /tmp/x41pool/abl_arctan_diff_41.v
   （cwd=/tmp/x41w 异地空目录——承 X19'' 殁因勘定：cwd 残留 vo 与池 -Q 单根
   二义。绿判四件套：EXIT=0/零 Error/vo 魔数 436f7121 00015ff4/vo 新于 v。）
   ========================================================================== *)

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
Require Import abl_arctan_diff_19.
Require Import abl_arctan_diff_20.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax Structures.GenericMinMax.
From Stdlib Require Import ZArith.
From Stdlib Require Import Extraction.

(* ============================================================ *)
(* 【A】Q 层剖分算术                                                *)
(* ============================================================ *)

(* 等距递推：qs i = i（Q 形）——定义性 qs (S i) == qs i + 1，
   供剖分节点分子使用，全程免 Z.of_nat 进 Q 项的重写型差。 *)
Fixpoint qs (i : nat) : Q :=
  match i with
  | O => 0
  | Datatypes.S j => qs j + (1 # 1)
  end.

Lemma abl9_qs_pos : forall K : nat, (1 <= K)%nat -> Qlt 0 (qs K).
Proof.
  induction K as [| m IHm].
  - intros H. lia.
  - cbn [qs].
    destruct m as [| j].
    + intros _. unfold Qlt. simpl. lia.
    + intros _.
      assert (Hltj : Qlt 0 (qs (Datatypes.S j))) by (apply IHm; lia).
      apply (Qlt_le_trans 0 (qs (Datatypes.S j)) (qs (Datatypes.S j) + (1 # 1))).
      * exact Hltj.
      * apply (Qle_trans (qs (Datatypes.S j)) (qs (Datatypes.S j) + 0)
                         (qs (Datatypes.S j) + (1 # 1))).
        -- apply qeq_imp_qle. ring.
        -- apply Qplus_le_compat. apply Qle_refl. unfold Qle. simpl. lia.
Qed.

(* Z 桥：装配取号 qs n == (Z.of_nat n#1)。    *)
Lemma abl9_qs_Z : forall n : nat, qs n == (Z.of_nat n # 1)%Q.
Proof.
  induction n as [| m IHm].
  - reflexivity.
  - cbn [qs].
    apply (Qeq_trans _ ((Z.of_nat m # 1)%Q + (1 # 1))%Q).
    + setoid_rewrite IHm. reflexivity.
    + unfold Qeq. cbn [Qnum Qden Qplus Qmult]. lia.
Qed.

(* 剖分分母取号：N 的 Q 形 (Z.of_nat N # 1) 正性。 *)
Lemma abl9_zN_pos : forall N : nat, (1 <= N)%nat -> Qlt 0 (Z.of_nat N # 1)%Q.
Proof. intros N HN. unfold Qlt. simpl. lia. Qed.

(* eps/(2N) 预算保正（登记册路线「预算 eps/(2N)」的 Q 层核）。*)
Lemma abl9_eps_2N_pos : forall (e : Q) (N : nat),
  Qlt 0 e -> (1 <= N)%nat -> Qlt 0 (e / (2 * (Z.of_nat N # 1))%Q).
Proof.
  intros e N He HN.
  apply Qlt_shift_div_l.
  - apply Qmult_lt_0_compat.
    + reflexivity.
    + apply abl9_zN_pos. exact HN.
  - apply (abl9_Qlt_transfer_l 0 (0 * (2 * (Z.of_nat N # 1))%Q) e).
    + ring.
    + exact He.
Qed.

(* ============================================================ *)
(* 【B】Real 层剖分拓扑：|x|+1 两件（nchain_crit 每步 delta 侧条件）   *)
(* ============================================================ *)

Lemma abl9_abs_plus_one_pos : forall x : Real,
  real_lt real_zero (real_plus (real_abs x) real_one).
Proof.
  intros x.
  exists (1 # 2)%Q. split.
  - apply Qlt_to_QltT. reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj (real_abs x) real_one n).
    rewrite (p2_one_proj n).
    rewrite (real_abs_proj x n).
    cbn [projT1 real_zero].
    apply (Qlt_le_trans (1 # 2) 1 (Qabs (projT1 x n) + 1 - 0)).
    + reflexivity.
    + apply (Qle_trans 1 (1 + Qabs (projT1 x n)) (Qabs (projT1 x n) + 1 - 0)).
      * apply (Qle_trans 1 (1 + 0) (1 + Qabs (projT1 x n))).
        -- apply qeq_imp_qle. ring.
        -- apply Qplus_le_compat. apply Qle_refl. apply Qabs_nonneg.
      * apply qeq_imp_qle. ring.
Qed.

Lemma abl9_abs_lt_plus_one : forall x : Real,
  real_lt (real_abs x) (real_plus (real_abs x) real_one).
Proof.
  intros x.
  exists (1 # 2)%Q. split.
  - apply Qlt_to_QltT. reflexivity.
  - exists 0%nat. intros n Hn.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj (real_abs x) real_one n).
    rewrite (p2_one_proj n).
    rewrite (real_abs_proj x n).
    cbn [projT1 real_zero].
    assert (E : Qabs (projT1 x n) + 1 - Qabs (projT1 x n) == 1) by ring.
    setoid_rewrite E.
    reflexivity.
Qed.

(* ============================================================ *)
(* 【C】链式组合件（telescoping+归纳；本片核心）                      *)
(* ============================================================ *)

(* 等步迭代节点：t_0 := base，t_{S i} := t_i + step。
   节点以迭代加法定义 ⟹ 单步结论 phi(t_i + step) 与 phi(t_{S i}) 定义性
   转换（iota），链上免 phi 合同性假设。 *)
Fixpoint abl9_walk (base step : Real) (i : nat) : Real :=
  match i with
  | O => base
  | Datatypes.S j => real_plus (abl9_walk base step j) step
  end.

(* 抽象 telescoping 组合件：逐步 real_eq → 端点 real_eq（归纳形式）。 *)
Lemma abl9_nchain_eq : forall (phi : Real -> Real) (t : nat -> Real) (N : nat),
  (forall i : nat, (i < N)%nat -> real_eq (phi (t (Datatypes.S i))) (phi (t i))) ->
  real_eq (phi (t N)) (phi (t 0%nat)).
Proof.
  intros phi t N Hstep.
  assert (Hmain : forall k : nat, (k <= N)%nat -> real_eq (phi (t k)) (phi (t 0%nat))).
  { induction k as [| j IHj].
    - intros _. apply real_eq_refl.
    - intros Hj.
      apply (real_eq_trans (phi (t (Datatypes.S j))) (phi (t j)) (phi (t 0%nat))).
      + apply Hstep. lia.
      + apply IHj. lia. }
  apply (Hmain N). apply Nat.le_refl.
Qed.

(* walk 实例。 *)
Lemma abl9_nchain_walk : forall (phi : Real -> Real) (base step : Real) (N : nat),
  (forall i : nat, (i < N)%nat ->
     real_eq (phi (abl9_walk base step (Datatypes.S i)))
             (phi (abl9_walk base step i))) ->
  real_eq (phi (abl9_walk base step N)) (phi (abl9_walk base step 0%nat)).
Proof.
  intros phi base step N H.
  apply (abl9_nchain_eq phi (abl9_walk base step) N).
  exact H.
Qed.

(* ===== ③主件：单步一致增量估计 → N 步链式估计 =====
   剖分：N 等步（步长 step 任意给定），节点=abl9_walk。
   每步使用件20 abl9_const_crit（其 delta 侧条件取 |step|+1——恒合法，
   见【B】两件），单步 real_eq 后 telescoping 闭合。 *)
Lemma abl9_nchain_crit : forall (phi : Real -> Real) (base step : Real) (N : nat),
  (forall i : nat, (i < N)%nat ->
     forall (eps eps' : Real), real_lt real_zero eps -> real_lt real_zero eps' ->
       real_le (real_abs (real_plus (phi (abl9_walk base step (Datatypes.S i)))
                                    (real_opp (phi (abl9_walk base step i)))))
               (real_plus (real_mult eps (real_abs step)) eps')) ->
  real_eq (phi (abl9_walk base step N)) (phi (abl9_walk base step 0%nat)).
Proof.
  intros phi base step N H.
  apply abl9_nchain_walk. intros i Hi.
  apply (abl9_const_crit phi (abl9_walk base step i) step
           (real_plus (real_abs step) real_one)).
  - apply abl9_abs_plus_one_pos.
  - apply abl9_abs_lt_plus_one.
  - intros eps eps' Heps Heps'.
    exact (H i Hi eps eps' Heps Heps').
Qed.

(* ============================================================ *)
(* 【D】h/N 剖分件（全 z 泛型——z 由装配取号，正性随带）               *)
(* ============================================================ *)

(* h/N 步长项：h·(1/z)。 *)
Definition abl9_hN_step (h : Real) (z : Q) : Real :=
  real_mult (real_const ((1 # 1) / z)%Q) h.

(* 缩放形节点：base+(qs i / z)·h（登记册 t_i:=real_const (i#N)*h 的 
   division 形——qs i 系 i 的 Q 形，免 Z.of_nat 进 Q 项）。 *)
Definition abl9_hN_node (base h : Real) (z : Q) (i : nat) : Real :=
  real_plus base (real_mult (real_const ((qs i / z)%Q)) h).

(* 迭代形==缩放形（逐点 Q 环等，field 闭合）。 *)
Lemma abl9_walk_hN : forall (base h : Real) (z : Q), ~ (z == 0) ->
  forall i : nat,
  real_eq (abl9_walk base (abl9_hN_step h z) i) (abl9_hN_node base h z i).
Proof.
  intros base h z Hz i. induction i as [| j IHj].
  - apply real_eq_of_zero_diff. intros n.
    cbn [abl9_walk abl9_hN_node].
    rewrite (real_plus_proj base (real_mult (real_const ((qs 0 / z)%Q)) h) n).
    rewrite (real_mult_proj (real_const ((qs 0 / z)%Q)) h n).
    rewrite (real_const_proj ((qs 0 / z)%Q) n).
    cbn [projT1].
    assert (H0 : (qs 0 / z)%Q == 0) by (cbn [qs]; unfold Qdiv; apply Qmult_0_l).
    setoid_rewrite H0.
    ring.
  - apply (real_eq_trans
             (abl9_walk base (abl9_hN_step h z) (Datatypes.S j))
             (real_plus (abl9_hN_node base h z j) (abl9_hN_step h z))
             (abl9_hN_node base h z (Datatypes.S j))).
    + apply (real_eq_trans
               (abl9_walk base (abl9_hN_step h z) (Datatypes.S j))
               (real_plus (abl9_walk base (abl9_hN_step h z) j) (abl9_hN_step h z))
               (real_plus (abl9_hN_node base h z j) (abl9_hN_step h z))).
      * apply real_eq_refl.
      * apply RealSetoid.real_eq_plus_compat.
        -- exact IHj.
        -- apply real_eq_refl.
    + apply real_eq_of_zero_diff. intros n.
      unfold abl9_hN_node, abl9_hN_step.
      rewrite (real_plus_proj
                (real_plus base (real_mult (real_const ((qs j / z)%Q)) h))
                (real_mult (real_const (((1 # 1) / z)%Q)) h) n).
      rewrite (real_plus_proj base (real_mult (real_const ((qs j / z)%Q)) h) n).
      rewrite (real_mult_proj (real_const ((qs j / z)%Q)) h n).
      rewrite (real_const_proj ((qs j / z)%Q) n).
      rewrite (real_mult_proj (real_const (((1 # 1) / z)%Q)) h n).
      rewrite (real_const_proj (((1 # 1) / z)%Q) n).
      rewrite (real_plus_proj base
                 (real_mult (real_const ((qs (Datatypes.S j) / z)%Q)) h) n).
      rewrite (real_mult_proj (real_const ((qs (Datatypes.S j) / z)%Q)) h n).
      rewrite (real_const_proj ((qs (Datatypes.S j) / z)%Q) n).
      cbn [projT1].
      cbn [qs].
      field. exact Hz.
Qed.

(* 端点规整：node(base,h,qs K,K)==base+h（z:=qs K 自实例——(q/q)==1）。 *)
Lemma abl9_hN_node_top : forall (base h : Real) (K : nat), (1 <= K)%nat ->
  real_eq (abl9_hN_node base h (qs K) K) (real_plus base h).
Proof.
  intros base h K HK.
  assert (Hz : ~ (qs K == 0)%Q).
  { intros H0.
    assert (Hlt : Qlt 0 (qs K)) by (apply abl9_qs_pos; exact HK).
    assert (Hle : Qle (qs K) 0) by (apply qeq_imp_qle; exact H0).
    exact (Qlt_not_le 0 (qs K) Hlt Hle). }
  apply real_eq_of_zero_diff. intros n.
  unfold abl9_hN_node.
  rewrite (real_plus_proj base (real_mult (real_const ((qs K / qs K)%Q)) h) n).
  rewrite (real_mult_proj (real_const ((qs K / qs K)%Q)) h n).
  rewrite (real_const_proj ((qs K / qs K)%Q) n).
  rewrite (real_plus_proj base h n).
  cbn [projT1].
  assert (E : (qs K / qs K)%Q == 1) by (field; exact Hz).
  setoid_rewrite E. ring.
Qed.

(* 剖分步长合法性：|h| < z·delta ⟹ |h/z| < delta（见证 q/z；
   乘 z 闭合 Qmult_lt_r，|h/z|==(1/z)|h| 经 Qabs_Qmult+Qabs_pos）。 *)
Lemma abl9_hN_lt_delta : forall (h delta : Real) (z : Q), (0 < z)%Q ->
  real_lt (real_abs h) (real_mult (real_const z) delta) ->
  real_lt (real_abs (abl9_hN_step h z)) delta.
Proof.
  intros h delta z Hz Hlt.
  assert (Hz0 : ~ (z == 0)%Q).
  { intros H0.
    assert (Hle : Qle z 0) by (apply qeq_imp_qle; exact H0).
    exact (Qlt_not_le 0 z Hz Hle). }
  assert (HzN0 : Qlt 0 ((1 # 1) / z)%Q).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - reflexivity.
    - apply Qinv_lt_0_compat. exact Hz. }
  destruct Hlt as [q [Hq0 [M HM]]].
  exists (q * ((1 # 1) / z))%Q. split.
  - apply Qlt_to_QltT.
    apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. exact Hq0.
    + exact HzN0.
  - exists M. intros n Hn.
    apply Qlt_to_QltT.
    assert (HabsN : projT1 (real_abs (abl9_hN_step h z)) n
                    == ((1 # 1) / z)%Q * Qabs (projT1 h n)).
    { rewrite (real_abs_proj (abl9_hN_step h z) n).
      unfold abl9_hN_step.
      rewrite (real_mult_proj (real_const (((1 # 1) / z)%Q)) h n).
      rewrite (real_const_proj (((1 # 1) / z)%Q) n).
      cbn [projT1].
      rewrite Qabs_Qmult.
      assert (E1 : Qabs (((1 # 1) / z)%Q) == ((1 # 1) / z)%Q)
        by (apply Qabs_pos; apply Qlt_le_weak; exact HzN0).
      rewrite E1. reflexivity. }
    assert (HM' : Qlt q (z * projT1 delta n - Qabs (projT1 h n))).
    { apply (abl9_Qlt_transfer_r q
               (projT1 (real_mult (real_const z) delta) n
                - projT1 (real_abs h) n)).
      - rewrite (real_mult_proj (real_const z) delta n).
        rewrite (real_const_proj z n).
        rewrite (real_abs_proj h n).
        cbn [projT1]. reflexivity.
      - apply QltT_to_Qlt. exact (HM n Hn). }
    apply (abl9_Qlt_transfer_r (q * ((1 # 1) / z))%Q
             (projT1 delta n - ((1 # 1) / z)%Q * Qabs (projT1 h n))
             (projT1 delta n - projT1 (real_abs (abl9_hN_step h z)) n)).
    + setoid_rewrite HabsN. reflexivity.
    + (* (q/z) < delta_n − |h_n|/z ⟸ q < z·delta_n − |h_n|（乘 z>0） *)
      apply (proj1 (Qmult_lt_r (q * ((1 # 1) / z))%Q
               (projT1 delta n - ((1 # 1) / z)%Q * Qabs (projT1 h n))
               z Hz)).
      * assert (EA : (q * ((1 # 1) / z))%Q * z == q) by (field; exact Hz0).
        assert (EB : (projT1 delta n - ((1 # 1) / z)%Q * Qabs (projT1 h n)) * z
                     == z * projT1 delta n - Qabs (projT1 h n))
          by (field; exact Hz0).
        setoid_rewrite EA. setoid_rewrite EB. exact HM'.
Qed.

(* ============================================================ *)
(* 终验 · 承认面 + 提取检验                                            *)
(*   对账三联：Lemma 名清单 12 = Qed 计数 12 = PA 语句 12，零差。       *)
(* ============================================================ *)
Print Assumptions abl9_qs_pos.
Print Assumptions abl9_qs_Z.
Print Assumptions abl9_zN_pos.
Print Assumptions abl9_eps_2N_pos.
Print Assumptions abl9_abs_plus_one_pos.
Print Assumptions abl9_abs_lt_plus_one.
Print Assumptions abl9_nchain_eq.
Print Assumptions abl9_nchain_walk.
Print Assumptions abl9_nchain_crit.
Print Assumptions abl9_walk_hN.
Print Assumptions abl9_hN_node_top.
Print Assumptions abl9_hN_lt_delta.

(* 提取检验（判据 = 输出 Obj.magic 计数 0） *)
Recursive Extraction abl9_qs_pos abl9_nchain_crit abl9_hN_lt_delta.
Recursive Extraction abl9_walk_hN abl9_eps_2N_pos abl9_hN_node_top.
