(* LW3ExpNegLB.v                                                     *)
(* 使命：e^{−node} 显式正有理下界件（C4 供给侧 GAPASUME 缺口清单第 3 项——   *)
(*       eps 选取位的 QltT 0 eps 槽供给）：对任意非负整数点 node，显式产出   *)
(*       正有理数 r := 1/(4C)（C 为 exp 级数在 a := node 处的一致界，        *)
(*       exp_series_arch 构造产出）使得 real_const r < e^{−node} 严格成立    *)
(*       （real_lt 数据形逐字对照 383 链 realcarrier 的节点使用形            *)
(*       cauchy_real_exp (real_const (- lw2_node node))）。                  *)
(* 依赖：S01_BaseRing/S02_CauchyComplete/S03_QExp/LW0QPoly/LW2Hermite        *)
(*       （deps 五件自 Live_X 与主库/399 谱系只读拷贝，digest 三侧实测全等）。*)
(* 对标：E-STAGING-LW0-GAPASUME（检索索引 L1842：缺口即后续段目标形，        *)
(*       eps 选取位落地后下游零改动实例化）；E-STAGING-LW0-NOEVALIFT         *)
(*       （检索索引 L1860：装配全走在件引理与数据桥，零 eval 级拼装——       *)
(*       核心机件 exp_series_arch/exp_partial_tail_small/exp_partial_       *)
(*       even_lower/exp_partial_odd_lower 全 S03 在件）；E-STAGING-LW3-     *)
(*       PROBEPIN（值级面照配方族）；383 投影桥判例（projT1 reflexivity 化）。*)
(* 构造性：语句面全 Set——结论 sigT＋And（S01 A*B）＋QltT（Id-bool）＋       *)
(*       real_lt（sigT 嵌套数据形），零 Prop 命题、零假设承载位、零 Axiom；  *)
(*       证明体 Qlt/Qle 仅体内转译（Qlt_to_QltT/Qle_to_QleT' 桥归 Set 出口， *)
(*       正本同款口径）；提取并集仅数据名 tlw401_parity（纯 nat 结构函数，   *)
(*       match 型见证不入提取并集——391/399 同款工艺）。                      *)
(* 编译配方：SW2 双 export COQLIB/ROCQLIB="C:/Rocq-Platform~9.1~2026.01/    *)
(*       lib/coq" 全字面；coqc -q -Q . ""；cpu_guard 包裹。                  *)
(* 406 解冻出处（1001）：承 401 冻结件（md5 769a467e）解冻收束。红点   *)
(* L141 出口段按 401 记录 §七径甲核心（Hdiff 全桥，投影桥 Qeq 面内实测工作）   *)
(* ＋病灶谱诊修正尾段（qltT_eq_compat_r 差项移写；Qplus_lt_r 系左移位 iff      *)
(* z+x<z+y<->x<y，取 proj1；2r=1/(2·C) 由 ring/field 双桥闭合）一次发射闭合。  *)

Require Import QArith Lia Arith ZArith List.
From Stdlib Require Import QArith_base.
From Stdlib Require Import QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import LW0QPoly.
Require Import LW2Hermite.

Local Open Scope Q_scope.

(* ============================================================ *)
(* 桥 0：常值实数与有理点实指数的逐点投影（383 判例同款 reflexivity 桥）      *)
(* ============================================================ *)

Lemma tlw401_proj_const : forall (c : Q) (n : nat),
  projT1 (real_const c) n == c.
Proof. intros c n. unfold real_const. reflexivity. Qed.

Lemma tlw401_proj_exp : forall (X : Q) (n : nat),
  projT1 (cauchy_real_exp (real_const X)) n == exp_partial n X.
Proof. intros X n. unfold cauchy_real_exp, real_const. reflexivity. Qed.

(* ============================================================ *)
(* 桥 1：自然数偶奇二分（纯 Set 数据形：sum＋sigT，语句面零 Prop）            *)
(* ============================================================ *)

Lemma tlw401_parity : forall n : nat,
  sigT (fun m : nat => (n = 2 * m)%nat) +
  sigT (fun m : nat => (n = Datatypes.S (2 * m))%nat).
Proof.
  induction n as [| n IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[m Hm] | [m Hm]].
    + right. exists m. rewrite Hm. lia.
    + left. exists (Datatypes.S m). rewrite Hm. lia.
Qed.

(* ============================================================ *)
(* 主件：e^{−node} 的显式正有理下界（eps 选取位供给形）                        *)
(*   构造：a := node（lw2_node 透明嵌入），C := exp 级数一致界               *)
(*   （exp_series_arch），m0 := 尾衰见证（exp_partial_tail_small），           *)
(*   逐点统一下界 1/(2C)（偶支 1/C ≤ S_{2m}、奇支 1/(2C) < S_{2m+1}），        *)
(*   r := 1/(4C)：0 < r 且 2r < 逐点截断 ⟹ real_lt (real_const r) e^{−a}。   *)
(* ============================================================ *)

Theorem tlw401_expneg_pos_lb : forall (node : nat),
  sigT (fun r : Q =>
    And (QltT 0 r)
        (real_lt (real_const r)
           (cauchy_real_exp (real_const (- lw2_node node))))).
Proof.
  intros node.
  set (a := lw2_node node).
  (* ① 节点点非负（Z 层直构，Zmult_1_r＋Zle_0_nat） *)
  assert (Ha0 : QleT' 0 a).
  { unfold a, lw2_node. apply Qle_to_QleT'.
    unfold Qle. cbn [Qnum Qden].
    rewrite !Zmult_1_r. apply Zle_0_nat. }
  (* ② 一致界 C 与尾衰见证 m0（S03 双 sigT 件直连） *)
  destruct (exp_series_arch a Ha0) as [C [HC1 HCs]].
  destruct (exp_partial_tail_small a C Ha0 HC1) as [m0 Hm0].
  assert (HCpos : Qlt 0 C).
  { apply (Qlt_le_trans 0 1 C).
    - unfold Qlt. simpl. lia.
    - apply QleT'_to_Qle. exact HC1. }
  assert (Hz2C : Qlt 0 (2 * C)).
  { apply (Qmult_lt_0_compat 2 C).
    - unfold Qlt. simpl. lia.
    - exact HCpos. }
  assert (Hz4C : Qlt 0 (4 * C)).
  { apply (Qmult_lt_0_compat 4 C).
    - unfold Qlt. simpl. lia.
    - exact HCpos. }
  (* ③ 显式下界 r := 1/(4C) 与半步严格桥（同乘 (2C)/(4C) 的 field 面） *)
  assert (Hrpos : QltT 0 (1 / (4 * C))).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat 1 (Qinv (4 * C))).
    - unfold Qlt. simpl. lia.
    - apply Qinv_lt_0_compat. exact Hz4C. }
  assert (Hhalf : Qlt (1 / (2 * C)) (1 / C)).
  { apply (Qlt_shift_div_r 1 (2 * C) (1 / C) Hz2C).
    assert (E2 : (1 / C) * (2 * C) == 2%Q).
    { unfold Qdiv. field. apply q_neq_of_lt. exact HCpos. }
    rewrite E2. unfold Qlt. reflexivity. }
  assert (Hhalf2 : Qlt (1 / (4 * C)) (1 / (2 * C))).
  { apply (Qlt_shift_div_r 1 (4 * C) (1 / (2 * C)) Hz4C).
    assert (E2 : (1 / (2 * C)) * (4 * C) == 2%Q).
    { unfold Qdiv. field. apply q_neq_of_lt. exact HCpos. }
    rewrite E2. unfold Qlt. reflexivity. }
  (* ④ |−a| ≤ a 的承载槽（Qabs_opp＋Qabs_pos 双步） *)
  assert (Hy : QleT' (Qabs (- a)) a).
  { apply Qle_to_QleT'.
    apply (Qle_trans (Qabs (- a)) (Qabs a) a).
    - apply qeq_le. apply Qabs_opp.
    - apply qeq_le. apply Qabs_pos. apply QleT'_to_Qle. exact Ha0. }
  (* ⑤ 逐点统一下界：n ≥ 2m0 ⟹ 1/(2C) < S_n(−a)（偶偶奇奇双支合流） *)
  assert (Hlow : forall n : nat, NatLe (2 * m0) n ->
            QltT (1 / (2 * C)) (exp_partial n (- a))).
  { intros n Hn. apply NatLe_drop in Hn.
    destruct (tlw401_parity n) as [[m Hm] | [m Hm]].
    - subst n. assert (Hge : (m0 <= m)%nat) by lia.
      apply Qlt_to_QltT.
      apply (Qlt_le_trans (1 / (2 * C)) (1 / C) (exp_partial (2 * m) (- a)) Hhalf).
      exact (exp_partial_even_lower a C (- a) m Ha0 HC1 HCs Hy).
    - subst n. assert (Hge : (m0 <= m)%nat) by lia.
      replace (Datatypes.S (2 * m)) with (2 * m + 1)%nat by lia.
      exact (Qlt_to_QltT (1 / (2 * C)) (exp_partial (2 * m + 1) (- a))
               (exp_partial_odd_lower a C m0 m (- a) Ha0 HC1 HCs Hm0 Hge Hy)). }
  (* ⑥ 装配出口：拆 real_lt 定义；出口差项经 Hdiff 全桥（径甲核心）与
     qltT_eq_compat_r 移写化为 e^{−a} − r 形；2r = 1/(2·C) 半步差严格收尾。 *)
  exists (1 / (4 * C))%Q.
  split.
  - exact Hrpos.
  - exists (1 / (4 * C))%Q.
    split.
    + exact Hrpos.
    + exists (2 * m0)%nat. intros n Hn.
      assert (Hdiff : projT1 (cauchy_real_exp (real_const (- a))) n -
                      projT1 (real_const (1 / (4 * C))) n ==
                      exp_partial n (- a) - 1 / (4 * C)).
      { rewrite (tlw401_proj_exp (- a) n), (tlw401_proj_const (1 / (4 * C)) n).
        reflexivity. }
      apply (qltT_eq_compat_r
               (projT1 (cauchy_real_exp (real_const (- a))) n -
                projT1 (real_const (1 / (4 * C))) n)
               (exp_partial n (- a) - 1 / (4 * C)) (1 / (4 * C)) Hdiff).
      apply Qlt_to_QltT.
      apply (proj1 (Qplus_lt_r (1 / (4 * C))
                               (exp_partial n (- a) - 1 / (4 * C))
                               (1 / (4 * C)))).
      assert (Hback : 1 / (4 * C) + (exp_partial n (- a) - 1 / (4 * C))
                      == exp_partial n (- a)) by ring.
      rewrite Hback.
      assert (Hrr : 1 / (4 * C) + 1 / (4 * C) == 1 / (2 * C)).
      { field.
        all: try (apply q_neq_of_lt; assumption). }
      rewrite Hrr.
      apply QltT_to_Qlt. apply Hlow. exact Hn.
Qed.

Print Assumptions tlw401_expneg_pos_lb.
Print Assumptions tlw401_parity.

(* 提取闸：并集仅数据名 tlw401_parity（纯 nat 结构函数；match 型见证不入—— *)
(* 391/399 同款工艺，EXTRACT-UNION-PINLESS 判例）。落名 _tlw401_expneg_lb.ml。 *)
Separate Extraction tlw401_parity.
