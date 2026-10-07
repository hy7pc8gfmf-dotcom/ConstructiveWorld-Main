(* ================================================================== *)
(* TLW1448L2Escape —— 档二参数化上界的组装主定理                          *)
(*                                                                    *)
(* 数学使命：给定 0 < c 与 pi_L 到 q 的逐点距离证书（尾段 c < |xL k−q|），*)
(*   在显式窗阶 n0 := S(pie_modulus(c/2)) 处必有 bool 分离判定器出窗：   *)
(*   lw5n_sep_dec q n0 = true。证法三步：包络模量界 pie_modulus_bound   *)
(*   给 4·pie_mag(pie_modulus(c/2)) < c/2；Q 算术桥给窗族 eps_{n0} =     *)
(*   1/(n0+1) < c；lw1m_dist_outwin（入窗则近距、窗宽小于距离则必出窗）  *)
(*   即完成证明。此即增长律闭合定理的上界供给（闭合定理与双向带合成另件）。     *)
(*                                                                    *)
(* 依赖清单：Stdlib QArith/List/Bool/Arith/Setoid/Morphisms/Lia/Qminmax；*)
(*   S01_BaseRing S02_CauchyComplete S03_QExp PiEnvelope LW0MLicBridge  *)
(*   LW0LeibWindow S10_KVQuantTrig S11_TP3B5 LW5SepComplexity           *)
(*   Local.LW0LeibSeparation LW0PiIrrational LW1PiMeasure               *)
(*                                                                    *)
(* 对标行：LW5SepComplexity §4 注记（档二参数化上界：置 lw5n_B c :=      *)
(*   S(pie_modulus(c/2))，仅注记无定理——本件闭证之）；LW1PiMeasure        *)
(*   lw1m_dist_outwin（距离-出窗互译核）；PiEnvelope pie_modulus_bound。 *)
(*                                                                    *)
(* 构造性注记：全 Set/Type 层；零 Axiom/Admitted；零 Prop 泄露；Q 算术    *)
(*   走 Qlt 定义性展开＋Z 线性判定（Lia），不引 Reals/经典逻辑。          *)
(*                                                                    *)
(* 编译配方：coqc -native-compiler no -q -Q . "" tlw1448_l2escape.v      *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW0LeibWindow.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import LW5SepComplexity.
Require Import Local.LW0LeibSeparation.
Require Import LW0PiIrrational.
Require Import LW1PiMeasure.

(* 档二主定理：距离证书 ⟹ 显式窗阶 S(pie_modulus(c/2)) 处出窗 *)
Theorem tlw1448_l2_escape : forall (q c : Q), QltT' 0 c ->
  lw1m_dist_pt q c ->
  Id (lw5n_sep_dec q (Datatypes.S (pie_modulus (c / 2)%Q))) true.
Proof.
  intros q c Hc Hd.
  apply (lw1m_dist_outwin q (Datatypes.S (pie_modulus (c / 2)%Q)) c).
  - (* 窗族阶：eps_{S P} < c，其中 P := pie_modulus (c/2) *)
    apply Qlt_to_QltT'.
    pose proof Hc as HcQ. apply QltT'_to_Qlt in HcQ.
    set (P := pie_modulus (c / 2)%Q).
    (* 半量正性：0 < c/2 *)
    assert (Hc2 : Qlt 0 (c / 2)%Q).
    { unfold Qdiv.
      apply (Qmult_lt_0_compat c (/ (2 # 1))).
      - exact HcQ.
      - apply Qinv_lt_0_compat. unfold Qlt. cbn [Qnum Qden]. lia. }
    (* 包络模量界：4·pie_mag P < c/2（pie_modulus_bound） *)
    pose proof (pie_modulus_bound (c / 2)%Q Hc2) as Hpb.
    (* 半量传递：c/2 < c（c·(1/2) < c·1，正乘子 c 上的单调性） *)
    assert (Hhalf : Qlt (c / 2)%Q c).
    { unfold Qdiv.
      replace (Qinv (2 # 1)%Q) with (1 # 2)%Q by reflexivity.
      assert (Hq2 : Qlt (1 # 2)%Q (1 # 1)%Q)
        by (unfold Qlt; cbn [Qnum Qden]; lia).
      pose proof (Qmult_lt_compat_r (1 # 2)%Q (1 # 1)%Q c HcQ Hq2) as Hm.
      rewrite Qmult_1_l in Hm.
      rewrite (Qmult_comm c (1 # 2)%Q).
      exact Hm. }
    (* Q 算术桥：eps_{S P} = 1/(P+2) < 4/(2P+1) = 4·pie_mag P
       （交叉乘 2P+1 < 4(P+2)，对 P 恒真；pie_mag 分母的 Z.of_nat 形经
         S 形定义性归一至 Z.pos 后整式 transport；Nat2Z 链＋Z 判定） *)
    assert (Heps : Qlt (lw5n_eps (Datatypes.S P)) (4 * pie_mag P)).
    { unfold lw5n_eps, pie_mag.
      replace (Z.of_nat (2 * P + 1)) with (Z.pos (Pos.of_succ_nat (2 * P))).
      2: { replace (2 * P + 1)%nat with (Datatypes.S (2 * P))%nat by lia.
           reflexivity. }
      replace (4 * (1 / (Z.pos (Pos.of_succ_nat (2 * P)) # 1)))%Q
        with (4 # Pos.of_succ_nat (2 * P))%Q by reflexivity.
      unfold Qlt. cbn [Qnum Qden].
      replace (Z.pos (Pos.of_succ_nat (Datatypes.S P)))
        with (Z.of_nat (Datatypes.S (Datatypes.S P))) by reflexivity.
      replace (Z.pos (Pos.of_succ_nat (2 * P)))
        with (Z.of_nat (Datatypes.S (2 * P))) by reflexivity.
      lia. }
    exact (Qlt_trans (lw5n_eps (Datatypes.S P)) (4 * pie_mag P) c Heps
            (Qlt_trans (4 * pie_mag P) (c / 2)%Q c Hpb Hhalf)).
  - exact Hd.
Qed.

(* 换基搜索器实例（接 tlw1448_rebase 模块的参数化形；本件独立重述供审计） *)
Definition tlw1448_l2_order (q : Q) (c : Q) : nat :=
  Datatypes.S (pie_modulus (c / 2)%Q).

(* ---- 假设审计（应 Closed）---- *)
Print Assumptions tlw1448_l2_escape.

(* ---- 提取检验（Obj.magic 计数如实登记）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1448_l2escape_ext.ml" tlw1448_l2_order lw5n_sep_dec.
