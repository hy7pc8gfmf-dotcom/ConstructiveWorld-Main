(* ============================================================ *)
(* UpAblQfloorDepth.v —— S10 尾界链 N 指标实例化纵深直配件（N10 席·20260920） *)
(*                                                                *)
(* 席位：N10（Qfloor 纵深 N 指标实例化席，N4R 清单⑤·C.1 门后纵深）        *)
(* 零承认件：无承认词面、无经典逻辑、全件 Qed 闭合；                        *)
(*   交付语句面全 Set 层值（QltT/QleT'＝S02 Id 形＋sigT 见证），           *)
(*   语句面无裸命题；Qeq/Z 换形全部内联于证明内部（不上语句面）。           *)
(*                                                                *)
(* 槽位来源（本席 M3 纵深普查，逐处 grep 语句实形定谳）：                   *)
(*   槽① S10_KVQuantTrig.v :2971 cauchy_real_pi_leibniz 柯西见证位——      *)
(*      destruct (q_arch_inv (eps / lp_four)) 取 N1 后 exists N1（:2972）， *)
(*      契约＝S02:1681 q_arch_inv 的单位分数形 sigT(N, 1/(N+2) < u)；      *)
(*      下游经 sc_lp_four_arch_lt（:2936）四倍链入 eps。                   *)
(*      定谳：可直配——Qfloor 指标 uabS4b_arch_N 直接实例化 N 位            *)
(*      （N := S(arch_N u)，降容支 uabS4b_null_mono 承接 +2 槽移）。        *)
(*   槽② S10 :1675/1722/6424/11088/12009 五同形 q_arch_geom 基指标位——     *)
(*      契约＝sigT(N, forall t≥N, 2B ≤ (t+1)#1)（调和位 1/(t+1) vs 2B）。   *)
(*      定谳（墙论证级，照 B3 体例申报）：Qfloor 指标 1/(arch_N(Qinv(2B))+1) *)
(*      < 1/(2B) 到 2B < (M+1)#1 的调和反演位受阻——Qinv 的 Zneg 三支       *)
(*      match 阻断定义性换形（Qinv x ≢ Qmake (QDen x) (Qnum x)），Q 层      *)
(*      缺 Qeq 右换形件（Qlt/QltT 基座）与 Qinv-Qdiv 桥件，禁硬凑——        *)
(*      列后续席（需 S02 层补 Qeq 右换形位或 Qmult_inv 桥件后直配）。        *)
(*   不可直配定谳（墙论证级，列后续席）：                                   *)
(*   S10 :1682/1728/6436/11100/12022 arch_decay 衰减位——(1/2)^{S t}        *)
(*      几何衰减形，非单位分数谱系，Qfloor 指标不供此形；                   *)
(*   S10 :2236/2318 输入柯西模位——N 由假设的 cauchy 证书供给（全称位），    *)
(*      非阿基米德实例化位。                                               *)
(*                                                                *)
(* 供给结构（四件，qfd_ 前缀）：                                           *)
(*   A 单位分数 +2 槽移核：qfd_arch_inv_core（QltT 面）＋                  *)
(*      qfd_arch_inv_instT（S02:1681 契约位 sigT 实例——槽① N 位直配）；    *)
(*   B C.1 门纵深：qfd_pi_margin_absT——+2 槽移单位分数降容过               *)
(*      uaq_qfloor_abs_margin 门（C.1 直配消费，尾句 exact 该门）；          *)
(*   C 槽①下游四倍链：qfd_pi_four_marginT——消费 S10:2936                  *)
(*      sc_lp_four_arch_lt 本位（N := S(arch_N(eps/lp_four)) 实例化）；     *)
(*   D 槽②未交付（墙级定谳见上）——本件交付 A/B/C 三部四件，全款槽①。      *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（S01–S15 全 Export 薄壳，q_arch_inv/     *)
(*   q_arch_geom/sc_lp_four_arch_lt/lp_four 皆在 namespaces）＋             *)
(*   UpAblAbsSumLeB2（S4B Qfloor 谱系件）＋UpAblAbsQFeed（uaq_ 系供体件）。 *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* Part 0 · 冻结现态打表（签名漂移即响亮失败）                              *)
(* ============================================================ *)

Check QltT. Check QleT'.
Check QltT_to_Qlt. Check Qlt_to_QltT. Check Qle_to_QleT'.
Check qltT_eq_compat_l. Check qleT'_ltT_ltT. Check qeq_le.
Check Qeq_sym. Check Qeq_trans. Check Qabs_wd. Check Qabs_pos.
Check Qle_trans.
Check uabS4b_arch_N. Check uabS4b_null_lt. Check uabS4b_null_mono.
Check uabS4b_null_nonneg. Check uabS4b_pos_succ_Z.
Check uaq_qfloor_abs_margin.
Check NatLe_drop.
Check Qmult_lt_0_compat. Check Qinv_lt_0_compat.
Check q_arch_inv. Check q_arch_geom. Check arch_decay.
Check lp_four. Check sc_lp_four_pos. Check sc_lp_four_arch_lt.

(* ============================================================ *)
(* Part A · 槽①核：单位分数 +2 槽移（Qfloor 指标直配 q_arch_inv 契约）      *)
(* ============================================================ *)

(* A.1 核：N := S(arch_N u) 使 1/(N+2)#1 <T u。
   谱系链：uabS4b_null_lt 给 1/(n+1) <T u；uabS4b_null_mono 降容
   1/(n+2) ≤ 1/(n+1)；Qeq 换形（Z 恒等式 uabS4b_pos_succ_Z）入 #1 槽形。 *)
Lemma qfd_arch_inv_core : forall u : Q, QltT 0 u ->
  QltT (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)) u.
Proof.
  intros u Hu.
  assert (Hzk : Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2)
                = Z.pos (Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))).
  { rewrite uabS4b_pos_succ_Z. lia. }
  assert (Hstep : 1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)
                  == (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))%Q).
  { rewrite Hzk. reflexivity. }
  apply (qltT_eq_compat_l
           (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))
           (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1))
           u
           (Qeq_sym _ _ Hstep)).
  apply (qleT'_ltT_ltT
           (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))
           (1#(Pos.of_succ_nat (uabS4b_arch_N u)))
           u).
  - apply Qle_to_QleT'. apply uabS4b_null_mono. lia.
  - exact (uabS4b_null_lt u Hu).
Qed.

(* A.2 契约位实例（槽①直配）：S02:1681 q_arch_inv 契约的 Qfloor 具体
   见证——N 指标＝具体自然数 S(uabS4b_arch_N u)，零 Qarchimedean 不透明位。
   S10:2971 消费面（destruct q_arch_inv (eps/lp_four) 后 exists N1）的
   N1 即可以此具体值实例化（plain-Qlt 面经 QltT_to_Qlt 一步转换层入槽）。 *)
Corollary qfd_arch_inv_instT : forall u : Q, QltT 0 u ->
  sigT (fun N : nat => QltT (1 / (Z.of_nat (N + 2) # 1)) u).
Proof.
  intros u Hu. exists (Datatypes.S (uabS4b_arch_N u)).
  apply qfd_arch_inv_core. exact Hu.
Qed.

(* ============================================================ *)
(* Part B · C.1 门纵深：+2 槽移单位分数降容过 Qabs 门                       *)
(* ============================================================ *)

(* B.1 门纵深：Qabs(1/(S(arch_N u)+2)#1) <T u——尾句 exact C.1 门
   （uaq_qfloor_abs_margin），即 +2 槽移分数在 C.1 门内单位分数之下。
   Qabs 换形全走 Qabs_pos/Qabs_wd（非负门 uabS4b_null_nonneg 承接）。 *)
Corollary qfd_pi_margin_absT : forall u : Q, QltT 0 u ->
  QltT (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1))) u.
Proof.
  intros u Hu.
  assert (Hstep : QleT' (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)))
                        (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))).
    - apply qeq_le.
      apply (Qeq_trans _ (Qabs (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))))).
      + apply Qabs_wd.
        assert (Hzk1 : 1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)
                       == (1#(Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1)))%Q).
        { assert (Hzk : Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2)
                        = Z.pos (Pos.of_succ_nat (Datatypes.S (uabS4b_arch_N u) + 1))).
          { rewrite uabS4b_pos_succ_Z. lia. }
          rewrite Hzk. reflexivity. }
        exact Hzk1.
      + apply Qabs_pos. apply uabS4b_null_nonneg.
    - apply (Qle_trans _ (1#(Pos.of_succ_nat (uabS4b_arch_N u)))).
      + apply uabS4b_null_mono. lia.
      + apply qeq_le.
        apply (Qeq_sym (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))
                       (1#(Pos.of_succ_nat (uabS4b_arch_N u)))).
        apply Qabs_pos. apply uabS4b_null_nonneg. }
  apply (qleT'_ltT_ltT
           (Qabs (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N u) + 2) # 1)))
           (Qabs (1#(Pos.of_succ_nat (uabS4b_arch_N u))))
           u).
  - exact Hstep.
  - exact (uaq_qfloor_abs_margin u Hu).
Qed.

(* ============================================================ *)
(* Part C · 槽①下游四倍链：S10:2936 sc_lp_four_arch_lt 本位消费            *)
(* ============================================================ *)

(* C.1 π-Leibniz 四倍尾量：lp_four · 1/(S(arch_N(eps/lp_four))+2)#1 <T eps。
   消费 S10:2993/3016 的 sc_lp_four_arch_lt 本位（plain-Qlt 面）——
   N 位以 Qfloor 具体指标实例化，eps/lp_four 正性证书逐字复刻 S10:2966-2970。 *)
Corollary qfd_pi_four_marginT : forall eps : Q, QltT 0 eps ->
  QltT (lp_four * (1 / (Z.of_nat (Datatypes.S (uabS4b_arch_N (eps / lp_four)) + 2) # 1))) eps.
Proof.
  intros eps Hep.
  assert (Hq4 : QltT 0 (eps / lp_four)).
  { apply Qlt_to_QltT. unfold Qdiv.
    apply (Qmult_lt_0_compat eps (Qinv lp_four)).
    - apply QltT_to_Qlt. exact Hep.
    - apply Qinv_lt_0_compat. exact sc_lp_four_pos. }
  apply Qlt_to_QltT.
  apply (sc_lp_four_arch_lt eps (Datatypes.S (uabS4b_arch_N (eps / lp_four)))).
  - exact (QltT_to_Qlt _ _ Hep).
  - apply QltT_to_Qlt. apply (qfd_arch_inv_core (eps / lp_four) Hq4).
Qed.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零外部未证假设）                                *)
(* ============================================================ *)

Print Assumptions qfd_arch_inv_core.
Print Assumptions qfd_arch_inv_instT.
Print Assumptions qfd_pi_margin_absT.
Print Assumptions qfd_pi_four_marginT.
