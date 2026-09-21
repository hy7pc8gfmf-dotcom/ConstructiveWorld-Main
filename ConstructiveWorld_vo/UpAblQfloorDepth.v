(* ============================================================ *)
(* ToyR 玩具证替换件 —— T267 台账席 战役包AB（tier2 十八批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   qfd_arch_inv_instT（原 L102，4 句玩具证）                            *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblQfloorDepth.v —— S10 尾界链 N 指标实例化的单位分数供给件 *)
(*                                                                *)
(* 使命：本件形式化柯西型尾界中阿基米德指标位的可实例化性——对任意 *)
(*   正有理数 u，取具体自然数指标 N := S(uabS4b_arch_N u)，即得   *)
(*   单位分数下界 1/(N+2)#1 <T u；并沿 π-Leibniz 四倍尾量链给出   *)
(*   绝对值之下的界与 lp_four 尾量的 QltT 面实例（qfd_ 前缀四件）。 *)
(*                                                                *)
(* 供给结构（四件）：                                              *)
(*   A 单位分数核：qfd_arch_inv_core——N := S(uabS4b_arch_N u) 时  *)
(*      1/(N+2)#1 <T u（QltT 面）；以及                           *)
(*      qfd_arch_inv_instT——q_arch_inv 结论形 sigT(N, 1/(N+2) < u) *)
(*      的具体实例（指标为具体自然数，无阿基米德不透明环节）；     *)
(*   B 绝对值下的界：qfd_pi_margin_absT——Qabs(1/(N+2)#1) <T u，  *)
(*      归约到 uaq_qfloor_abs_margin 给出的单位分数绝对值界；      *)
(*   C 四倍尾量链：qfd_pi_four_marginT——应用 sc_lp_four_arch_lt， *)
(*      指标取 N := S(uabS4b_arch_N(eps/lp_four))，得             *)
(*      lp_four · 1/(N+2)#1 <T eps。                              *)
(*                                                                *)
(* 范围注记（构造性边界）：本件只供单位分数形式的指标位——         *)
(*   其一，q_arch_geom 基指标位（调和形 sigT(N, forall t ≥ N,     *)
(*   2B ≤ (t+1)#1)）：由 1/(uabS4b_arch_N(Qinv(2B))+1) <T 1/(2B)  *)
(*   反演到 2B < (M+1)#1 受阻——Qinv 的 Zneg 三支 match 阻断       *)
(*   定义性改写（Qinv x ≢ Qmake (QDen x) (Qnum x)），且 Q 层      *)
(*   尚缺 Qeq 右改写引理与 Qinv-Qdiv 桥接引理，属后续工作；        *)
(*   其二，arch_decay 衰减位（(1/2)^{S t} 几何衰减形）：           *)
(*   非单位分数形式，本件不供；                                    *)
(*   其三，输入侧柯西模的位置：指标 N 由前提中的柯西条件全称给出， *)
(*   非阿基米德实例化位。上述边界不涉及本件四定理自身的封闭性。    *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219（q_arch_inv/q_arch_geom/        *)
(*   sc_lp_four_arch_lt/lp_four 皆在其命名空间）＋                 *)
(*   UpAblAbsSumLeB2（uabS4b_ 单位分数下界引理族）＋               *)
(*   UpAblAbsQFeed（uaq_qfloor_abs_margin 之界）。                 *)
(* 对标：stdlib QArith/Lqa（有理数序、绝对值与乘法保序引理）。     *)
(* 构造性注记：全件 Set 层承载（QltT/QleT'＝Qlt/Qle 加 sigT 见证），*)
(*   零承认词面、无经典逻辑；Qeq/Z 改写全部内联于证明内部，        *)
(*   语句面无裸命题；四定理 Print Assumptions 全 Closed，可提取。  *)
(* 编译配方：Rocq 9.1 coqc 直调，cpu_guard -LoadLimit 85 -CoreN 2  *)
(*   包裹，输出经 -o 临时目录，树内 .vo 不重写。                   *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpAblAbsSumLeB2.
Require Import UpAblAbsQFeed.

(* ============================================================ *)
(* §0 · 依赖签名核验（所引标识符漂移即编译期暴露） *)
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
(* §A · 单位分数核：N := S(uabS4b_arch_N u) 满足 q_arch_inv 结论形      *)
(* ============================================================ *)

(* A.1 核引理：N := S(uabS4b_arch_N u) 时 1/(N+2)#1 <T u。证明链：
   uabS4b_null_lt 给 1/(n+1) <T u；uabS4b_null_mono 给
   1/(n+2) ≤ 1/(n+1)；再以 Z 恒等式 uabS4b_pos_succ_Z 作 Qeq 改写成 #1 分母形。 *)
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

(* A.2 结论形实例：q_arch_inv 结论所要求的 sigT(N, 1/(N+2)#1 < u) 形的
   具体见证——指标取具体自然数 S(uabS4b_arch_N u)，无阿基米德不透明环节。
   下游凡对 q_arch_inv (eps / lp_four) 作 destruct 后以 exists 供证的
   见证位，均可以此具体值实例化；plain-Qlt 面经 QltT_to_Qlt 一步转换即得。 *)
Corollary qfd_arch_inv_instT : forall u : Q, QltT 0 u ->
  sigT (fun N : nat => QltT (1 / (Z.of_nat (N + 2) # 1)) u).
Proof.
  intros u Hu.
  exists (Datatypes.S (uabS4b_arch_N u)).
  apply qfd_arch_inv_core.
  exact Hu.
Qed.

(* ============================================================ *)
(* §B · 绝对值下的界：Qabs(1/(N+2)#1) <T u                              *)
(* ============================================================ *)

(* B.1 绝对值界：Qabs(1/(S(uabS4b_arch_N u)+2)#1) <T u——先证
   Qabs(1/(n+2)#1) ≤ Qabs(1/(n+1)#1)（n := uabS4b_arch_N u，经
   qeq_le/Qabs_wd/Qabs_pos），尾句 exact uaq_qfloor_abs_margin 收尾。 *)
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
(* §C · 四倍尾量：lp_four · 1/(N+2)#1 <T eps                            *)
(* ============================================================ *)

(* C.1 π-Leibniz 四倍尾量：应用 sc_lp_four_arch_lt（plain-Qlt 面，经
   QltT_to_Qlt 转换），指标以 N := S(uabS4b_arch_N(eps/lp_four)) 实例化；
   eps/lp_four 的正性由 Qmult_lt_0_compat、Qinv_lt_0_compat 与 sc_lp_four_pos 推得。 *)
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
(* §D · 假设审计：四定理 Print Assumptions 全 Closed（零外部未证假设）      *)
(* ============================================================ *)

Print Assumptions qfd_arch_inv_core.
Print Assumptions qfd_arch_inv_instT.
Print Assumptions qfd_pi_margin_absT.
Print Assumptions qfd_pi_four_marginT.
