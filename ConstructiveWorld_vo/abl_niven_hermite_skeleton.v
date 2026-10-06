(* ===================================================================== *)
(* abl_niven_hermite_skeleton —— Niven–Hermite 无理性证明五段式泛型骨架件      *)
(*                                                                        *)
(* 使命: 形式化两座无理性塔共有结构——π 塔（Hermite 1873 插值恒等式 +        *)
(*   Niven 1947 多项式核）与 ln2 塔（Beukers 型积分核）——共有的五段式结构：  *)
(*   ①多项式核构造 ②整性引理 ③余项/尾项上界 ④极限/积分面 ⑤无理性夹逼，      *)
(*   本件将其首次抽象为单一泛型机器。关键抽象为「缩放隙族」：目标实数的      *)
(*   有理逼近残差 gap n，配缩放因子族 dscale n。机器的语句面只依赖②③④的    *)
(*   下游面（缩放隙整性、隙受界、隙正性），⑤段出口对所有实例一致：          *)
(*   nhs_exit_machine —— 缩放隙既是有理数域整数、又严格落入 (0,1)，         *)
(*   故矛盾门 nhs_int_gap_gate 实例化消解。①核槽作为②的输入源以义务清单登记：*)
(*   每槽实例须供给何物逐条显式（零悬置设计）。首段实例绑定 ln2 塔：        *)
(*   核槽（Beukers 核 num/den 求值律）、整槽（lcm 缩放整性）、界槽          *)
(*   （几何尾界引擎）。                                                    *)
(*                                                                        *)
(* 依赖: Stdlib QArith/Qring/Qfield/List/Arith/ZArith/Lia/Extraction       *)
(*   + S01_BaseRing（Set 层 Id）+ S02_CauchyComplete（QeqT/QleT'/QltT 及桥） *)
(*   首段实例层：PolyIntegral（pint_eval）/S03_QExp（q_pow）/BeukersLists/   *)
(*   HansonLcm（hl_lcm_upto）/BeukersVariant（bv_p——见订正注记：Import 不    *)
(*   传递，前次死点即漏 Require 本件）/Ln2Integrality +                     *)
(*   abl_qpoly_divmod / abl_qpoly_divmod_gen /                              *)
(*   abl_ln2_numer_int / abl_ln2_qpoly_consume（核 lnc_bk_num/den、整 lni_） *)
(*   + abl_ln2_tail_bound / abl_ln2_sharp_weight（界 lnw_wgap_geo）。        *)
(*                                                                        *)
(* 对标: C. Hermite, C. R. Acad. Sci. Paris 77 (1873)（插值恒等式）；       *)
(*   I. Niven, Bulletin Amer. Math. Soc. 53 (1947)（π 无理性五段式原型）；   *)
(*   F. Beukers (1980)（ln2 积分核，工程注册引用未在线复核）。               *)
(*   两塔源面：π 塔 LW2Hermite/LW2NivenInt/LW2UpperBound/LW0PiIrrational；   *)
(*   ln2 塔 abl_ln2_qpoly_consume/abl_ln2_numer_int/abl_ln2_sharp_weight。   *)
(*                                                                        *)
(* 构造性: 零公理零承认零经典。语句面全部 Set 载体形（Id/sigT/QeqT/         *)
(*   QleT'/QltT）；Prop 层仅出现在证内脚手架（Qeq 降档桥、Z 算术叶位 lia）。  *)
(*   主机器 nhs_exit_machine 证明为显式构造链（合流三定理 + 矛盾门），        *)
(*   无 solver 收尾。每槽 Hypothesis 均为 Set 型并附实例化义务清单。          *)
(*                                                                        *)
(* 编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&         *)
(*   ulimit -s 65532；起编前道闸 ps rocq 计 ≤1；链序：                       *)
(*   abl_qpoly_divmod → abl_qpoly_divmod_gen → abl_ln2_numer_int →          *)
(*   abl_ln2_qpoly_consume → abl_ln2_tail_bound → abl_ln2_sharp_weight       *)
(*   → 本件；配方 nice -19 rocq c -native-compiler no                        *)
(*   -Q /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 "" *)
(*   -Q . "" <件>.v（订正注记：统一缓存根 ConstructiveWorld_vo 之 S01 与      *)
(*   当前 Corelib 假设不一致，改挂 vo_local_world_unified_0930 根，           *)
(*   该根 BeukersVariant 含 bv_p，实测绿）。                                  *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete.

(* ------------------------------------------------------------------ *)
(* §1 整槽通用输入件：有限有理和的整数见证闭包                            *)
(*    （两塔 §② 的公共内脏：π 塔侧对应 lw2i_qsum0_zmap_gen，             *)
(*      ln2 塔侧对应 lni_psQ_zsum_ex；此处首次以塔无关形式孤立）           *)
(* ------------------------------------------------------------------ *)

Fixpoint nhs_qsum (m : nat) (g : nat -> Q) : Q :=
  match m with
  | Datatypes.O => 0%Q
  | Datatypes.S m' => (nhs_qsum m' g + g m')%Q
  end.

(* 义务登记（零悬置）：本定理使用的假设恰为「逐项整数见证」——
   实例塔对每项 g k 供 Z 见证 z_k 及 QeqT (g k) (z_k # 1)。 *)
Theorem nhs_zsum_wit : forall (m : nat) (g : nat -> Q),
  (forall k : nat, sigT (fun z : Z => QeqT (g k) ((z # 1)%Q))) ->
  sigT (fun z : Z => QeqT (nhs_qsum m g) ((z # 1)%Q)).
Proof.
  intros m. induction m as [|m IHm]; intros g Hall.
  - exists 0%Z. apply qeq_imp_qeqT. reflexivity.
  - destruct (IHm g Hall) as [z1 H1].
    destruct (Hall m) as [z2 H2].
    exists (z1 + z2)%Z.
    cbn [nhs_qsum].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ H1).
    rewrite (qeqT_imp_qeq _ _ H2).
    unfold Qeq. cbn [Qnum Qden Qplus Pos.mul]. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* §2 ⑤段矛盾门：整数落入开区间 (0,1) 的构造性否证                         *)
(*    （π 塔出口 lw0_pi_irrational_exit 与 ln2 塔装配门共用的原子机器；     *)
(*      此处首次以 Z/Q 显式形式孤立）                                      *)
(* ------------------------------------------------------------------ *)

Theorem nhs_int_gap_gate : forall z : Z,
  QltT 0 ((z # 1)%Q) -> QltT ((z # 1)%Q) 1 -> Id false true.
Proof.
  intros z Hpos Hlt.
  assert (H0 : Qlt 0 ((z # 1)%Q)) by exact (QltT_to_Qlt 0 ((z # 1)%Q) Hpos).
  assert (H1 : Qlt ((z # 1)%Q) 1) by exact (QltT_to_Qlt ((z # 1)%Q) 1 Hlt).
  unfold Qlt in H0, H1.
  cbn [Qnum Qden] in H0, H1.
  assert (Hc : False) by lia.
  destruct Hc.
Qed.

(* ------------------------------------------------------------------ *)
(* §3 泛型五段式骨架 Section：接口参数 + 实例化义务清单 + ⑤段出口机器       *)
(*                                                                        *)
(*   槽 D（缩放族，②段出口面） dscale : nat -> Z                            *)
(*     义务 D-1：逐 n 缩放因子正性（hD_pos）。                              *)
(*     义务 D-2：实例塔须说明 dscale n 的算术来源                           *)
(*       （π 塔实例：分母幂 b^n；ln2 塔实例：前 n 项最小公倍数）。           *)
(*   槽 G（隙族，④段输出面）   gapf : nat -> Q                              *)
(*     义务 G-1：逐 n 隙正性（hgap_pos，⑤段前置）。                         *)
(*     义务 G-2：实例塔须供给核恒等式使 gapf 良定义                         *)
(*       （π 塔实例：Hermite 恒等式 lw2_lambda = lw2_endpoint 之残差面；     *)
(*        ln2 塔实例：Beukers 核积分残差真族面）。                          *)
(*   槽 I（整性，②段输入）                                                *)
(*     义务 I-1：缩放隙整性 sigT 见证（hint）——由①核构造 + ②整性引理       *)
(*       联合输入；通用输入件见 §1 nhs_zsum_wit。                           *)
(*   槽 B（界，③段输入）    bndf : nat -> Q                                *)
(*     义务 B-1：隙受界 QleT'（hbnd）。                                    *)
(*     义务 B-2：缩放×界趋于 1 之下（hbnd_van）——实例塔由尾项上界引擎       *)
(*       供给（π 塔实例：LW2UpperBound；ln2 塔实例：几何尾界 lnw_wgap_geo    *)
(*       与 θ 预算）。                                                     *)
(* ------------------------------------------------------------------ *)

Section NivenHermiteSkeleton.

  Variable dscale : nat -> Z.
  Variable gapf : nat -> Q.
  Variable bndf : nat -> Q.

  Hypothesis hD_pos : forall n : nat, QltT 0 ((dscale n # 1)%Q).
  Hypothesis hint : forall n : nat,
    sigT (fun z : Z => QeqT ((dscale n # 1)%Q * gapf n)%Q ((z # 1)%Q)).
  Hypothesis hbnd : forall n : nat, QleT' (gapf n) (bndf n).
  Hypothesis hbnd_van : forall n : nat,
    QltT ((dscale n # 1)%Q * bndf n)%Q 1.
  Hypothesis hgap_pos : forall n : nat, QltT 0 (gapf n).

  (* 缩放隙正性：D > 0 与隙 > 0 的乘法传递 *)
  Theorem nhs_scaled_gap_pos : forall n : nat,
    QltT 0 ((dscale n # 1)%Q * gapf n)%Q.
  Proof.
    intro n. apply qmult_ltT_0_compat.
    - apply hD_pos.
    - apply hgap_pos.
  Qed.

  (* 缩放隙严格小于 1：隙 ≤ 界 与 缩放×界 < 1 的合流 *)
  Theorem nhs_scaled_gap_lt1 : forall n : nat,
    QltT ((dscale n # 1)%Q * gapf n)%Q 1.
  Proof.
    intro n.
    apply (qleT'_ltT_ltT _ ((dscale n # 1)%Q * bndf n)%Q 1).
    - apply qleT'_mult_compat_l.
      + apply qltT_leT'. apply hD_pos.
      + apply hbnd.
    - apply hbnd_van.
  Qed.

  (* ⑤段出口机器：任取 n，缩放隙是有理整数域元素且严格落入 (0,1)。 *)
  Theorem nhs_exit_machine : forall n : nat, Id false true.
  Proof.
    intro n.
    destruct (hint n) as [z Hz].
    apply (nhs_int_gap_gate z).
    - pose proof (nhs_scaled_gap_pos n) as Hp.
      apply QltT_to_Qlt in Hp.
      rewrite (qeqT_imp_qeq _ _ Hz) in Hp.
      apply Qlt_to_QltT. exact Hp.
    - pose proof (nhs_scaled_gap_lt1 n) as Hl.
      apply QltT_to_Qlt in Hl.
      rewrite (qeqT_imp_qeq _ _ Hz) in Hl.
      apply Qlt_to_QltT. exact Hl.
  Qed.

End NivenHermiteSkeleton.

(* ------------------------------------------------------------------ *)
(* §4 首段实例：ln2 塔三槽绑定面                                          *)
(*   核槽（①）：Beukers 核 t^n(1−t)^n / (1−t/2)^(n+1) 的 QPoly 编码        *)
(*     lnc_bk_num / lnc_bk_den 及其求值律（义务 D-2/G-2 的 ln2 供面）。     *)
(*   整槽（②）：lcm 缩放整性 lni_bvp_lcm_int —— 缩放隙有理整数域见证，      *)
(*     与槽 I 义务 I-1 的语句面逐字同形。                                  *)
(*   界槽（③）：几何尾界引擎 lnw_wgap_geo —— 权重项和的几何包络。           *)
(* ------------------------------------------------------------------ *)

Require Import PolyIntegral S03_QExp BeukersLists HansonLcm BeukersVariant
  Ln2Integrality.
Require Import abl_qpoly_divmod abl_qpoly_divmod_gen.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_qpoly_consume.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.

(* 核槽实例·分子求值律：num 之求值 = (x(1−x))^n *)
Theorem nhl2_kernel_num_eval : forall (n : nat) (x : Q),
  QeqT (pint_eval (lnc_bk_num n) x) (q_pow (x * (1 - x)) n).
Proof.
  intros n x. apply qeq_imp_qeqT. apply lnc_bk_num_eval.
Qed.

(* 核槽实例·分母求值律：den 之求值 = (1−x/2)^(n+1)（u=1−x/2 极点坐标） *)
Theorem nhl2_kernel_den_eval : forall (n : nat) (x : Q),
  QeqT (pint_eval (lnc_bk_den n) x)
       (q_pow (1 + x * (-(1 # 2))) (Datatypes.S n)).
Proof.
  intros n x. apply qeq_imp_qeqT. apply lnc_bk_den_eval.
Qed.

(* 整槽实例：缩放隙整性 —— dscale := 前 n 项 lcm，gapf := Beukers 残差。
   语句面与 §3 槽 I 义务 I-1 同形：(L_n # 1) * bv_p n 有 Z 见证。 *)
Theorem nhl2_int_slot_product : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((Z.of_nat (hl_lcm_upto n) # 1)%Q * bv_p n)%Q ((z # 1)%Q)).
Proof.
  intro n. exact (lni_bvp_lcm_int n).
Qed.

(* 界槽实例：几何尾界引擎（权重项和的几何包络，ln2 塔 §③ 供面） *)
Theorem nhl2_bound_slot : forall (n M d : nat),
  1 <= n -> 2 * n <= M + 1 ->
  QleT' (sum_upto (Datatypes.S (M + d)) (fun k : nat => lnw_wterm n k))
        (sum_upto (Datatypes.S M) (fun k : nat => lnw_wterm n k)
           + (q_pow (2 # 1)%Q (Datatypes.S (Datatypes.S (Datatypes.S n)))
                * q_pow (3 # 4)%Q (Datatypes.S M - 2 * n))%Q)%Q.
Proof.
  intros n M d Hn HM. exact (lnw_wgap_geo n M d Hn HM).
Qed.

(* ------------------------------------------------------------------ *)
(* §5 提取检验区与假设审计                                                *)
(* ------------------------------------------------------------------ *)

Separate Extraction nhs_zsum_wit nhs_int_gap_gate nhs_exit_machine
  nhl2_kernel_num_eval nhl2_int_slot_product.

Print Assumptions nhs_zsum_wit.
Print Assumptions nhs_int_gap_gate.
Print Assumptions nhs_scaled_gap_pos.
Print Assumptions nhs_scaled_gap_lt1.
Print Assumptions nhs_exit_machine.
Print Assumptions nhl2_kernel_num_eval.
Print Assumptions nhl2_kernel_den_eval.
Print Assumptions nhl2_int_slot_product.
Print Assumptions nhl2_bound_slot.
