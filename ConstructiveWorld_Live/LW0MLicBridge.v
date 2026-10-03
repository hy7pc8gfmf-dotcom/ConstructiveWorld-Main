(* 五字段指针｜使命：M0+ 母判据适配先行波三件——槽 1 tail 供给 lw0m_tail_bounded_pi（lic_tail_bounded 实例）、槽 2 vanish 供给 lw0m_vanish_pi（lic_vanish 实例）、real_metric 同余件 lw0m_metric_congr（未竟#2 通用解）。依据 M0 母判据适配设计书（attn\_tlw25 系）§一映射表与分段授权：槽 3（lw0m_escape_export）硬门槛候 lw0_pi_irrational 落 .vo 且机械验证通过，本件不做不凑。 依赖：PiEnvelope（pie_tail4/pie_modulus/pie_modulus_bound/pie_v_eq/pie_mag_pos/pie_mag_antitone）、UpReqIrrationalCriterion（lic_tail_bounded/lic_vanish/Qlt_to_QltT/QltT_to_Qlt）、S02_CauchyComplete（real_eq/QltT/Real）、S03_QExp（real_metric/q_abs_abs_triangle）、S10_KVQuantTrig（lp_four/lp_odd/cauchy_real_pi_leibniz）。 构造性：零承认式语句（机械核验）；语句面全 Set 层零 Prop 泄露（lic 两接口与 real_eq 均 Set 值形），证内 Prop（Qlt/Qle）仅作脚手架不进结论面；Qlt↔QltT 换形仅在两实例各一处（设计书坑位 2）；统一窗 lw0m_e n := 5 * pie_mag n 三槽共享（设计书坑位 3），槽 3 装配同用此名。 编译配方：coqc -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" LW0MLicBridge.v。 命名：lw0m_ 前缀（主会话已裁；全树 grep -w 查重零占用）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lqa.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.

(* ============================================================ *)
(* §0 统一窗与 π_L 投影序列（设计书 §一 统一记号）                  *)
(* ============================================================ *)

(* 统一窗：e n := 5 * pie_mag n（三槽共享；系数 5 吸收两处索引抬升） *)
Definition lw0m_e (n : nat) : Q := 5 * pie_mag n.

(* π_L 投影序列：xL n := lp_four * lp_odd n
   （= projT1 cauchy_real_pi_leibniz n，定义性；S10 同式） *)
Definition lw0m_xL (n : nat) : Q := lp_four * lp_odd n.

(* ============================================================ *)
(* §1 槽 1：tail 桥（设计书 §一 映射表行 1）                        *)
(* pie_tail4 非严格 Qle + 1×pie_mag 余量 ⟹ 严格 QltT；            *)
(* 索引抬升 pie_mag(2n+2) ⟹ pie_mag n（pie_mag_antitone）；        *)
(* 序列接缝 pie_v_eq（lp_four * lp_odd · ⟹ 4 * pie_partial(2·+2)）。 *)
(* ============================================================ *)
Definition lw0m_tail_bounded_pi : lic_tail_bounded lw0m_xL lw0m_e.
Proof.
  intros n k Hn1 Hnk.
  unfold lw0m_xL, lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : Qle (pie_mag (2 * n + 2)) (pie_mag n))
    by (apply pie_mag_antitone; lia).
  pose proof (pie_mag_pos n) as Hpm.
  apply (Qle_lt_trans _ (4 * pie_mag (2 * n + 2)) _).
  - rewrite (pie_v_eq k). rewrite (pie_v_eq n).
    apply (pie_tail4 (2 * n + 2) (2 * k + 2)). lia.
  - lra.
Qed.

(* ============================================================ *)
(* §2 槽 2：vanish 桥（设计书 §一 映射表行 2）                      *)
(* 模量重标定 N := pie_modulus (eps / 10)（pie_modulus 天然配      *)
(* 4 系窗，lic 窗是 5 系）；单点界 ⟹ 最终界经 pie_mag_antitone；   *)
(* QltT↔Qlt 双换形器各一处（前提换入＋结论换出）。                 *)
(* ============================================================ *)
Definition lw0m_vanish_pi : lic_vanish lw0m_e.
Proof.
  intros eps Heps.
  pose proof (QltT_to_Qlt 0%Q eps Heps) as Heps0.
  assert (Hd10 : Qlt 0 (eps * (1 # 10))) by lra.
  assert (Hb : Qlt (4 * pie_mag (pie_modulus (eps * (1 # 10))))
                   (eps * (1 # 10)))
    by (apply pie_modulus_bound; exact Hd10).
  exists (pie_modulus (eps * (1 # 10))).
  intros n Hn.
  unfold lw0m_e.
  apply Qlt_to_QltT.
  assert (Hanti : Qle (pie_mag n)
                      (pie_mag (pie_modulus (eps * (1 # 10)))))
    by (apply pie_mag_antitone; exact Hn).
  lra.
Qed.

(* ============================================================ *)
(* §3 real_metric 同余件（_tlw19 未竟#2 通用解；设计书 §三）        *)
(* 逐 eps 构造：反三角 q_abs_abs_triangle 单步给界；                *)
(* 投影定义性展开 real_metric := real_abs (real_plus x             *)
(* (real_opp z))（S03，Defined 透明）。                            *)
(* ============================================================ *)
Lemma lw0m_metric_congr : forall (x y z : Real), real_eq x y ->
  real_eq (real_metric x z) (real_metric y z).
Proof.
  intros x y z Hxy.
  destruct x as [u Hu]. destruct y as [v Hv]. destruct z as [w Hw].
  intros eps Heps.
  destruct (Hxy eps Heps) as [N HN].
  exists N. intros n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _ (Qabs (u n - v n)) _).
  - cbv beta iota delta [real_metric real_abs real_plus real_opp].
    assert (Hr : (u n - v n == u n - w n - (v n - w n))%Q) by ring.
    rewrite Hr.
    apply q_abs_abs_triangle.
  - apply QltT_to_Qlt. exact (HN n Hn).
Qed.
