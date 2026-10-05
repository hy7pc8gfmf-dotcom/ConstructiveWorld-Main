(* 五字段指针｜使命：M0+ 槽 3 适配件骨架——主语句到母判据 lic_irrational_criterion
   出口形的定点适配（条件形）。主语句 lw0_pi_irrational 真名在件直代：合入
   按 _tlw181 交接单 §三.2 删暂替（Set 型 Section Variable 块整删），Require 面
   追加 LW0PiIrrational 后取用名同铭直代，End 抽象首参自动消失，二三两件收
   两参形，非公理壳（PREFILLRUN 判例同构，coqchk 零公理属预期）。裁决依据：_tlw132 形态冲突三选一预登记
   (a)（单前提出口件，M0 侧证能）未落；终装配两前提形落地下五步流水线步①②
   不可达（Hp : real_eq real_pi_geom (real_const (a/b)) 施工面无从供给），
   本件按条件形落地——单前提出口件注册后按交接单升全量形 lic_escape_window。
   依赖：LW0MLicBridge（lw0m_xL/lw0m_e/lw0m_tail_bounded_pi/lw0m_vanish_pi/
   lw0m_metric_congr）、LW2TrigBridge（lw2_channel_f1_closed）、
   S01_BaseRing（NatLe_lift）、S02_CauchyComplete（Qseq/Real/real_eq/real_lt/
   real_const）、S10_KVQuantTrig（cauchy_real_pi_leibniz/real_pi_leibniz_proj）、
   PiEnvelope、UpReqIrrationalCriterion（lic_seq_cauchy/lic_metric_proj/
   QltT_to_Qlt/Qlt_to_QltT）。
   构造性：零承认式语句；语句面全 Set 层（sigT/And/QltT/real_lt 均 Set 值形）；
   证内 Prop（Qlt）仅作脚手架，出口前经 Qlt_to_QltT 回 Set 层，零 Prop 渗入结论面。
   编译配方：coqc -q -Q <本件目录> "" -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" LW0LicAdapt.v（cpu_guard 包裹＋python 列表传参）。
   命名：lw0m_ 前缀沿用 LW0MLicBridge 在册五名；本件新增 lw0m_pack_congr/
   lw0m_lic_inst_pi_cond/lw0m_escape_at_cond 三名（开工 grep -w 三树查重零占用）。 *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Lia Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import UpReqIrrationalCriterion.
Require Import LW0MLicBridge.
Require Import LW0PiIrrational.
Require Import LW2TrigBridge.

Section LW0LicAdaptSkel.

(* ---------- 一、装包同构：π_L 绿件装包与母判据装包逐点定义性同 ---------- *)
(* 母判据出口的实数装包是 existT lw0m_xL (lic_seq_cauchy ...)，与绿件
   cauchy_real_pi_leibniz 序列同为 lp_four * lp_odd n，real_eq 零成本。 *)
Lemma lw0m_pack_congr :
  real_eq cauchy_real_pi_leibniz
    (existT (fun u : Qseq => cauchy u) lw0m_xL
       (lic_seq_cauchy lw0m_xL lw0m_e
          lw0m_tail_bounded_pi lw0m_vanish_pi)).
Proof.
  intros eps Heps.
  exists 1%nat. intros n Hn.
  apply Qlt_to_QltT.
  rewrite (real_pi_leibniz_proj n). cbn [projT1]. unfold lw0m_xL.
  assert (Hz : (lp_four * lp_odd n - lp_four * lp_odd n)%Q == 0) by ring.
  rewrite Hz.
  assert (Hz2 : Qabs 0 == 0) by reflexivity.
  rewrite Hz2. exact (QltT_to_Qlt 0%Q eps Heps).
Qed.

(* ---------- 二、母判据 π 定点实例（条件形）：出口相离见证跨装包传输 ---------- *)
(* 结论形＝lic_irrational_criterion lw0m_xL lw0m_e 两绿件的出口在 q:=a/b
   的定点实例；M0 出口见证经两次 real_lt_eq_lt 传输（先 lw0m_metric_congr
   跨 π_geom 到 π_L，再 lw0m_pack_congr 跨装包），零新分析内容。 *)
Lemma lw0m_lic_inst_pi_cond :
  forall a b : Q,
    QltT 0 (Qabs b) ->
    real_eq real_pi_geom (real_const (a / b)) ->
    sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c)
         (real_metric (existT (fun u : Qseq => cauchy u) lw0m_xL
                         (lic_seq_cauchy lw0m_xL lw0m_e
                            lw0m_tail_bounded_pi lw0m_vanish_pi))
                      (real_const (a / b))))).
Proof.
  intros a b Hb Hp.
  destruct (lw0_pi_irrational a b Hb Hp) as [c [Hc0 Hlt]].
  pose proof (lw0m_metric_congr real_pi_geom cauchy_real_pi_leibniz
                (real_const (a / b)) lw2_channel_f1_closed) as Hmc.
  pose proof (real_lt_eq_lt (real_const c)
                (real_metric real_pi_geom (real_const (a / b)))
                (real_metric cauchy_real_pi_leibniz (real_const (a / b)))
                Hlt Hmc) as Hlt1.
  pose proof (lw0m_metric_congr cauchy_real_pi_leibniz
                (existT (fun u : Qseq => cauchy u) lw0m_xL
                   (lic_seq_cauchy lw0m_xL lw0m_e
                      lw0m_tail_bounded_pi lw0m_vanish_pi))
                (real_const (a / b)) lw0m_pack_congr) as Hpk.
  pose proof (real_lt_eq_lt (real_const c)
                (real_metric cauchy_real_pi_leibniz (real_const (a / b)))
                (real_metric (existT (fun u : Qseq => cauchy u) lw0m_xL
                                (lic_seq_cauchy lw0m_xL lw0m_e
                                   lw0m_tail_bounded_pi lw0m_vanish_pi))
                             (real_const (a / b)))
                Hlt1 Hpk) as Hlt2.
  exists c. split.
  - exact Hc0.
  - exact Hlt2.
Qed.

(* ---------- 三、槽 3 五步流水线定点形（条件）：逃逸窗在点 a/b ---------- *)
(* 步③（黄金通道展开）＋步④（投影 lic_metric_proj，装包位已就绪免再跨岸）
   ＋步⑤（窗宽消失取 N2、max 终结）；Qabs 对称经 Qabs_Qminus 一次对齐，
   Q 层闭合 lra（QltT 前提位 Qlt_to_QltT 回 Set 层）。 *)
Lemma lw0m_escape_at_cond :
  forall a b : Q,
    QltT 0 (Qabs b) ->
    real_eq real_pi_geom (real_const (a / b)) ->
    sigT (fun n : nat => And ((1 <= n)%nat)
            (QltT (lw0m_e n) (Qabs ((a / b - lw0m_xL n)%Q)))).
Proof.
  intros a b Hb Hp.
  destruct (lw0m_lic_inst_pi_cond a b Hb Hp) as [c [Hc0 Hlt]].
  destruct Hlt as [d [Hd0 [N1 HN1]]].
  destruct (lw0m_vanish_pi d Hd0) as [N2 HN2].
  exists (Nat.max N1 (Nat.max N2 1%nat)). split.
  - lia.
  - assert (Hle1 : NatLe N1 (Nat.max N1 (Nat.max N2 1%nat)))
      by (apply NatLe_lift; lia).
    assert (Hn2 : (N2 <= Nat.max N1 (Nat.max N2 1%nat))%nat) by lia.
    pose proof (HN1 _ Hle1) as HQ1.
    pose proof (QltT_to_Qlt _ _ HQ1) as HQ1'.
    rewrite lic_metric_proj in HQ1'.
    cbn [projT1 real_const] in HQ1'.
    rewrite (Qabs_Qminus (lw0m_xL (Nat.max N1 (Nat.max N2 1%nat))) (a / b))
      in HQ1'.
    pose proof (HN2 _ Hn2) as HQ2.
    pose proof (QltT_to_Qlt _ _ HQ2) as HQ2'.
    pose proof (QltT_to_Qlt 0%Q c Hc0) as Hcp.
    apply Qlt_to_QltT.
    unfold lw0m_e in HQ2' |- *. lra.
Qed.

End LW0LicAdaptSkel.

(* ---------- 出口核对（真名直代态：二三两件两参形属预期） ---------- *)
Check lw0m_pack_congr.
Check lw0m_lic_inst_pi_cond.
Check lw0m_escape_at_cond.
Print Assumptions lw0m_pack_congr.
Print Assumptions lw0m_lic_inst_pi_cond.
Print Assumptions lw0m_escape_at_cond.
