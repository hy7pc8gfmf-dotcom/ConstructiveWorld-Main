(* 五字段指针｜模块：LW3ExclusionCalc.v。
   数学使命：圆周率有理逼近的排除见证计算器。对任意有理数 q 与分离常数 c
   （0 < c 且 c 严格小于点态距离 |pi - q|），构造自足的排除见证包 lw3x_seal：
   分离常数 c 与其正性证明、分离性证明一同封装于存在包中，附带 Leibniz 包络
   端点 [lo, hi]（pi 属于开区间 (lo, hi)，端点算式与 pi_rational_envelope 的
   见证算式逐字同源）、外侧判定布尔位 b（q < lo 时取 true）与决策支位
   sumbool (hi < q) (q < lo)。核心定理 lw3x_band_excl 给出带不相容性引理：
   端点带宽度严格小于分离半径且 lo <= q 时，逐点夹逼与分离下界不相容，
   迫使 hi < q——排除证据在左右两支中恰居其一。主定理 lw3x_calc 以参数 c
   前提位承载分离假设（无前提位版本在 q 落入包络带内时两支同时为假，
   故前提位为语句面的必要成分）。定理 lw3x_pi_geom_seal_slot 把圆周率
   几何表示 real_pi_geom 处的分离假设经两表示等价桥 channel_f1 传输到
   Leibniz 级数表示 cauchy_real_pi_leibniz（半径按传递定理减半），并以
   主定理 lw3x_calc 装成排除见证包。供给定理 lw3x_env_supply 对任意正
   eps 给出显式端点对 (lw3x_env_lo eps, lw3x_env_hi eps) 的透明承载：
   pi < hi、lo < pi 与带宽 hi - lo < eps 三位见证数据全显式。
   依赖：S01_BaseRing（Set 层 Id/And/NatLe）、S02_CauchyComplete（Real/real_lt/
   real_const/QltT/QltT_to_Qlt/Qlt_to_QltT/real_const_proj/NatLe_lift）、
   S03_QExp（real_metric/q_abs_abs_triangle）、S10_KVQuantTrig
   （cauchy_real_pi_leibniz）、UpReqIrrationalCriterion（lic_metric_proj 逐点
   投影归约）、PiEnvelope（QltT'/QltT'_to_Qlt/pie_partial/pie_modulus/
   pi_rational_envelope）、LW0LeibWindow（leiblw_Qltb/leiblw_Qltb_true/
   leiblw_Qltb_inv）、LW2SepTransport（lw2t_sep_transport：分离半径沿柯西
   等价减半）、S11_TP3B5（channel_f1：圆周率两表示的柯西等价，及其装配
   见证 a3_h4_value_bridge/b5b_hsc_theorem）、S14_B5BatchBlock
   （b5dS_E_zero_on_unit）。
   对标：Bishop 构造分析中否定命题的计算器化——对每个 q 给出显式 [lo, hi]
   排除见证包；端点算式的唯一来源为 PiEnvelope 的包络见证算式，布尔判定器
   的唯一来源为 LW0LeibWindow 的 leiblw_Qltb；逐点投影归约的唯一来源为
   UpReqIrrationalCriterion 的 lic_metric_proj；Q 层线性算术段使用 Lia/Lqa。
   构造性：语句面全 Set 层（QltT/QltT'/real_lt/sigT/And:=prod/sumbool），主定理
   证明为显式装配链，零承认、零经典逻辑、Require 面不引公理模块；计算层
   lw3x_sideb/lw3x_env_lo/lw3x_env_hi/lw3x_env_supply 全 Defined 且上游透明
   （可提取值域），
   文件尾 Separate Extraction 提取并以 Obj.magic 零命中为检验判据；证书面
   lw3x_band_excl/lw3x_calc 为Qed件，不入提取并集（其端点使用 Qed 包络
   pi_rational_envelope）。
   编译配方：coqc -q -Q . "" LW3ExclusionCalc.v，工作目录 Live_X，-Q 仅绑定
   本地 vo 库根；COQLIB 与 ROCQLIB 环境变量需同值指向 Rocq 9.1 库根；
   尾段提取产物经 Set Extraction Output Directory 落独立目录。
*)

From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia Lqa.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import UpReqIrrationalCriterion.
Require Import PiEnvelope.
Require Import LW0LeibWindow.
Require Import LW2SepTransport.
Require Import S11_TP3B5.
Require Import S14_B5BatchBlock.

(* §1 计算核：外侧判定位与包络端点选择器（全 Defined，可提取） *)

(* 外侧判定位：q < lo 时为 true。布尔判定器唯一来源为 leiblw_Qltb。 *)
Definition lw3x_sideb (q lo : Q) : bool := leiblw_Qltb q lo.

(* 包络端点选择器：与 pi_rational_envelope 的见证算式逐字同源
   （lo := 4·pie_partial(2·pie_modulus(eps/2)+2) − eps/4，
     hi := 4·pie_partial(2·pie_modulus(eps/2)+1) + eps/4）。
   上游 pie_partial/pie_modulus 均透明定义，选择器全链可提取。 *)
Definition lw3x_env_lo (eps : Q) : Q :=
  4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4.
Definition lw3x_env_hi (eps : Q) : Q :=
  4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4.

(* 判定位反映律：leiblw_Qltb 逆反映对的直接改述。 *)
Lemma lw3x_sideb_spec : forall q lo : Q, lw3x_sideb q lo = true -> Qlt q lo.
Proof.
  intros q lo H. exact (leiblw_Qltb_inv q lo H).
Qed.

(* §2 排除见证包：Set 层存在封装（常数 c 与其正性、分离性证明同包；
   And 位为 S01 的 Set 层积型，pi_rational_envelope 同面在案；
   决策支位 sumbool 为 Set 层，载荷均为命题层且在提取中擦除） *)
Definition lw3x_seal (q c : Q) : Set :=
  sigT (fun c' : Q =>
    sigT (fun _ : QltT 0 c' =>
      sigT (fun _ : real_lt (real_const c')
                       (real_metric cauchy_real_pi_leibniz (real_const q)) =>
        sigT (fun lo : Q =>
          sigT (fun hi : Q =>
            sigT (fun b : bool =>
              And (real_lt (real_const lo) cauchy_real_pi_leibniz)
                  (And (real_lt cauchy_real_pi_leibniz (real_const hi))
                       (sumbool (Qlt hi q) (Qlt q lo))))))))).

(* §3 带不相容性引理：端点带宽度严格小于分离半径且 lo <= q 时，
   逐点夹逼与分离下界不相容，被迫得 hi < q。 *)
Theorem lw3x_band_excl : forall (q c lo hi : Q),
  QltT 0 c ->
  real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)) ->
  real_lt (real_const lo) cauchy_real_pi_leibniz ->
  real_lt cauchy_real_pi_leibniz (real_const hi) ->
  QltT' (hi - lo) c ->
  Qle lo q ->
  Qlt hi q.
Proof.
  intros q c lo hi Hc Hsep Hlo Hhi Hw Hqlo.
  apply (QltT'_to_Qlt (hi - lo) c) in Hw.
  apply QltT_to_Qlt in Hc.
  (* 包络双岸与分离槽各自的逐点模量（见证自带预算 eps1/eps2/eps0） *)
  destruct Hlo as [eps1 [Hpos1 [N1 HN1]]].
  destruct Hhi as [eps2 [Hpos2 [N2 HN2]]].
  destruct Hsep as [eps0 [Heps0 [N3 HN3]]].
  apply QltT_to_Qlt in Hpos1.
  apply QltT_to_Qlt in Hpos2.
  apply QltT_to_Qlt in Heps0.
  pose (m := Nat.max (Nat.max N1 N2) N3).
  assert (Hn1 : NatLe N1 m).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_l.
    - apply Nat.le_max_l. }
  assert (Hn2 : NatLe N2 m).
  { apply NatLe_lift. apply Nat.le_trans with (Nat.max N1 N2).
    - apply Nat.le_max_r.
    - apply Nat.le_max_l. }
  assert (Hn3 : NatLe N3 m).
  { apply NatLe_lift. apply Nat.le_max_r. }
  pose proof (HN1 m Hn1) as Hp1.
  pose proof (HN2 m Hn2) as Hp2.
  pose proof (HN3 m Hn3) as Hp3.
  apply QltT_to_Qlt in Hp1.
  apply QltT_to_Qlt in Hp2.
  apply QltT_to_Qlt in Hp3.
  rewrite (lic_metric_proj cauchy_real_pi_leibniz q m) in Hp3.
  rewrite (real_const_proj c m) in Hp3.
  rewrite (real_const_proj lo m) in Hp1.
  rewrite (real_const_proj hi m) in Hp2.
  (* 逐点层：pi_m 距 lo/hi 分别在 eps1/eps2 内，分离下界 c + eps0 作用于
     |pi_m − q|；绝对值按 pi_m − q 的符号两支归约后线性收束：
     非负支与 lo <= q 迫使 c + eps0 + eps2 < hi − lo < c，矛盾；
     负支经 q > pi_m + c + eps0 > lo + c + eps1 + eps0 > hi 得 hi < q *)
  destruct (Qlt_le_dec (projT1 cauchy_real_pi_leibniz m - q)%Q 0)
    as [Hsign | Hsign].
  - assert (Hle0 : Qle (projT1 cauchy_real_pi_leibniz m - q)%Q 0)
      by (apply Qlt_le_weak; exact Hsign).
    rewrite (Qabs_neg (projT1 cauchy_real_pi_leibniz m - q)%Q Hle0) in Hp3.
    lra.
  - rewrite (Qabs_pos (projT1 cauchy_real_pi_leibniz m - q)%Q Hsign) in Hp3.
    lra.
Qed.

(* §4 主语句：q 进、排除见证包出（参数 c 前提位） *)
Theorem lw3x_calc : forall (q c : Q),
  QltT 0 c ->
  real_lt (real_const c) (real_metric cauchy_real_pi_leibniz (real_const q)) ->
  lw3x_seal q c.
Proof.
  intros q c Hc Hsep.
  destruct (pi_rational_envelope c Hc) as [lo [hi [Hlo [Hhi Hw]]]].
  exists c.
  exists Hc.
  exists Hsep.
  exists lo.
  exists hi.
  exists (lw3x_sideb q lo).
  split.
  - exact Hlo.
  - split.
    + exact Hhi.
    + destruct (lw3x_sideb q lo) eqn:Eb.
      * (* 判定位为 true：q < lo，right 支位承载 *)
        exact (right (leiblw_Qltb_inv q lo Eb)).
      * (* 判定位为 false：lo <= q，带不相容性定理用于 left 支 *)
        destruct (Qlt_le_dec q lo) as [Hlt | Hge].
        -- unfold lw3x_sideb in Eb.
           rewrite (leiblw_Qltb_true q lo Hlt) in Eb.
           discriminate.
        -- exact (left (lw3x_band_excl q c lo hi Hc Hsep Hlo Hhi Hw Hge)).
Qed.

(* §5 圆周率两表示的桥与几何表示下的分离定理 *)

(* 两表示等价桥的零前提闭式：节导出形 channel_f1 的闭实例，
   由库内等式 a3_h4_value_bridge 与 b5b_hsc_theorem b5dS_E_zero_on_unit
   装配而得。 *)
Definition lw3x_channel_f1_closed : real_eq real_pi_geom cauchy_real_pi_leibniz :=
  channel_f1 a3_h4_value_bridge (b5b_hsc_theorem b5dS_E_zero_on_unit).

(* c/2 的正性：Q 除法算术，与 PiEnvelope 中 eps/4 正性段同一证法。 *)
Lemma lw3x_c2_pos : forall c : Q, QltT 0 c -> QltT 0 (c / 2)%Q.
Proof.
  intros c Hc. apply Qlt_to_QltT. unfold Qdiv.
  apply (Qmult_lt_0_compat c (/ (2 # 1))).
  - apply QltT_to_Qlt. exact Hc.
  - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia.
Qed.

(* 分离假设的传输与装包：给定 0 < c 与几何表示 real_pi_geom 到有理点
   a/b 的点态分离，经传递定理 lw2t_sep_transport 与两表示等价桥
   lw3x_channel_f1_closed，半径减半后得 Leibniz 级数表示到 a/b 的分离，
   再由主定理 lw3x_calc 装成排除见证包。 *)
Theorem lw3x_pi_geom_seal_slot :
  forall (a b c : Q),
    QltT 0 c ->
    real_lt (real_const c) (real_metric real_pi_geom (real_const (a / b))) ->
    lw3x_seal (a / b) (c / 2)%Q.
Proof.
  intros a b c Hc Hsep.
  apply (lw3x_calc (a / b) (c / 2)%Q).
  - exact (lw3x_c2_pos c Hc).
  - exact (lw2t_sep_transport real_pi_geom cauchy_real_pi_leibniz
             (a / b) c Hc lw3x_channel_f1_closed Hsep).
Qed.

(* §6 Leibniz 端点包络的透明供给定理 *)

(* 包络供给定理：对任意正 eps，端点对 (lo, hi) = (lw3x_env_lo eps,
   lw3x_env_hi eps) 满足 lo < pi < hi 且带宽 hi - lo < eps。证明为
   pi_rational_envelope 同一装配的透明化重述：端点数据面全显式
   （Defined），供下游语句直接取用端点见证。 *)
Definition lw3x_env_supply (eps : Q) (Heps : QltT' 0 eps) :
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_lt (real_const lo) cauchy_real_pi_leibniz)
        (And (real_lt cauchy_real_pi_leibniz (real_const hi))
             (QltT' (hi - lo) eps)))).
Proof.
  assert (HepsQ : Qlt 0 eps) by (apply (QltT'_to_Qlt 0 eps Heps)).
  assert (Hc4 : Qlt 0 (eps / 4)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (4 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hc2 : Qlt 0 (eps / 2)).
  { unfold Qdiv. apply (Qmult_lt_0_compat eps (/ (2 # 1))).
    - exact HepsQ.
    - apply Qinv_lt_0_compat. unfold Qlt; simpl; lia. }
  assert (Hb : Qlt (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) (eps / 2)).
  { apply (Qle_lt_trans _ (4 * pie_mag (pie_modulus (eps / 2))) _).
    - apply pie_mult4_le. apply pie_mag_antitone. lia.
    - apply (pie_modulus_bound (eps / 2) Hc2). }
  exists (lw3x_env_lo eps).
  exists (lw3x_env_hi eps).
  unfold lw3x_env_lo, lw3x_env_hi.
  split.
  - apply (pie_real_lower_gen (pie_modulus (eps / 2)) (eps / 4)
            (4 * pie_partial (2 * pie_modulus (eps / 2) + 2) - eps / 4)).
    + exact Hc4.
    + apply qeq_le. ring.
  - split.
    + apply (pie_real_upper_gen (pie_modulus (eps / 2)) (eps / 4)
              (4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)).
      * exact Hc4.
      * apply Qle_refl.
    + apply Qlt_to_QltT'.
      replace (2 * pie_modulus (eps / 2) + 2)%nat
        with (Datatypes.S (2 * pie_modulus (eps / 2) + 1))%nat by lia.
      assert (Hgap : 4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                     - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     == 4 * pie_mag (2 * pie_modulus (eps / 2) + 1)).
      { assert (Hg := pie_gap1 (2 * pie_modulus (eps / 2) + 1)).
        assert (Hs : pie_term (2 * pie_modulus (eps / 2) + 1)
                     == - pie_mag (2 * pie_modulus (eps / 2) + 1)).
        { unfold pie_term, pie_mag, Qdiv.
          rewrite (atan_sign_odd (pie_modulus (eps / 2))). ring. }
        setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                        - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
          with (- (4 * (pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                     - pie_partial (2 * pie_modulus (eps / 2) + 1))))
          by ring.
        rewrite Hg. rewrite Hs. ring. }
      setoid_replace ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1) + eps / 4)
                      - (4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1))
                         - eps / 4))
        with ((4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
               - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
              + (eps / 4 + eps / 4)) by ring.
      setoid_replace (4 * pie_partial (2 * pie_modulus (eps / 2) + 1)
                      - 4 * pie_partial (Datatypes.S (2 * pie_modulus (eps / 2) + 1)))
        with (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)) by exact Hgap.
      setoid_replace (eps / 4 + eps / 4) with (eps / 2)
        by apply pie_q_add_halves.
      apply (proj2 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1)
                                   + eps / 2) eps)).
      setoid_replace (eps - (4 * pie_mag (2 * pie_modulus (eps / 2) + 1) + eps / 2))
        with ((eps - eps / 2) - 4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
        by ring.
      setoid_replace (eps - eps / 2) with (eps / 2)
        by (unfold Qdiv; field).
      apply (proj1 (Qlt_minus_iff (4 * pie_mag (2 * pie_modulus (eps / 2) + 1))
                                  (eps / 2))).
      exact Hb.
Defined.

Print Assumptions lw3x_sideb_spec.
Print Assumptions lw3x_band_excl.
Print Assumptions lw3x_calc.
Print Assumptions lw3x_seal.
Print Assumptions lw3x_channel_f1_closed.
Print Assumptions lw3x_c2_pos.
Print Assumptions lw3x_pi_geom_seal_slot.
Print Assumptions lw3x_env_supply.

Set Extraction Output Directory "Y:/attn/_tlw648_sbx/extract".
Separate Extraction lw3x_sideb lw3x_env_lo lw3x_env_hi lw3x_env_supply.
