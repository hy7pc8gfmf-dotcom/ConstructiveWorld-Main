(* 五字段指针｜模块：LW2TrigBridge.v。
   数学使命：圆周率的两条构造性表示——几何零点表示 real_pi_geom
   （real_mult (real_const 2) cos_pi_half，cos_pi_half 为余弦在
   (3/2, 5/3) 内的唯一零点）与 Leibniz 级数和 cauchy_real_pi_leibniz
   ——在三角函数端点值面上的互通。其一，将端点值 cos(pi) == -1 与
   sin(pi) == 0 由 real_pi_geom 表示转写为 cauchy_real_pi_leibniz
   表示（经 channel_f1 传输）；其二，给出实数层二倍角点值语句
   sin(2θ) == 2·sinθ·cosθ 与 cos(2θ) == cos²θ − sin²θ；其三，将
   直连边 cos_pi_half == 2·arctan_one_real 转写为
   2·arctan_one_real == pi_L/2 形，使 cos_pi_half、arctan_one_real
   与 pi_L 三量在单条零前提语句中互连。
   依赖：S01_BaseRing、S02_CauchyComplete（real_eq 及其传递、对称、
   自反、零差与投影诸件）、S03_QExp 至 S09_EntropyReal、
   S10_KVQuantTrig（cauchy_real_sin/cos、rs_add_sin/cos、
   real_sin_eq_compat、real_cos_eq_compat、real_pi_geom、
   cos_pi_half）、S11_TP3B5（cauchy_real_pi_leibniz、channel_f1、
   arctan_one_real）、S12_B5RecycleSF、S14_B5BatchBlock
   （pi_triangle_direct_edge）、LW0PiTrigValues、LW0_SinPos、
   UpReqPadeTailPos。
   对标：mathlib Real.sin_two_mul 与 Real.cos_two_mul（二倍角点值形）、
   Real.arctan_one_eq_pi_div_four 与 Real.cos_pi_half 的组合事实。
   构造性：全部语句为 Set 层（real_eq : Real -> Real -> Set；And 为
   Set 层积型），语句面零 Prop 命题；零公理、零承认、零经典逻辑；
   证明由库内语句直接引用与 Q 层逐点恒等式组装，支持 Separate
   Extraction。
   编译配方：先编 LW0PiTrigValues.v 与 LW0_SinPos.v（同目录），再以
   -Q <本目录> "" -Q "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo" ""
   编 LW2TrigBridge.v。 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Opaque Qred.

(* ---- Q 层点值恒等两件（独立语句面，ring 闭合） ---- *)
Lemma lw2_q_point_double : forall w : Q, (w + w - 2 * w == 0)%Q.
Proof. intro w. ring. Qed.

Lemma lw2_q_point_double_half : forall w : Q,
  (w - (1 # 2) * (2 * w) == 0)%Q.
Proof. intro w. ring. Qed.

(* ---- 通用双倍：z + z == 2·z（Q 层逐点恒等） ---- *)
Lemma lw2_real_double : forall z : Real,
  real_eq (real_plus z z) (real_mult (real_const 2) z).
Proof.
  intro z.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_plus_proj z z n).
  rewrite (real_mult_proj (real_const 2) z n).
  rewrite (real_const_proj 2 n).
  apply lw2_q_point_double.
Qed.

(* ---- 逐点半倍恒等：z == (1/2)·(2·z)（Q 层逐点恒等） ----
   由它可把 2·z 形的语句读回 z 形（配 lw2_half_mult_eq_compat）。 *)
Lemma lw2_real_double_half : forall z : Real,
  real_eq z (real_mult (real_const (1 / 2)) (real_mult (real_const 2) z)).
Proof.
  intro z.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_mult_proj (real_const (1 / 2))
             (real_mult (real_const 2) z) n).
  rewrite (real_mult_proj (real_const 2) z n).
  rewrite (real_const_proj 2 n).
  rewrite (real_const_proj (1 / 2) n).
  apply lw2_q_point_double_half.
Qed.

(* ---- 半倍标量乘对 real_eq 的合同 ----
   eps 倍松弛：由 |x_n − y_n| < 2·eps 得 |x_n/2 − y_n/2| < eps。 *)
Lemma lw2_half_mult_eq_compat : forall x y : Real,
  real_eq x y ->
  real_eq (real_mult (real_const (1 / 2)) x)
          (real_mult (real_const (1 / 2)) y).
Proof.
  intros x y Hxy eps Heps.
  assert (Hlt : (0 < eps)%Q) by (apply QltT_to_Qlt; exact Heps).
  assert (Hc : (0 < 2)%Q) by (unfold Qlt; reflexivity).
  assert (Hm : (0 * 2 < eps * 2)%Q)
    by (apply (proj2 (Qmult_lt_r 0 eps 2 Hc)); exact Hlt).
  assert (Hmz : ((0 * 2) == 0)%Q) by ring.
  setoid_rewrite Hmz in Hm.
  assert (HmT : QltT 0 (eps * 2)%Q) by (apply Qlt_to_QltT; exact Hm).
  destruct x as [u Hu]. destruct y as [v Hv].
  unfold real_eq in Hxy.
  destruct (Hxy (eps * 2)%Q HmT) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  change (QltT (Qabs ((1 # 2) * u n - (1 # 2) * v n)) eps).
  apply Qlt_to_QltT.
  assert (Hrw : (((1 # 2) * u n - (1 # 2) * v n)
               == ((u n - v n) * (1 # 2)))%Q) by ring.
  setoid_rewrite Hrw.
  rewrite Qabs_Qmult.
  assert (Hh : (Qabs (1 # 2) == (1 # 2))%Q) by (vm_compute; reflexivity).
  rewrite Hh.
  apply (Qle_lt_trans _ (Qabs (u n - v n) * (1 # 2))%Q _).
  - apply Qle_refl.
  - assert (Hq : (Qabs (u n - v n) * (1 # 2) < (eps * 2) * (1 # 2))%Q).
    { apply (proj2 (Qmult_lt_r (Qabs (u n - v n)) (eps * 2) (1 # 2) Hc)).
      apply QltT_to_Qlt. exact HN. }
    assert (Hre : (((eps * 2) * (1 # 2)) == eps)%Q) by ring.
    setoid_rewrite Hre in Hq.
    exact Hq.
Qed.

Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S14_B5BatchBlock.
Require Import LW0PiTrigValues.
Require Import LW0_SinPos.
Import PropositionConvergenceCore.

(* ---- channel_f1 的零前提闭合实例 ----
   节导出形的两个前提由 4·theta1 == pi_L 与
   sin theta1 == cos theta1 两条库内等式供给。 *)
Lemma lw2_channel_f1_closed :
  real_eq real_pi_geom cauchy_real_pi_leibniz.
Proof.
  exact (channel_f1 a3_h4_value_bridge
           (b5b_hsc_theorem b5dS_E_zero_on_unit)).
Qed.

(* ---- 端点值一：sin(pi_L) == 0 ----
   由 sin 对 real_eq 的合同与 channel_f1（real_pi_geom == pi_L）
   传输 pi_geom_sin_pi_zero。 *)
Lemma lw2_pi_L_sin_zero :
  real_eq (cauchy_real_sin cauchy_real_pi_leibniz) real_zero.
Proof.
  apply (real_eq_trans
          (cauchy_real_sin cauchy_real_pi_leibniz)
          (cauchy_real_sin real_pi_geom)
          real_zero).
  - exact (real_eq_sym _ _
             (real_sin_eq_compat real_pi_geom cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
  - exact pi_geom_sin_pi_zero.
Qed.

(* ---- 端点值二：cos(pi_L) == -1 ----
   由 cos 对 real_eq 的合同与 channel_f1 传输
   pi_geom_cos_pi_neg_one。 *)
Lemma lw2_pi_L_cos_neg_one :
  real_eq (cauchy_real_cos cauchy_real_pi_leibniz) (real_const (-1)%Q).
Proof.
  apply (real_eq_trans
          (cauchy_real_cos cauchy_real_pi_leibniz)
          (cauchy_real_cos real_pi_geom)
          (real_const (-1)%Q)).
  - exact (real_eq_sym _ _
             (real_cos_eq_compat real_pi_geom cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
  - exact pi_geom_cos_pi_neg_one.
Qed.

(* ---- 直连边的 pi_L 读法：2·arctan_one_real == pi_L/2 ----
   链：2·arctan_one_real == cos_pi_half（pi_triangle_direct_edge 的
   对称）== (2·cos_pi_half)·(1/2)（逐点恒等）== pi_L·(1/2)
   （半倍合同配 channel_f1，其中 2·cos_pi_half 即 real_pi_geom 的
   定义体）。 *)
Lemma lw2_theta_double_eq_pi_L :
  real_eq (real_mult (real_const 2) arctan_one_real)
          (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz).
Proof.
  apply (real_eq_trans
          (real_mult (real_const 2) arctan_one_real)
          cos_pi_half
          (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)).
  - exact (real_eq_sym cos_pi_half
             (real_mult (real_const 2) arctan_one_real)
             pi_triangle_direct_edge).
  - exact (real_eq_trans
             cos_pi_half
             (real_mult (real_const (1 / 2))
                (real_mult (real_const 2) cos_pi_half))
             (real_mult (real_const (1 / 2)) cauchy_real_pi_leibniz)
             (lw2_real_double_half cos_pi_half)
             (lw2_half_mult_eq_compat
                (real_mult (real_const 2) cos_pi_half)
                cauchy_real_pi_leibniz
                lw2_channel_f1_closed)).
Qed.

(* ---- 二倍角（sin 侧）：sin(2θ) == 2·sinθ·cosθ ----
   rs_add_sin 取 X = Y 得 sin(θ+θ) == sinθ·cosθ + cosθ·sinθ，
   次项经 real_mult_comm 换序后以通用双倍恒等收拢。 *)
Lemma lw2_sin_double_eq_two_sin_cos : forall X : Real,
  real_eq (cauchy_real_sin (real_plus X X))
          (real_mult (real_const 2)
                     (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
Proof.
  intro X.
  apply (real_eq_trans
          (cauchy_real_sin (real_plus X X))
          (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                     (real_mult (cauchy_real_cos X) (cauchy_real_sin X)))
          (real_mult (real_const 2)
                     (real_mult (cauchy_real_sin X) (cauchy_real_cos X)))).
  - exact (rs_add_sin X X).
  - apply (real_eq_trans
            (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                       (real_mult (cauchy_real_cos X) (cauchy_real_sin X)))
            (real_plus (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
                       (real_mult (cauchy_real_sin X) (cauchy_real_cos X)))
            (real_mult (real_const 2)
                       (real_mult (cauchy_real_sin X)
                                  (cauchy_real_cos X)))).
    + apply (lw0_sin_plus_eq_compat
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))
               (real_mult (cauchy_real_cos X) (cauchy_real_sin X))
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
      * apply real_eq_refl.
      * apply real_mult_comm.
    + exact (lw2_real_double
               (real_mult (cauchy_real_sin X) (cauchy_real_cos X))).
Qed.

(* ---- 二倍角（cos 侧）：cos(2θ) == cos²θ − sin²θ ----
   rs_add_cos 取 X = Y 的直接实例。 *)
Lemma lw2_cos_double_eq_cos_sq_minus_sin_sq : forall X : Real,
  real_eq (cauchy_real_cos (real_plus X X))
          (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                     (real_opp (real_mult (cauchy_real_sin X)
                                          (cauchy_real_sin X)))).
Proof.
  intro X.
  exact (rs_add_cos X X).
Qed.

(* ---- pi_L 端点值面证书：sin(pi_L) == 0 与 cos(pi_L) == -1 的
   Set 层积型封装 ---- *)
Lemma lw2_pi_L_trig_values :
  And (real_eq (cauchy_real_sin cauchy_real_pi_leibniz) real_zero)
      (real_eq (cauchy_real_cos cauchy_real_pi_leibniz)
               (real_const (-1)%Q)).
Proof.
  exact (lw2_pi_L_sin_zero, lw2_pi_L_cos_neg_one).
Qed.
