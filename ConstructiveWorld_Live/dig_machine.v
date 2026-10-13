(* ===================================================================== *)
(*  dig_machine.v —— 双积分组机（ζ(2)/μ(π) 双线共用前置机件）               *)
(*  模块名：dig_machine。                                                  *)
(*  使命：Beukers 型二重积分 ∫∫(x(1−x)y(1−y))ⁿ/(1−xy)ⁿ⁺¹ 的构造性可提取化     *)
(*        组机——① sup 证书面 dig_sup：676·N ≤ 61·(1−xy)（换元 u=1−x,        *)
(*        v=1−y 后 m=u+v, k=uv 化 G = 61m − k(737−676m+676k)，由 k ≤ m²/4   *)
(*        与 B* = (676/4)(m−2)²+61 ≥ 61 放缩至 (m/16)·H(m)，                *)
(*        H = 976−2948m+2704m²−676m³ 分档收束（m ≤ 4/5 档二次正定型；        *)
(*        m ≥ 4/5 档内括号 ≥ 1352/5）；② 复合面 dig_pointwise_decay：        *)
(*        4·(676/61)ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（基档取 dmw2_N4_le_dsq 后乘 sup）；   *)
(*        ③ 载体族界 dig_carrier_decay：F_{m+1,M} ≤ (1/4)·(61/676)^m        *)
(*        （取 zb2 截断族接口）；竞争判定 dig_comp_verdict：                 *)
(*        (9/4)·(549/676)^m < 1 于 m ≥ 4（1/11 档为 m ≥ 5，双侧锐度锚在卷）； *)
(*        条件分离 dig_sep_small：d ≤ 3^{m+1}·族界 ⟹ d²·Isum < 1。          *)
(*  衰减率档 θ = 61/676 ≈ 0.0902367 较 1/11 ≈ 0.0909091 更锐，向核真最优     *)
(*        ((√5−1)/2)⁵ ≈ 0.0901699 推进（61·11=671<676、15127²>6760²·5        *)
(*        两整数判别精确在卷）；量化距离注记（勘形级如实申报）：族界供下游    *)
(*        测度档推算，μ(π) 线＝「分母增长 < 衰减率」竞争判定面的可实例化      *)
(*        形态；Rhin–Viola 组结构置换群法本体非本件范围；禁「首例/更强于」。  *)
(*  依赖：Stdlib QArith/ZArith/Arith/Lia/Setoid；S01_BaseRing、              *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists、abl_z2_truncfam、      *)
(*        abl_z2_itg_carrier、abl_dmw2_pointwise_sharp、                     *)
(*        abl_dmw2_sharpen_decay。                                         *)
(*  对标：Beukers, Bull. London Math. Soc. 11 (1979)；abl_dmw2_pointwise_   *)
(*        sharp（11 档）的参数化推广；Hanson 1972（lcm ≤ 3ⁿ）竞争步照用。     *)
(*  构造性注记：全语句 Set 承载；Print Assumptions 全谱 Closed；             *)
(*        Separate Extraction Obj.magic=0；零实数层、零经典逻辑。            *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" dig_machine.v           *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier.
Require Import abl_dmw2_pointwise_sharp abl_dmw2_sharpen_decay.

Open Scope Q_scope.

(* ============================================================ *)
(* §0 机件参数槽：锐化逐点常数 θ := 61/676 与机件权重                             *)
(* ============================================================ *)

(* 机件唯一参数位：逐点常数 θ。61/676 为核真最优 θ* = φ⁻⁵ ≈ 0.0901699 的   *)
(* 上方有理逼近（比 B2 整值档 1/11 更锐），精确判别：                        *)
(*   61/676 < 1/11 ⟺ 61·11 = 671 < 676；                                    *)
(*   θ* < 61/676  ⟺  (5√5−11)/2 < 61/676 ⟺ 15127² > 6760²·5。              *)
Definition dig_theta : Q := (61#676).

(* 机件权重输出：族界面 (1/4)·θ^m（供下游测度档推算） *)
Definition dig_weight (m : nat) : Q := (1#4) * q_pow dig_theta m.

Lemma dig_theta_ge0 : 0 <= dig_theta.
Proof. unfold dig_theta. unfold Qle. simpl. lia. Qed.

Lemma dig_theta_le_one : dig_theta <= 1.
Proof. unfold dig_theta. unfold Qle. simpl. lia. Qed.

Lemma dig_weight_ge0 : forall m : nat, QleT' 0 (dig_weight m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply q_pow_nonneg. exact dig_theta_ge0.
Qed.

(* 参数槽锐度锚：新权重 (1/4)(61/676) ≤ 旧权重 (1/4)(1/11)（1/11 档同位）
   （Qle_bool 可计算判定·θ 层锐化记录） *)
Lemma dig_weight_sharpen :
  QleT' ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qle_bool ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1))).
Qed.

(* ============================================================ *)
(* §A sup 证书面（主定理·新数学）：676·N ≤ 61·(1−xy)，即 N/(1−xy) ≤ 61/676     *)
(* ============================================================ *)

(* sup 证书（换元形）：0≤u,v≤1 ⟹ 676·u(1−u)v(1−v) ≤ 61·(u+v−uv)。 *)
Lemma dig_sup_uv : forall u v : Q,
  0 <= u <= 1 -> 0 <= v <= 1 ->
  676 * u * (1 - u) * v * (1 - v) <= 61 * (u + v - u * v).
Proof.
  intros u v [Hu1 Hu2] [Hv1 Hv2].
  assert (Hk0 : 0 <= u * v) by (apply dmw2_mult2_ge0; assumption).
  assert (Hm0 : 0 <= u + v).
  { apply (Qle_trans 0 (0 + 0) (u + v)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 u 0 v); assumption. }
  assert (Hm2 : (u + v) <= 2).
  { apply (Qle_trans (u + v) (1 + 1) 2).
    - apply (Qplus_le_compat u 1 v 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (H4k : 0 <= (u+v)*(u+v) - 4*(u*v)).
  { assert (Heq : (u+v)*(u+v) - 4*(u*v) == (u-v)*(u-v)) by ring.
    rewrite Heq. apply dmw2_sq_ge0. }
  (* 由 H4k 线性导出：676k ≤ (676/4)m² 与 k ≤ m²/4 *)
  assert (HBB : 676 * (u*v) <= (676#4)*(u+v)*(u+v)).
  { apply (Qle_trans (676 * (u*v))
      (676 * (u*v) + (676#4) * ((u+v)*(u+v) - 4*(u*v)))
      ((676#4)*(u+v)*(u+v))).
    - apply dmw2_add_ge0_le.
      apply (dmw2_mult2_ge0 (676#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (dmw2_qmake_pos 676 4); lia | exact H4k ].
    - assert (Heq : 676 * (u*v) + (676#4) * ((u+v)*(u+v) - 4*(u*v))
                 == (676#4)*(u+v)*(u+v)) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk_le : u * v <= ((u+v)*(u+v)) * (1#4)).
  { apply (Qle_trans (u * v)
      (u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4))
      (((u+v)*(u+v)) * (1#4))).
    - apply dmw2_add_ge0_le.
      assert (Heqc : ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                  == (1#4) * ((u+v)*(u+v) - 4*(u*v))) by ring.
      rewrite Heqc.
      apply (dmw2_mult2_ge0 (1#4) ((u+v)*(u+v) - 4*(u*v)))
      ; [ apply (dmw2_qmake_pos 1 4); lia | exact H4k ].
    - assert (Heq : u * v + ((u+v)*(u+v) - 4*(u*v)) * (1#4)
                 == ((u+v)*(u+v)) * (1#4)) by ring.
      rewrite Heq. apply Qle_refl. }
  (* 因子界：B* = 737−676m+(676/4)m² = (676/4)(m−2)²+61 ≥ 61 > 0 *)
  assert (HBp : 0 <= 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)).
  { assert (Hid0 : 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)
                == (676#4)*((2-(u+v))*(2-(u+v))) + 61) by ring.
    rewrite Hid0.
    assert (Hs : 0 <= (2-(u+v))*(2-(u+v))) by apply dmw2_sq_ge0.
    assert (HX : 0 <= (676#4)*((2-(u+v))*(2-(u+v)))).
    { apply (dmw2_mult2_ge0 (676#4) ((2-(u+v))*(2-(u+v))))
      ; [ apply (dmw2_qmake_pos 676 4); lia | exact Hs ]. }
    apply (Qle_trans 0 ((676#4)*((2-(u+v))*(2-(u+v))))
                      ((676#4)*((2-(u+v))*(2-(u+v))) + 61)).
    - exact HX.
    - apply dmw2_add_ge0_le. apply (dmw2_qmake_pos 61 1); lia. }
  assert (HBs : 737 - 676*(u+v) + 676*(u*v)
             <= 737 - 676*(u+v) + (676#4)*(u+v)*(u+v)).
  { apply (Qplus_le_compat (737 - 676*(u+v)) (737 - 676*(u+v))
             (676*(u*v)) ((676#4)*(u+v)*(u+v)))
    ; [ apply Qle_refl | exact HBB ]. }
  (* 步一：k·B ≤ k·B* *)
  assert (HkBB : (u*v) * (737 - 676*(u+v) + 676*(u*v))
              <= (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (737 - 676*(u+v) + 676*(u*v))
                  (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) (u*v) HBs Hk0) as H.
    assert (Heq1 : (u*v) * (737 - 676*(u+v) + 676*(u*v))
                == (737 - 676*(u+v) + 676*(u*v)) * (u*v)) by ring.
    assert (Heq2 : (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
                == (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) * (u*v)) by ring.
    rewrite <- Heq1, <- Heq2 in H. exact H. }
  (* 步二：k·B* ≤ (m²/4)·B* *)
  assert (HkB2 : (u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
              <= (((u+v)*(u+v)) * (1#4)) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))).
  { pose proof (Qmult_le_compat_r (u*v) (((u+v)*(u+v)) * (1#4))
                  (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)) Hk_le HBp) as H.
    exact H. }
  (* 单变元末式非负（分档 m ≤ 4/5 ／ m ≥ 4/5） *)
  assert (Hlow : 0 <= ((u+v) * (1#16))
                   * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                            - 676*(u+v)*(u+v)*(u+v))).
  { destruct (Qlt_le_dec (u+v) (4#5)) as [Hm45 | Hm45].
    - (* 档一 m ≤ 4/5：z = 4/5−m，H = 256/125−(2012/25)z+(5408/5)z²+676z³ *)
      assert (Hz0 : 0 <= (4#5) - (u+v))
        by (apply (dmw2_le_sub (u+v) (4#5)); exact (Qlt_le_weak _ _ Hm45)).
      assert (HidB : 976 - 2948*(u+v) + 2704*(u+v)*(u+v) - 676*(u+v)*(u+v)*(u+v)
                  == (256#125) - (2012#25)*((4#5)-(u+v))
                     + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                     + 676*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v))))
        by ring.
      assert (Hcube0 : 0 <= (((4#5)-(u+v))*((4#5)-(u+v)))*((4#5)-(u+v))).
      { apply Qmult_le_0_compat.
        - apply dmw2_sq_ge0.
        - exact Hz0. }
      assert (Hcube : 0 <= 676*(((4#5)-(u+v))*((4#5)-(u+v))*((4#5)-(u+v)))).
      { apply (dmw2_mult2_ge0 676); [ apply (dmw2_nat_pos 676) | exact Hcube0 ]. }
      assert (Hsq : 0 <= (((4#5)-(u+v))-(503#13520))*(((4#5)-(u+v))-(503#13520)))
        by apply dmw2_sq_ge0.
      assert (Hin : 0 <= (5408#5)*(((4#5)-(u+v))-(503#13520))
                                 *(((4#5)-(u+v))-(503#13520))).
      { assert (Hasso : (5408#5)*(((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520))
                     == (5408#5)*((((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520)))) by ring.
        rewrite Hasso.
        apply (dmw2_mult2_ge0 (5408#5)
                ((((4#5)-(u+v))-(503#13520))*(((4#5)-(u+v))-(503#13520))))
        ; [ apply (dmw2_qmake_pos 5408 5); lia | exact Hsq ]. }
      assert (Hin2 : 0 <= (5408#5)*(((4#5)-(u+v))-(503#13520))
                                   *(((4#5)-(u+v))-(503#13520))
                          + (372412#676000)).
      { apply (Qle_trans 0
                 ((5408#5)*(((4#5)-(u+v))-(503#13520))
                           *(((4#5)-(u+v))-(503#13520))) _).
        - exact Hin.
        - apply (dmw2_add_ge0_le
                   ((5408#5)*(((4#5)-(u+v))-(503#13520))
                             *(((4#5)-(u+v))-(503#13520)))
                   (372412#676000)).
          apply (dmw2_qmake_pos 372412 676000); lia. }
      assert (Hquad : 0 <= (256#125) - (2012#25)*((4#5)-(u+v))
                           + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))).
      { assert (Hsos : (256#125) - (2012#25)*((4#5)-(u+v))
                           + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v)))
                    == (5408#5)*(((4#5)-(u+v))-(503#13520))
                                *(((4#5)-(u+v))-(503#13520))
                       + (372412#676000))
          by ring.
        rewrite Hsos. exact Hin2. }
      assert (HH : 0 <= 976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                        - 676*(u+v)*(u+v)*(u+v)).
      { rewrite HidB.
        apply (Qle_trans _ ((256#125) - (2012#25)*((4#5)-(u+v))
                 + (5408#5)*(((4#5)-(u+v))*((4#5)-(u+v))))).
        - exact Hquad.
        - apply dmw2_add_ge0_le. exact Hcube. }
      apply Qmult_le_0_compat.
      + apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH.
    - (* 档二 m ≥ 4/5：s = m−4/5 ∈ [0,6/5]，
         H = 256/125 + s(2012/25 + s(5408/5−676s)) ≥ 256/125 > 0 *)
      assert (Hs0 : 0 <= (u+v) - (4#5))
        by (apply (dmw2_le_sub (4#5) (u+v)); exact Hm45).
      assert (Hs2 : (u+v) - (4#5) <= (6#5)).
      { apply (dmw2_sub_ge0 ((u+v)-(4#5)) (6#5)).
        assert (Heq : (6#5) - ((u+v)-(4#5)) == 2 - (u+v)) by ring.
        rewrite Heq. apply (dmw2_le_sub (u+v) 2). exact Hm2. }
      (* 5408/5 − 676s ≥ 5408/5 − 676·(6/5) = 1352/5 > 0 *)
      assert (Hb1 : (5408#5) - 676*(6#5) == (1352#5)) by ring.
      assert (Hb2 : 676*((u+v)-(4#5)) <= 676*(6#5)).
      { pose proof (Qmult_le_compat_r ((u+v)-(4#5)) (6#5) 676 Hs2
                      (dmw2_nat_pos 676)) as H.
        assert (Hc : 676*((u+v)-(4#5)) == ((u+v)-(4#5)) * 676) by ring.
        assert (Hc2 : 676*(6#5) == (6#5) * 676) by ring.
        rewrite Hc, Hc2. exact H. }
      assert (Hbr : 0 <= (5408#5) - 676*((u+v)-(4#5))).
      { assert (Hb3 : (5408#5) - 676*(6#5) <= (5408#5) - 676*((u+v)-(4#5)))
          by (apply (dmw2_minus_le (5408#5) (676*((u+v)-(4#5))) (676*(6#5)))
            ; exact Hb2).
        apply (Qle_trans 0 ((5408#5) - 676*(6#5))).
        - rewrite Hb1. apply (dmw2_qmake_pos 1352 5); lia.
        - exact Hb3. }
      assert (Hbrk : 0 <= (2012#25)
                          + ((u+v)-(4#5))*((5408#5) - 676*((u+v)-(4#5)))).
      { apply (Qle_trans 0 (2012#25) _).
        - apply (dmw2_qmake_pos 2012 25); lia.
        - apply dmw2_add_ge0_le.
          apply (dmw2_mult2_ge0 ((u+v)-(4#5)) ((5408#5) - 676*((u+v)-(4#5))))
          ; [ exact Hs0 | exact Hbr ]. }
      assert (HidA : 976 - 2948*(u+v) + 2704*(u+v)*(u+v) - 676*(u+v)*(u+v)*(u+v)
                  == (256#125) + ((u+v)-(4#5))
                       *((2012#25) + ((u+v)-(4#5))
                                      *((5408#5) - 676*((u+v)-(4#5)))))
        by ring.
      assert (Hterm : 0 <= ((u+v)-(4#5))
                       *((2012#25) + ((u+v)-(4#5))
                                      *((5408#5) - 676*((u+v)-(4#5))))).
      { apply (dmw2_mult2_ge0 ((u+v)-(4#5)))
        ; [ exact Hs0 | exact Hbrk ]. }
      assert (HH : 0 <= 976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                        - 676*(u+v)*(u+v)*(u+v)).
      { rewrite HidA.
        apply (Qle_trans 0 (256#125) _).
        - apply (dmw2_qmake_pos 256 125); lia.
        - apply dmw2_add_ge0_le. exact Hterm. }
      apply Qmult_le_0_compat.
      + apply (dmw2_mult2_ge0 (u+v) (1#16))
        ; [ exact Hm0 | apply (dmw2_qmake_pos 1 16); lia ].
      + exact HH. }
  (* 链式合成：0 ≤ (m/16)H = 61m−(m²/4)B* ≤ 61m−k·B* ≤ 61m−k·B = G *)
  assert (Hid2 : 61*(u+v) - (((u+v)*(u+v)) * (1#4))
                       * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))
              == ((u+v) * (1#16))
                   * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                            - 676*(u+v)*(u+v)*(u+v)))
    by ring.
  assert (HG : 0 <= 61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)).
  { assert (HeqG : 61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)
                == 61*(u+v) - (u*v)*(737 - 676*(u+v) + 676*(u*v))) by ring.
    rewrite HeqG.
    apply (Qle_trans _ (((u+v) * (1#16))
              * (976 - 2948*(u+v) + 2704*(u+v)*(u+v)
                       - 676*(u+v)*(u+v)*(u+v)))).
    - exact Hlow.
    - rewrite <- Hid2.
      apply (Qle_trans _ (61*(u+v) - (u*v)*(737 - 676*(u+v) + (676#4)*(u+v)*(u+v)))).
      + apply (dmw2_minus_le (61*(u+v))
          ((u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v)))
          ((((u+v)*(u+v)) * (1#4)) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))))
        ; exact HkB2.
      + apply (dmw2_minus_le (61*(u+v))
          ((u*v) * (737 - 676*(u+v) + 676*(u*v)))
          ((u*v) * (737 - 676*(u+v) + (676#4)*(u+v)*(u+v))))
        ; exact HkBB. }
  (* 终步：61(u+v−uv) = 676N + G ≥ 676N *)
  apply (Qle_trans (676*u*(1-u)*v*(1-v))
    (676*u*(1-u)*v*(1-v) + (61*(u + v - u*v) - 676*u*(1-u)*v*(1-v)))
    (61*(u + v - u*v))).
  - apply dmw2_add_ge0_le. exact HG.
  - assert (HeqF : 676*u*(1-u)*v*(1-v)
                 + (61*(u + v - u*v) - 676*u*(1-u)*v*(1-v))
                == 61*(u + v - u*v)) by ring.
    rewrite HeqF. apply Qle_refl.
Qed.

(* sup 证书（原变元形）：0≤x,y≤1 ⟹ 676·x(1−x)y(1−y) ≤ 61·(1−xy)
   （u=1−x, v=1−y 换算） *)
Lemma dig_sup : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  676 * x * (1 - x) * y * (1 - y) <= 61 * (1 - x * y).
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hu1 : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hu2 : (1 - x) <= 1) by (apply (dmw2_minus_ge0 x 1); exact Hx1).
  assert (Hv1 : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hv2 : (1 - y) <= 1) by (apply (dmw2_minus_ge0 y 1); exact Hy1).
  pose proof (dig_sup_uv (1 - x) (1 - y) (conj Hu1 Hu2) (conj Hv1 Hv2)) as H.
  assert (HeqL : 676 * x * (1 - x) * y * (1 - y)
              == 676 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
    by ring.
  assert (HeqR : (1 - x) + (1 - y) - (1 - x) * (1 - y) == 1 - x * y) by ring.
  rewrite HeqR in H.
  apply (Qle_trans (676 * x * (1 - x) * y * (1 - y))
                   (676 * (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y)))
                   (61 * (1 - x * y))).
  - apply (dmw2_le_eq _ _ HeqL).
  - exact H.
Qed.

(* 金点邻域数值锚：u=v=38/100 档 61T−676N = 22363/781250 > 0
   （真 sup 点 u=v=((√5−1)/2)²≈0.382 的有理邻域·裕量层机器可查记录） *)
Lemma dig_anchor_gold :
  QltT 0 (61 * ((38#100) + (38#100) - (38#100)*(38#100))
      - 676 * ((38#100)*(1 - (38#100))*(38#100)*(1 - (38#100)))).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qlt_bool 0 (61 * ((38#100) + (38#100) - (38#100)*(38#100))
      - 676 * ((38#100)*(1 - (38#100))*(38#100)*(1 - (38#100)))))).
Qed.

(* 半点档 sup 锚：676/16 ≤ 183/4（x=y=1/2 处直接可计算判定） *)
Lemma dig_anchor_sup_half :
  QleT' (676 * (1#2)*(1 - (1#2))*(1#2)*(1 - (1#2)))
        (61 * ((1#2) + (1#2) - (1#2)*(1#2))).
Proof.
  exact (id_refl (A:=bool)
    (x:=Qle_bool (676 * (1#2)*(1 - (1#2))*(1#2)*(1 - (1#2)))
                 (61 * ((1#2) + (1#2) - (1#2)*(1#2))))).
Qed.

(* ============================================================ *)
(* §B 复合面：4·(676/61)ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²（除法自由形·Set 面）                *)
(*    （基档取 dmw2_N4_le_dsq：4N ≤ (1−xy)² 常数无关层直接复用；          *)
(*      步档乘 sup 证书槽 dig_sup 的 (676/61)·N ≤ 1−xy）                       *)
(* ============================================================ *)

Theorem dig_pointwise_decay : forall (n : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n)
  <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)).
Proof.
  induction n as [| n IH]; intros x y [Hx1 Hx2] [Hy1 Hy2].
  - assert (Heq1 : 4 * q_pow (676#61) 0 * q_pow (x*(1-x)*y*(1-y)) 1
                == 4 * x * (1-x) * y * (1-y)) by (cbn [q_pow]; ring).
    assert (Heq2 : q_pow (1 - x*y) 2 == (1 - x*y)*(1 - x*y))
      by (cbn [q_pow]; ring).
    rewrite Heq1, Heq2.
    apply dmw2_N4_le_dsq; [ split; assumption | split; assumption ].
  - pose proof (IH x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as HIH.
    pose proof (dig_sup x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hsup.
    (* 倒数槽换算：(676/61)·N ≤ 1−xy（由 676N ≤ 61T 乘 1/61） *)
    assert (Hz61 : 0 <= (1#61)) by (unfold Qle; simpl; lia).
    pose proof (Qmult_le_compat_r (676 * x*(1-x)*y*(1-y)) (61 * (1 - x*y))
                                  (1#61) Hsup Hz61) as Hmul.
    assert (Hth : (676#61) * x*(1-x)*y*(1-y) <= 1 - x*y).
    { assert (E1 : (676#61) * x*(1-x)*y*(1-y)
                == 676 * x*(1-x)*y*(1-y) * (1#61)) by ring.
      assert (E2 : 61 * (1 - x*y) * (1#61) == 1 - x*y) by ring.
      apply (Qle_trans _ (676 * x*(1-x)*y*(1-y) * (1#61))).
      - apply (dmw2_le_eq _ _ E1).
      - apply (Qle_trans _ (61 * (1 - x*y) * (1#61))).
        + exact Hmul.
        + apply (dmw2_le_eq _ _ E2). }
    (* 非负性面 *)
    assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
    assert (Hxyb : 0 <= 1 - x*y)
      by (apply (dmw2_le_sub (x*y) 1); apply (dmw2_xy_le_1 x y); assumption).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y))
      by (apply (dmw2_mult4_ge0 x (1-x) y (1-y))
        ; [ exact Hx1 | exact Hxb | exact Hy1 | exact Hyb ]).
    assert (HL0 : 0 <= (676#61) * x*(1-x)*y*(1-y)).
    { apply (dmw2_mult2_ge0 ((676#61) * x * (1-x) * y) (1-y)).
      - apply (dmw2_mult2_ge0 ((676#61) * x * (1-x)) y).
        + apply (dmw2_mult2_ge0 ((676#61) * x) (1-x)).
          * apply (dmw2_mult2_ge0 (676#61) x).
            -- unfold Qle. simpl. lia.
            -- exact Hx1.
          * exact Hxb.
        + exact Hy1.
      - exact Hyb. }
    assert (HTn : 0 <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
      by (apply q_pow_nonneg; exact Hxyb).
    (* 步一：LHS_n·(676/61)N ≤ RHS_n·(676/61)N *)
    assert (S1 : (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))
              <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))).
    { apply (Qmult_le_compat_r
               (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
               (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
               ((676#61) * x*(1-x)*y*(1-y)) HIH HL0). }
    (* 步二：≤ RHS_n·(1−xy) *)
    assert (S2 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                   * ((676#61) * x*(1-x)*y*(1-y))
              <= q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y)).
    { pose proof (Qmult_le_compat_r ((676#61) * x*(1-x)*y*(1-y)) (1 - x*y)
                 (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))) Hth HTn) as H.
      assert (Hc1 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                      * ((676#61) * x*(1-x)*y*(1-y))
                  == ((676#61) * x*(1-x)*y*(1-y))
                       * q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))) by ring.
      assert (Hc2 : q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y)
                  == (1 - x*y) * q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)))
        by ring.
      rewrite Hc1, Hc2. exact H. }
    (* 合成与幂重写 *)
    assert (Eg1 : 4 * q_pow (676#61) (Datatypes.S n) * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S (Datatypes.S n))
               == (4 * q_pow (676#61) n * q_pow (x*(1-x)*y*(1-y)) (Datatypes.S n))
                  * ((676#61) * x*(1-x)*y*(1-y)))
      by (cbn [q_pow]; ring).
    rewrite Eg1.
    apply (Qle_trans _ (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                          * ((676#61) * x*(1-x)*y*(1-y)))).
    + exact S1.
    + apply (Qle_trans _ (q_pow (1 - x*y) (Datatypes.S (Datatypes.S n))
                            * (1 - x*y))).
      * exact S2.
      * assert (Hsq : q_pow (1 - x*y) (Datatypes.S (Datatypes.S (Datatypes.S n)))
                   == q_pow (1 - x*y) (Datatypes.S (Datatypes.S n)) * (1 - x*y))
          by (rewrite (q_pow_succ (1 - x*y)
                (Datatypes.S (Datatypes.S n))); ring).
        rewrite Hsq. apply Qle_refl.
Qed.

(* 数值锚：n=1、x=y=1/2 档复合左端 4·(676/61)·N² = 169/976 机器可查 *)
Lemma dig_anchor_decay_n1 :
  4 * q_pow (676#61) 1
    * q_pow ((1#2)*(1-(1#2))*(1#2)*(1-(1#2))) 2 == (169#976).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §C 机件装配面：载体族界＋竞争判定＋条件分离                                     *)
(* ============================================================ *)

(* 载体族界：0≤x,y≤1 ⟹ F_{m+1,M}(x,y) ≤ (1/4)·(61/676)^m
   （dmw2_dc_carrier_decay 的 61/676 档参数化重铸） *)
Theorem dig_carrier_decay : forall (m M : nat) (x y : Q),
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y) (dig_weight m).
Proof.
  intros m M x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hxb : 0 <= 1 - x) by (apply (dmw2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (dmw2_le_sub y 1); exact Hy2).
  assert (Hxy0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hxy1 : x * y <= 1) by (apply (dmw2_xy_le_1 x y); assumption).
  pose proof (zb2_ps_bound (Datatypes.S m) M (x * y) (conj Hxy0 Hxy1)) as HpsT.
  pose proof (QleT'_to_Qle _ _ HpsT) as Hps.
  pose proof (zb2_beval_segl (Datatypes.S m) M x y) as Hseg.
  assert (Hmerge : q_pow (x * (1 - x)) (Datatypes.S m) * q_pow (y * (1 - y)) (Datatypes.S m)
                == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { rewrite <- (zb2_q_pow_mul (x * (1 - x)) (y * (1 - y)) (Datatypes.S m)).
    apply q_pow_wd. ring. }
  rewrite Hmerge in Hseg.
  assert (HN0 : 0 <= x * (1 - x) * y * (1 - y))
    by (apply (dmw2_mult4_ge0 x (1 - x) y (1 - y)); assumption).
  assert (HK0 : 0 <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
    by (apply q_pow_nonneg; exact HN0).
  (* (A)：T^(m+2)·F ≤ N^(m+1) *)
  assert (HA : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
            <= q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)).
  { assert (Hrw : q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
               == (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_ps (Datatypes.S m) M (x * y))
                  * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
      by (rewrite Hseg; ring).
    rewrite Hrw.
    apply (Qle_trans _ (1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_ps (Datatypes.S m) M (x * y))
                               1 (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               Hps HK0).
    - assert (H1K : 1 * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                 == q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)) by ring.
      rewrite H1K. apply Qle_refl. }
  (* (B)：4·(676/61)^m·N^(m+1) ≤ T^(m+2)（机件复合面） *)
  pose proof (dig_pointwise_decay m x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as Hdec0.
  assert (HKt : 0 <= 4 * q_pow (676#61) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  (* 组合：(A) 右乘 4·(676/61)^m 后与 (B) 串接 *)
  assert (HC : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
               * (4 * q_pow (676#61) m)
            <= q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))).
  { apply (Qle_trans _ (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                           * (4 * q_pow (676#61) m))).
    - apply (Qmult_le_compat_r (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                                 * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                               (q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
                               (4 * q_pow (676#61) m) HA HKt).
    - assert (Hcomm : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m)
                        * (4 * q_pow (676#61) m)
                   == 4 * q_pow (676#61) m
                        * q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m))
        by ring.
      rewrite Hcomm. exact Hdec0. }
  (* 按 T = 1−xy 的符号分情况 *)
  destruct (Qlt_le_dec 0 (1 - x * y)) as [Hpos | Hneg].
  - (* 主情形：T > 0，正因子消去后乘权重 *)
    pose proof (QltT_to_Qlt _ _
      (dmw2_dc_qp_pos (Datatypes.S (Datatypes.S m)) (1 - x * y) Hpos)) as HPpos.
    assert (Hrg : (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))
                    * zb2_beval_l (zb2_segl (Datatypes.S m) M) x y)
                  * (4 * q_pow (676#61) m)
               == (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  * q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) by ring.
    rewrite Hrg in HC.
    pose proof (dmw2_dc_cancel_one
                  (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  (q_pow (1 - x * y) (Datatypes.S (Datatypes.S m))) HPpos HC) as H1.
    pose proof (QleT'_to_Qle _ _ (dig_weight_ge0 m)) as HW0.
    pose proof (Qmult_le_compat_r
                  (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                    * (4 * q_pow (676#61) m))
                  1 (dig_weight m) H1 HW0) as Hmult.
    assert (Hunit : (4 * q_pow (676#61) m) * dig_weight m == 1).
    { unfold dig_weight.
      assert (Hpm : q_pow (676#61) m * q_pow (61#676) m == 1).
      { rewrite <- (zb2_q_pow_mul (676#61) (61#676) m).
        assert (H676 : (676#61) * (61#676) == 1) by ring.
        rewrite H676. apply dmw2_dc_qp_one. }
      assert (Hre : (4 * q_pow (676#61) m) * ((1#4) * q_pow (61#676) m)
                 == (4 * (1#4)) * (q_pow (676#61) m * q_pow (61#676) m)) by ring.
      rewrite Hre, Hpm. ring. }
    assert (Hlhs : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * (4 * q_pow (676#61) m))
                   * dig_weight m
                == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y).
    { assert (Hre2 : (zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                       * (4 * q_pow (676#61) m))
                      * dig_weight m
                  == zb2_beval_l (zb2_segl (Datatypes.S m) M) x y
                     * ((4 * q_pow (676#61) m) * dig_weight m)) by ring.
      rewrite Hre2, Hunit. ring. }
    assert (Hrhs : 1 * dig_weight m == dig_weight m) by ring.
    rewrite Hrhs in Hmult. rewrite Hlhs in Hmult.
    apply Qle_to_QleT'. exact Hmult.
  - (* 边界情形：T ≤ 0 与 xy ≤ 1 联立得 T = 0，进而 x = y = 1、F = 0 *)
    assert (HT0 : 0 <= 1 - x * y) by (apply (dmw2_le_sub (x * y) 1); exact Hxy1).
    assert (HTeq : 1 - x * y == 0) by (apply Qle_antisym; [ exact Hneg | exact HT0 ]).
    assert (Hxyeq : x * y == 1).
    { assert (Ha : 1 - (1 - x * y) == 1 - 0) by (rewrite HTeq; ring).
      assert (Hb : 1 - (1 - x * y) == x * y) by ring.
      assert (Hc : 1 - 0 == 1) by ring.
      rewrite Hb, Hc in Ha. exact Ha. }
    assert (Hle1 : x * y <= x).
    { pose proof (Qmult_le_compat_r y 1 x Hy2 Hx1) as Hq.
      assert (Hd1 : y * x == x * y) by ring. assert (Hd2 : 1 * x == x) by ring.
      rewrite Hd1, Hd2 in Hq. exact Hq. }
    assert (Hle2 : x * y <= y).
    { pose proof (Qmult_le_compat_r x 1 y Hx2 Hy1) as Hq.
      assert (Hd2 : 1 * y == y) by ring. rewrite Hd2 in Hq. exact Hq. }
    assert (Hx1e : x == 1).
    { apply Qle_antisym.
      - exact Hx2.
      - apply (Qle_trans 1 (x * y) x).
        + apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle1. }
    assert (Hy1e : y == 1).
    { apply Qle_antisym.
      - exact Hy2.
      - apply (Qle_trans 1 (x * y) y).
        + apply (dmw2_le_eq 1 (x * y)). symmetry. exact Hxyeq.
        + exact Hle2. }
    assert (HN0e : x * (1 - x) * y * (1 - y) == 0) by (rewrite Hx1e, Hy1e; ring).
    assert (Hq0 : q_pow (x * (1 - x) * y * (1 - y)) (Datatypes.S m) == 0)
      by (rewrite HN0e; cbn [q_pow]; apply Qmult_0_l).
    assert (Hc0 : zb2_beval_l (zb2_segl (Datatypes.S m) M) x y == 0)
      by (rewrite Hseg, Hq0; apply Qmult_0_l).
    apply Qle_to_QleT'. rewrite Hc0.
    apply QleT'_to_Qle. apply dig_weight_ge0.
Qed.

(* 竞争恒等式：9^(m+1)·(1/4)·(61/676)^m = (9/4)·(549/676)^m *)
Lemma dig_comp_id : forall m : nat,
  q_pow 9 (Datatypes.S m) * dig_weight m == (9#4) * q_pow (549#676) m.
Proof.
  intro m. unfold dig_weight.
  assert (Hpm : q_pow 9 m * q_pow (61#676) m == q_pow (549#676) m).
  { rewrite <- (zb2_q_pow_mul 9 (61#676) m).
    assert (H911 : 9 * (61#676) == (549#676)) by ring.
    rewrite H911. reflexivity. }
  assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (61#676) m)
             == (9 * (1#4)) * (q_pow 9 m * q_pow (61#676) m))
    by (rewrite (q_pow_succ 9 m); ring).
  rewrite Hre, Hpm.
  assert (H94 : 9 * (1#4) == (9#4)) by ring.
  rewrite H94. reflexivity.
Qed.

(* 竞争基档：(9/4)·(549/676)^4 = 817583065209/835308258304 < 1（字面判定） *)
Lemma dig_comp_base : QltT ((9#4) * q_pow (549#676) 4) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (549#676) 4) 1)).
Qed.

(* 基档字面值锚：vm_compute 复算（与 §4 精确值一致） *)
Lemma dig_comp_base_val :
  (9#4) * q_pow (549#676) 4 == (817583065209#835308258304).
Proof. vm_compute. reflexivity. Qed.

(* 阈值锐度锚（新档）：(9/4)·(549/676)^3 = 1489222341/1235663104 ≥ 1
   ——m=3 不足，判定阈值 m ≥ 4 为锐阈值（Qle_bool 可计算判定） *)
Lemma dig_comp_base3_ge : QleT' 1 ((9#4) * q_pow (549#676) 3).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (549#676) 3))).
Qed.

(* 竞争步进：(9/4)·(549/676)^(m+1) ≤ (9/4)·(549/676)^m（两侧乘 549/676 ≤ 1） *)
Lemma dig_comp_step : forall m : nat,
  QleT' ((9#4) * q_pow (549#676) (Datatypes.S m)) ((9#4) * q_pow (549#676) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (549#676) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  assert (Hs676 : (549#676) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (549#676) (Datatypes.S m)
             == (549#676) * ((9#4) * q_pow (549#676) m))
    by (rewrite (q_pow_succ (549#676) m); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (549#676) 1 ((9#4) * q_pow (549#676) m)
                Hs676 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (549#676) m) == (9#4) * q_pow (549#676) m)
    by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* 竞争平移：(9/4)·(549/676)^(m+d) ≤ (9/4)·(549/676)^m（对平移量 d 归纳） *)
Lemma dig_comp_drop : forall (d m : nat),
  QleT' ((9#4) * q_pow (549#676) (m + d)) ((9#4) * q_pow (549#676) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat)
      by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (549#676) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (549#676) (m + d))
                       ((9#4) * q_pow (549#676) m)).
    + apply dig_comp_step.
    + apply IH.
Qed.

(* 竞争判定：m ≥ 4 ⟹ (9/4)·(549/676)^m < 1
   （le_lt_dec 可判定分情况：m > 4 时经步进回落至基档；
     m ≤ 4 时联立前提得 m+1 = 4，直接落基档） *)
Lemma dig_comp_verdict : forall m : nat, (4 <= m)%nat -> QltT ((9#4) * q_pow (549#676) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 4 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (549#676) (Datatypes.S m))
                           ((9#4) * q_pow (549#676) m) 1).
      * apply dig_comp_step.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 4)%nat) by lia.
      rewrite Heq. exact dig_comp_base.
Qed.

(* 平方权：0 ≤ d ≤ 3^n ⟹ d² ≤ 9^n（dmw2_dc_weight_sq 同构） *)
Lemma dig_weight_sq : forall (n : nat) (d : Q),
  QleT' 0 d -> QleT' d (q_pow 3 n) -> QleT' (d * d) (q_pow 9 n).
Proof.
  intros n d Hd0 Hd.
  pose proof (QleT'_to_Qle _ _ Hd0) as Hd0q.
  pose proof (QleT'_to_Qle _ _ Hd) as Hdq.
  assert (H30 : 0 <= q_pow 3 n) by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (H1 : d * d <= q_pow 3 n * d)
    by (apply (Qmult_le_compat_r d (q_pow 3 n) d); assumption).
  assert (H2 : q_pow 3 n * d <= q_pow 3 n * q_pow 3 n).
  { assert (H2' : d * q_pow 3 n <= q_pow 3 n * q_pow 3 n)
      by (apply (Qmult_le_compat_r d (q_pow 3 n) (q_pow 3 n)); assumption).
    assert (Hc : q_pow 3 n * d == d * q_pow 3 n) by ring.
    rewrite Hc. exact H2'. }
  assert (Hfin : d * d <= q_pow 3 n * q_pow 3 n)
    by (apply (Qle_trans _ (q_pow 3 n * d)); assumption).
  assert (Hsq : q_pow 3 n * q_pow 3 n == q_pow 9 n).
  { rewrite <- (zb2_q_pow_mul 3 3 n).
    assert (H33 : 3 * 3 == 9) by ring.
    rewrite H33. reflexivity. }
  rewrite Hsq in Hfin. apply Qle_to_QleT'. exact Hfin.
Qed.

(* 条件分离主定理（线性形式读出接口·显式前提形式·61/676 档）：设 d 满足
   0 ≤ d ≤ 3^(m+1)（Hanson 链供件位按同型实例化），积分值 Isum 满足
   Isum ≤ (1/4)(61/676)^m（族界前提 II′），则当 m ≥ 4 时 d²·Isum < 1。
   （B2 1/11 档同位 dmw2_dc_sep_small 阈值为 m ≥ 5——5→4 移位。） *)
Theorem dig_sep_small : forall (m M : nat) (d : Q),
  (4 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' (zb2_Isum (Datatypes.S m) M) (dig_weight m) ->
  QltT (d * d * zb2_Isum (Datatypes.S m) M) 1.
Proof.
  intros m M d Hm Hd0 Hd HI.
  pose proof (dig_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (zb2_Isum_pos (Datatypes.S m) M) as HposT.
  pose proof (QleT'_to_Qle _ _ (qltT_leT' _ _ HposT)) as HposI.
  pose proof (QleT'_to_Qle _ _ HI) as HIq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m))
                                 (zb2_Isum (Datatypes.S m) M) Hsqq HposI)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
                <= q_pow 9 (Datatypes.S m) * dig_weight m).
  { assert (H2' : zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)
               <= dig_weight m * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (zb2_Isum (Datatypes.S m) M) (dig_weight m)
                                   (q_pow 9 (Datatypes.S m)) HIq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M
               == zb2_Isum (Datatypes.S m) M * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : dig_weight m * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * dig_weight m) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * zb2_Isum (Datatypes.S m) M
                <= (9#4) * q_pow (549#676) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * dig_weight m)).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * zb2_Isum (Datatypes.S m) M)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (dmw2_le_eq _ _ (dig_comp_id m)). }
  pose proof (QltT_to_Qlt _ _ (dig_comp_verdict m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* ============================================================ *)
(* §D 旧档对照与假设审计（零全局假设复核）                                        *)
(* ============================================================ *)

(* 旧档对照（B2 池在卷锚直引）：1/11 档阈值 m ≥ 5 与本机 m ≥ 4 的移位记录：
   旧档 (9/4)(9/11)^5 < 1（dmw2_dc_comp_base）·新档 (9/4)(549/676)^4 < 1
   （dig_comp_base）·两侧锐度锚齐备。 *)
Lemma dig_anchor_thresh_shift :
  QleT' ((1#4) * q_pow dig_theta 1) ((1#4) * q_pow (1#11) 1).
Proof. exact dig_weight_sharpen. Qed.

Separate Extraction dig_comp_verdict dig_sep_small dig_carrier_decay.

Print Assumptions dig_sup_uv.
Print Assumptions dig_sup.
Print Assumptions dig_pointwise_decay.
Print Assumptions dig_carrier_decay.
Print Assumptions dig_comp_id.
Print Assumptions dig_comp_base.
Print Assumptions dig_comp_base_val.
Print Assumptions dig_comp_base3_ge.
Print Assumptions dig_comp_step.
Print Assumptions dig_comp_drop.
Print Assumptions dig_comp_verdict.
Print Assumptions dig_weight_sq.
Print Assumptions dig_sep_small.
Print Assumptions dig_weight_sharpen.
Print Assumptions dig_anchor_gold.
Print Assumptions dig_anchor_sup_half.
Print Assumptions dig_anchor_decay_n1.
Print Assumptions dig_anchor_thresh_shift.
