(* ===================================================================== *)
(*  abl_z3_pointwise.v —— ζ(3) Beukers 三重积分被积族的三变量逐点控制面      *)
(* ===================================================================== *)
(*  使命：                                                            *)
(*    为 Beukers 1979 的 ζ(3) 无理性三重积分                               *)
(*      I_n = ∫₀¹∫₀¹∫₀¹ Nⁿ/Tⁿ⁺¹ dx dy dz                                   *)
(*    （N := x(1−x)y(1−y)z(1−z)，T := 1−xyz）建立被积族的逐点指数控制。     *)
(*    在闭方格 [0,1]³ 上证得三件：                                        *)
(*      ① 平方控制 4N ≤ T²：由 (1−x)(1−y) ≤ 1−xy、精确平方恒等式           *)
(*         T²−4xy(1−xy)(1−z) = (1−2xy+xyz)² 与 z ≤ 1 逐级复合；           *)
(*      ② 线性控制 40N ≤ T：由 ζ(2) 面主不等式 10x(1−x)y(1−y) ≤ 1−xy      *)
(*         （abl_z2_pointwise 的 zb2_ten_le）、4z(1−z) ≤ 1 与              *)
(*         xy ≥ xyz 逐级缩放；                                            *)
(*      ③ 复合面（除法自由形）：4·40^m·N^{m+1} ≤ T^{m+2}（对 m 归纳），     *)
(*         即被积函数族逐点不超过 (1/4)·(1/40)^m 的无除法形。              *)
(*    常数 40 为整值短证书（线性控制步的倒数）；对角线上的真最优在          *)
(*    1/55 邻域，取整值常数以保有理证书形（与 ζ(2) 面 1/10 同款取舍）。     *)
(*  依赖：                                                            *)
(*    Stdlib（QArith/ZArith/Arith/Lia）；池内 abl_z2_pointwise            *)
(*    （Set 层序见证 zb2_qle、线性放缩原子库、主不等式 zb2_ten_le）。       *)
(*    零自动化战术依赖：有理域线性放缩全部以显式引理链组合。                *)
(*  对标：                                                            *)
(*    Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull.        *)
(*    London Math. Soc. 11 (1979) 的 ζ(3) 被积函数族逐点估计步。            *)
(*  构造性：                                                          *)
(*    纯构造性、零假设声明、零承认词面；语句面全 Set 层（zb2_qle）；        *)
(*    非线性不等式以显式平方分解判定，未引入实数、未引入经典逻辑。          *)
(* ===================================================================== *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" abl_z3_pointwise.v（经温控包裹）。            *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.

Require Import abl_z2_pointwise.

Open Scope Q_scope.

(* ============================================================ *)
(* §A 单变元档：4·z(1−z) ≤ 1                                        *)
(* ============================================================ *)

(* 平方分解：1 − 4z(1−z) = (2z−1)² ≥ 0 *)
Lemma zb3_4zz_le_1 : forall z : Q, zb2_qle (4 * z * (1 - z)) 1.
Proof.
  intro z.
  assert (Hs : 0 <= (2 * z - 1) * (2 * z - 1)) by apply zb2_sq_ge0.
  assert (Heq2 : 4 * z * (1 - z) == 1 - (2 * z - 1) * (2 * z - 1)) by ring.
  apply (zb2_qle_wd_l (1 - (2 * z - 1) * (2 * z - 1)) (4 * z * (1 - z)) 1).
  - symmetry. exact Heq2.
  - apply zb2_qle_of_Qle.
    apply (zb2_minus_ge0 ((2 * z - 1) * (2 * z - 1)) 1 Hs).
Qed.

(* ============================================================ *)
(* §B 双变元档：(1−x)(1−y) ≤ 1−xy                                    *)
(* ============================================================ *)

Lemma zb3_11xy_le : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> (1 - x) * (1 - y) <= 1 - x * y.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (HA : 0 <= x * (1 - y)) by (apply zb2_mult2_ge0; assumption).
  assert (HB : 0 <= y * (1 - x)) by (apply zb2_mult2_ge0; assumption).
  assert (Hr : 1 - x * y - ((1 - x) * (1 - y)) == x * (1 - y) + y * (1 - x)) by ring.
  apply (zb2_sub_ge0 ((1 - x) * (1 - y)) (1 - x * y)).
  rewrite Hr.
  apply (Qle_trans 0 (x * (1 - y)) (x * (1 - y) + y * (1 - x))).
  - exact HA.
  - apply zb2_add_ge0_le. exact HB.
Qed.

(* ============================================================ *)
(* §C 平方控制：4N ≤ T²                                              *)
(* ============================================================ *)

(* 精确平方恒等式：T² − 4xy(1−xy)(1−z) = (1−2xy+xyz)² *)
Lemma zb3_sq_id : forall x y z : Q,
  (1 - x*y*z)*(1 - x*y*z) - 4*x*y*(1 - x*y)*(1 - z)
  == (1 - 2*x*y + x*y*z)*(1 - 2*x*y + x*y*z).
Proof. intros x y z. ring. Qed.

Theorem zb3_N_le_Tsq : forall x y z : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  4 * x * (1 - x) * y * (1 - y) * z * (1 - z)
  <= (1 - x*y*z) * (1 - x*y*z).
Proof.
  intros x y z [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply (zb2_le_sub z 1); exact Hz2).
  assert (Hfac2 : 0 <= x * y * (1 - x * y)).
  { assert (Hxy1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
    apply (Qmult_le_0_compat (x * y) (1 - x * y)).
    - apply (Qmult_le_0_compat x y); assumption.
    - apply (zb2_le_sub (x * y) 1); exact Hxy1. }
  assert (Hfac3 : 0 <= (1 - z) * (4 * x * y * (1 - x * y))).
  { apply (Qmult_le_0_compat (1 - z) (4 * x * y * (1 - x * y)))
    ; [ exact Hzb
      | apply (zb2_mult4_ge0 4 x y (1 - x * y))
      ; [ apply (zb2_nat_pos 4) | exact Hx1 | exact Hy1
        | apply (zb2_le_sub (x * y) 1); apply (zb2_xy_le_1 x y); assumption ] ]. }
  (* 步一：(1−x)(1−y) ≤ 1−xy，右乘非负因子 K = 4xyz(1−z) *)
  assert (Hstep1 : ((1 - x) * (1 - y)) * (4 * x * y * z * (1 - z))
                <= (1 - x * y) * (4 * x * y * z * (1 - z))).
  { pose proof (zb3_11xy_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as H11.
    apply (Qmult_le_compat_r ((1 - x) * (1 - y)) (1 - x * y)
                             (4 * x * y * z * (1 - z)) H11).
    apply (Qmult_le_0_compat (((4 * x) * y) * z) (1 - z)).
    - apply (Qmult_le_0_compat ((4 * x) * y) z).
      + apply (Qmult_le_0_compat (4 * x) y).
        * apply (zb2_mult2_ge0 4 x); [ apply (zb2_nat_pos 4) | exact Hx1 ].
        * exact Hy1.
      + exact Hz1.
    - exact Hzb. }
  assert (E1 : ((1 - x) * (1 - y)) * (4 * x * y * z * (1 - z))
            == 4 * x * (1 - x) * y * (1 - y) * z * (1 - z)) by ring.
  assert (HA : 4 * x * (1 - x) * y * (1 - y) * z * (1 - z)
            <= (1 - x * y) * (4 * x * y * z * (1 - z)))
    by (rewrite <- E1; exact Hstep1).
  (* 步二：z ≤ 1 缩放（恒等换形后） *)
  assert (E2 : (1 - x * y) * (4 * x * y * z * (1 - z))
            == z * (1 - z) * (4 * x * y * (1 - x * y))) by ring.
  assert (HB : (1 - x * y) * (4 * x * y * z * (1 - z))
            <= (1 - z) * (4 * x * y * (1 - x * y))).
  { rewrite E2.
    assert (Hrw : z * (1 - z) * (4 * x * y * (1 - x * y))
               == z * ((1 - z) * (4 * x * y * (1 - x * y)))) by ring.
    rewrite Hrw.
    assert (Hrw2 : z * ((1 - z) * (4 * x * y * (1 - x * y)))
                <= 1 * ((1 - z) * (4 * x * y * (1 - x * y))))
      by (apply (Qmult_le_compat_r z 1 ((1 - z) * (4 * x * y * (1 - x * y))))
         ; [ exact Hz2 | exact Hfac3 ]).
    rewrite Qmult_1_l in Hrw2. exact Hrw2. }
  (* 步三：平方恒等式 4xy(1−xy)(1−z) ≤ T² *)
  assert (E3 : (1 - z) * (4 * x * y * (1 - x * y))
            == 4 * x * y * (1 - x * y) * (1 - z)) by ring.
  assert (Hstep3 : 4 * x * y * (1 - x * y) * (1 - z)
                <= (1 - x*y*z) * (1 - x*y*z)).
  { apply (zb2_sub_ge0 _ _).
    pose proof (zb2_sq_ge0 (1 - 2*x*y + x*y*z)) as Hsq.
    rewrite (zb3_sq_id x y z). exact Hsq. }
  assert (HC : (1 - z) * (4 * x * y * (1 - x * y))
            <= (1 - x*y*z) * (1 - x*y*z))
    by (rewrite E3; exact Hstep3).
  apply (Qle_trans _ ((1 - x * y) * (4 * x * y * z * (1 - z)))).
  - exact HA.
  - apply (Qle_trans _ ((1 - z) * (4 * x * y * (1 - x * y)))).
    + exact HB.
    + exact HC.
Qed.

(* ============================================================ *)
(* §D 线性控制：40N ≤ T                                              *)
(* ============================================================ *)

(* 线性控制：40N ≤ T。链：40N = 10A·4C（A = x(1−x)y(1−y)，C = z(1−z)）；
   4C ≤ 1 缩放、ζ(2) 面主不等式 10A ≤ 1−xy、xy ≥ xyz 逐级传递。 *)
Theorem zb3_N_le_T40 : forall x y z : Q,
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  40 * x * (1 - x) * y * (1 - y) * z * (1 - z) <= 1 - x*y*z.
Proof.
  intros x y z [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
  assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
  assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
  assert (Hzb : 0 <= 1 - z) by (apply (zb2_le_sub z 1); exact Hz2).
  assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
  assert (HC0 : 0 <= 4 * z * (1 - z))
    by (apply (Qmult_le_0_compat (4 * z) (1 - z))
       ; [ apply (zb2_mult2_ge0 4 z); [ apply (zb2_nat_pos 4) | exact Hz1 ]
         | exact Hzb ]).
  (* ζ(2) 面主不等式升 Qle 面 *)
  pose proof (zb2_ten_le x y (conj Hx1 Hx2) (conj Hy1 Hy2)) as HtenS.
  pose proof (zb2_qle_to_Qle _ _ HtenS) as Hten.
  (* 链一：10A·4C ≤ (1−xy)·4C *)
  assert (Hs1 : (10 * x * (1 - x) * y * (1 - y)) * (4 * z * (1 - z))
             <= (1 - x * y) * (4 * z * (1 - z)))
    by (apply (Qmult_le_compat_r _ _ _ Hten HC0)).
  assert (E1 : (10 * x * (1 - x) * y * (1 - y)) * (4 * z * (1 - z))
            == 40 * x * (1 - x) * y * (1 - y) * z * (1 - z)) by ring.
  assert (HA : 40 * x * (1 - x) * y * (1 - y) * z * (1 - z)
            <= (1 - x * y) * (4 * z * (1 - z)))
    by (rewrite <- E1; exact Hs1).
  (* 链二：(1−xy)·4C ≤ (1−xy)·1 = 1−xy（4C ≤ 1） *)
  pose proof (zb2_qle_to_Qle _ _ (zb3_4zz_le_1 z)) as H4c.
  assert (Hxy1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
  assert (Hle1 : 0 <= 1 - x * y) by (apply (zb2_le_sub (x * y) 1); exact Hxy1).
  pose proof (Qmult_le_compat_r (4 * z * (1 - z)) 1 (1 - x * y) H4c Hle1) as Ht.
  rewrite Qmult_1_l in Ht.
  assert (E2 : (4 * z * (1 - z)) * (1 - x * y)
            == (1 - x * y) * (4 * z * (1 - z))) by ring.
  rewrite E2 in Ht.
  assert (HB : (1 - x * y) * (4 * z * (1 - z)) <= 1 - x * y) by exact Ht.
  (* 链三：1−xy ≤ 1−xyz（xy ≥ xyz） *)
  assert (Hzr : x * y * z <= x * y).
  { assert (Hq := Qmult_le_compat_r z 1 (x * y) Hz2 Hxy0).
    rewrite Qmult_1_l in Hq.
    assert (Ez : x * y * z == z * (x * y)) by ring.
    rewrite Ez. exact Hq. }
  assert (HC : 1 - x * y <= 1 - x * y * z).
  { apply (zb2_minus_le 1 (x * y * z) (x * y) Hzr). }
  apply (Qle_trans _ ((1 - x * y) * (4 * z * (1 - z)))).
  - exact HA.
  - apply (Qle_trans _ (1 - x * y)).
    + exact HB.
    + exact HC.
Qed.

(* ============================================================ *)
(* §E 复合面：4·40^m·N^{m+1} ≤ T^{m+2}（除法自由形，Set 面）              *)
(* ============================================================ *)

(* 复合衰减：基档即 §C；步档乘 40N ≤ T（§D）后归纳。 *)
Theorem zb3_pointwise_decay : forall (m : nat) (x y z : Q),
  0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= z <= 1 ->
  zb2_qle (4 * zb2_pow 40 m * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
          (zb2_pow (1 - x*y*z) (S (S m))).
Proof.
  intros m x y z Hx Hy Hz.
  revert Hx Hy Hz.
  induction m as [| m IH]; intros [Hx1 Hx2] [Hy1 Hy2] [Hz1 Hz2].
  - (* 基档：4N ≤ T² *)
    apply zb2_qle_of_Qle.
    assert (Heq1 : 4 * zb2_pow 40 0 * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) 1
                == 4 * x * (1-x) * y * (1-y) * z * (1-z)) by (simpl; ring).
    assert (Heq2 : zb2_pow (1 - x*y*z) 2 == (1 - x*y*z)*(1 - x*y*z))
      by (simpl; ring).
    rewrite Heq1, Heq2.
    apply zb3_N_le_Tsq
    ; [ split; assumption | split; assumption | split; assumption ].
  - (* 步档：乘 40N ≤ T 后归纳 *)
    apply zb2_qle_of_Qle.
    assert (HIH := IH (conj Hx1 Hx2) (conj Hy1 Hy2) (conj Hz1 Hz2)).
    apply zb2_qle_to_Qle in HIH.
    pose proof (zb3_N_le_T40 x y z (conj Hx1 Hx2) (conj Hy1 Hy2) (conj Hz1 Hz2))
      as Hstep.
    assert (Hxb : 0 <= 1 - x) by (apply (zb2_le_sub x 1); exact Hx2).
    assert (Hyb : 0 <= 1 - y) by (apply (zb2_le_sub y 1); exact Hy2).
    assert (Hzb : 0 <= 1 - z) by (apply (zb2_le_sub z 1); exact Hz2).
    assert (Hxy0 : 0 <= x * y) by (apply (Qmult_le_0_compat x y); assumption).
    assert (Hxy1 : x * y <= 1) by (apply (zb2_xy_le_1 x y); assumption).
    assert (HN0 : 0 <= x*(1-x)*y*(1-y)*z*(1-z)).
    { assert (Hxy : 0 <= x * (1 - x)) by (apply zb2_mult2_ge0; [exact Hx1 | exact Hxb]).
      assert (Hyy : 0 <= y * (1 - y)) by (apply zb2_mult2_ge0; [exact Hy1 | exact Hyb]).
      assert (Hzz : 0 <= z * (1 - z)) by (apply zb2_mult2_ge0; [exact Hz1 | exact Hzb]).
      assert (Hpre : 0 <= (x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z)))).
      { apply (Qmult_le_0_compat (x * (1 - x)) ((y * (1 - y)) * (z * (1 - z))))
        ; [ exact Hxy
          | apply (Qmult_le_0_compat (y * (1 - y)) (z * (1 - z)))
          ; [ exact Hyy | exact Hzz ] ]. }
      apply (zb2_ge0_wd
               ((x * (1 - x)) * ((y * (1 - y)) * (z * (1 - z))))
               (x*(1-x)*y*(1-y)*z*(1-z)))
      ; [ ring | exact Hpre ]. }
    assert (HP0 : 0 <= zb2_pow (1 - x*y*z) (S (S m)))
      by (apply zb2_pow_ge0; apply (zb2_le_sub (x*y*z) 1)
         ; exact (zb2_xy_le_1 (x*y) z Hxy0 Hxy1 Hz1 Hz2)).
    assert (HK0 : 0 <= zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
      by (apply zb2_pow_ge0; exact HN0).
    assert (H4K : 0 <= (4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)).
    { apply (Qmult_le_0_compat (4 * zb2_pow 40 m)
                               (zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
      ; [ apply (zb2_mult2_ge0 4 (zb2_pow 40 m))
        ; [ apply (zb2_nat_pos 4) | apply zb2_pow_ge0; apply (zb2_nat_pos 40) ]
        | apply zb2_pow_ge0; exact HN0 ]. }
    assert (HN40 : 0 <= 40 * x*(1-x)*y*(1-y)*z*(1-z)).
    { apply (zb2_ge0_wd
               (40 * (x*(1-x)*y*(1-y)*z*(1-z)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)))
      ; [ ring
        | apply (zb2_mult2_ge0 40 (x*(1-x)*y*(1-y)*z*(1-z)))
        ; [ apply (zb2_nat_pos 40) | exact HN0 ] ]. }
    apply (Qle_trans
             (4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m)))
             (40 * x*(1-x)*y*(1-y)*z*(1-z)
              * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
             ((1 - x*y*z) * zb2_pow (1 - x*y*z) (S (S m)))).
    + apply (zb2_le_eq
               (4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)
                * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))).
      assert (Hrw : 4 * zb2_pow 40 (S m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S (S m))
                 == 40 * x*(1-x)*y*(1-y)*z*(1-z)
                    * ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m)))
        by (simpl; ring).
      exact Hrw.
    + apply (zb2_mono_pair
               ((4 * zb2_pow 40 m) * zb2_pow (x*(1-x)*y*(1-y)*z*(1-z)) (S m))
               (zb2_pow (1 - x*y*z) (S (S m)))
               (40 * x*(1-x)*y*(1-y)*z*(1-z)) (1 - x*y*z))
      ; [ exact HIH | exact Hstep | exact H4K | exact HP0 | exact HN40
        | apply (zb2_le_sub (x*y*z) 1)
        ; exact (zb2_xy_le_1 (x*y) z Hxy0 Hxy1 Hz1 Hz2) ].
Qed.

(* 数值基准：m = M = 1 档（载体件使用面）与对角点的线性控制实例
   x = y = z = 1/2：40N = 40/64 = 5/8 ≤ 1 − 1/8 = 7/8（Qcompare 判定） *)
Lemma zb3_lin_anchor : zb2_qle (40 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2)))
                               (1 - (1#2)*(1#2)*(1#2)).
Proof. apply zb2_idrefl. Qed.

(* ============================================================ *)
(* §F 尾舱：主语句公理面自检                                            *)
(* ============================================================ *)

Print Assumptions zb3_4zz_le_1.
Print Assumptions zb3_11xy_le.
Print Assumptions zb3_sq_id.
Print Assumptions zb3_N_le_Tsq.
Print Assumptions zb3_N_le_T40.
Print Assumptions zb3_pointwise_decay.
Print Assumptions zb3_lin_anchor.
