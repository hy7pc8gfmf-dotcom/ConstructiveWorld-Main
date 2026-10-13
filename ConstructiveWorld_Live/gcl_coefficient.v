(* ===================================================================== *)
(*  gcl_coefficient.v —— 组论系数层（DIG 组机承载面之上）                    *)
(*  模块名：gcl_coefficient。                                               *)
(*  使命：Rhin–Viola 组结构置换群法（ζ(2) 双积分 5.0193784 的方法核）的       *)
(*        多项式档系数层——组机 dig_machine 的承载面之上，铸对称化算子与      *)
(*        其对逐点控制常数的改进定理。                                       *)
(*  数学核：                                                                *)
(*    · 群载体：V4 = <Gsw=(y,x), Gco=(1−x,1−y)> 四元素置换群（Gsc=Gco∘Gsw），*)
(*      作用于 (0,1)²；分子 N=x(1−x)y(1−y) 群不变（gcl_N_invar）；分母轨道   *)
(*      {T=1−xy, T̄=x+y−xy}（gcl_T_orbit_Gsw/Gco——T̄ 即 dig_sup_uv 形，      *)
(*      系数轨道覆盖由 DIG 双形 sup 证书承载）。                             *)
(*    · 对称化算子 gcl_sym4（V4 轨道均值·Defined 透明可提取）与其在分母上的  *)
(*      实例 gcl_Tavg=(1/2)(T+T̄)=(1/2)(1+x+y−2xy)。                         *)
(*    · 主改进证书 gcl_sup_avg：24N ≤ 1+x+y−2xy（即 N/Tavg ≤ 1/12），        *)
(*      tight（等号于 τ-不动点 x=y=1/2，gcl_anchor_avg_tight）。逐点常数     *)
(*      锐化 61/676≈0.090237 → 1/12≈0.083333（−7.65%），且 1/12 穿越原       *)
(*      族内极限 θ*=φ⁻⁵≈0.090170（整数判别 30²·5=4500>67²=4489，             *)
(*      gcl_limit_cross_cert——组平均削掉金点脊，原族逐点层不可达）。         *)
(*      证明链（m=x+y, k=xy; B=26−24m+6m²=6(m−2)²+2≥2）：                    *)
(*        Φ:=1+m−2k−24N ≥ 1+m−26k+24mk−6m²k（24k²≤6m²k ⟸ 4k≤m²）            *)
(*              = 1+m−kB ≥ 1+m−(m²/4)B（k≤m²/4）                            *)
(*              = (m−1)²(1+(3/2)m(2−m)) ≥ 0 于 m∈[0,2]（对称化在 (m,k)      *)
(*        坐标恰为 k 的二次凹型，单档收束）。                                *)
(*    · 竞争/分离骨架：3/4 率（9·(1/12)=3/4<1）竞争判定 m≥3（DIG 档 549/676  *)
(*      率为 m≥4——阈值 4→3 移位，m=2 锐度锚 81/64≥1 双侧齐备）；通用分离     *)
(*      骨架 gcl_sep_generic（族参数化·零前提缺口·未来对称化截断族插槽）。    *)
(*  缺口位（显式申报）：对称化截断族（Tavg 分母版的 zb2 族）未铸——           *)
(*    gcl_sep_generic 的 Fam 位为具名插槽；μ_lib 勘形投影 11.5588→8.6377     *)
(*    （对 5.0193784 余距 ≈6.54→≈3.62，勘形级·禁施工引用）以该族铸成为前提。  *)
(*    下一锐化档=双有理生成元档（Rhin–Viola 本体，需 1−xy≠0 域面）。          *)
(*  依赖：Stdlib（QArith/ZArith/Arith/Lia/Setoid）；S01_BaseRing、           *)
(*        S02_CauchyComplete、S03_QExp、BeukersLists；abl_z2_truncfam、      *)
(*        abl_dmw2_pointwise_sharp；dig_machine（dig_sup_uv/dig_weight/     *)
(*        dig_weight_sq/dig_theta）。                                       *)
(*  对标：Rhin–Viola "On a permutation group related to ζ(2)"（Acta Arith.  *)
(*        77 (1996)）；Fischler, Groupes de Rhin-Viola et intégrales        *)
(*        multiples (JTNB 15 (2003) 479-534)。                              *)
(*  构造性注记：全语句 Set 承载；Print Assumptions 全谱 Closed；             *)
(*        Separate Extraction Obj.magic=0；零实数层、零经典逻辑。            *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" gcl_coefficient.v       *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
From Stdlib Require Import Setoid.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp BeukersLists.
Require Import abl_z2_truncfam abl_z2_itg_carrier abl_dmw2_pointwise_sharp dig_machine.

Open Scope Q_scope.

(* ============================================================ *)
(* §G 群载体面：V4 = <Gsw, Gco> 四元素置换群与作用 gcl_act                        *)
(* ============================================================ *)

(* 群元素载体（Set 承载·四元素：恒等/换位/双补/复合） *)
Inductive gcl_g : Set := Gid | Gsw | Gco | Gsc.

(* 群作用（Defined 透明·多项式档生成元）：
   Gid=(x,y)，Gsw=(y,x)，Gco=(1−x,1−y)，Gsc=Gco∘Gsw=(1−y,1−x)。 *)
Definition gcl_act (g : gcl_g) (x y : Q) : Q * Q :=
  match g with
  | Gid => (x, y)
  | Gsw => (y, x)
  | Gco => (1 - x, 1 - y)
  | Gsc => (1 - y, 1 - x)
  end.

(* 生成元对合的分量面（Gco 自合：1−(1−x)=x；Gsw 自合：定义性） *)
Lemma gcl_copl_invol_x : forall x : Q, 1 - (1 - x) == x.
Proof. intro x. ring. Qed.

Lemma gcl_act_Gco_fst : forall x y : Q, fst (gcl_act Gco x y) == 1 - x.
Proof. reflexivity. Qed.

Lemma gcl_act_Gco_snd : forall x y : Q, snd (gcl_act Gco x y) == 1 - y.
Proof. reflexivity. Qed.

Lemma gcl_act_Gsc_fst : forall x y : Q, fst (gcl_act Gsc x y) == 1 - y.
Proof. reflexivity. Qed.

Lemma gcl_act_Gsc_snd : forall x y : Q, snd (gcl_act Gsc x y) == 1 - x.
Proof. reflexivity. Qed.

(* 分子不变面：N=x(1−x)y(1−y) 在全群轨道上不变
   （Beukers 衰减供能面——群作用不改衰减原料，只置换分母轨道）。 *)
Lemma gcl_N_invar : forall (g : gcl_g) (x y : Q),
  (match g with
   | Gid => x * (1 - x) * y * (1 - y)
   | Gsw => y * (1 - y) * x * (1 - x)
   | Gco => (1 - x) * (1 - (1 - x)) * (1 - y) * (1 - (1 - y))
   | Gsc => (1 - y) * (1 - (1 - y)) * (1 - x) * (1 - (1 - x))
   end) == x * (1 - x) * y * (1 - y).
Proof. intros g x y. destruct g; ring. Qed.

(* 分母轨道面：T∘Gsw = T（换位不变）；T∘Gco = T̄ = x+y−xy（共轭分母）。
   —— 组作用在分母轨道 {T, T̄} 上的置换记录：dig_sup（T 形）与
   dig_sup_uv（T̄ 形，原变元读出）恰为两位轨道代表。 *)
Lemma gcl_T_orbit_Gsw : forall x y : Q,
  1 - fst (gcl_act Gsw x y) * snd (gcl_act Gsw x y) == 1 - x * y.
Proof. intros x y. unfold gcl_act. simpl. ring. Qed.

Lemma gcl_T_orbit_Gco : forall x y : Q,
  1 - fst (gcl_act Gco x y) * snd (gcl_act Gco x y) == x + y - x * y.
Proof. intros x y. unfold gcl_act. simpl. ring. Qed.

(* 复合面：Gsc = Gco∘Gsw（分量定义性一致） *)
Lemma gcl_Gsc_co_sw : forall x y : Q,
  gcl_act Gsc x y = (1 - y, 1 - x).
Proof. reflexivity. Qed.

(* ============================================================ *)
(* §S 对称化算子面：V4 轨道均值 gcl_sym4 与分母实例 gcl_Tavg                      *)
(* ============================================================ *)

(* 对称化算子（Defined 透明·可提取）：函数在 V4 全轨道上的均值。
   Rhin–Viola 组结构法的系数步：积分量在群轨道上平均后，其逐点控制
   函数获得群对称性，sup 随之可优化。 *)
Definition gcl_sym4 (f : Q -> Q -> Q) (x y : Q) : Q :=
  (f x y + f y x + f (1 - x) (1 - y) + f (1 - y) (1 - x)) * (1#4).

(* 对称化分母（本件系数层的改进载体）：Tavg = (T+T̄)/2 = (1/2)(1+x+y−2xy)
   —— gcl_sym4 在分母函数上的实例（Gsw 轨道两点重合）。 *)
Definition gcl_Tavg (x y : Q) : Q := (1#2) * (1 + x + y - 2 * x * y).

(* 算子实例一致：sym4(分母) == Tavg *)
Lemma gcl_sym4_Tavg : forall x y : Q,
  gcl_sym4 (fun a b : Q => 1 - a * b) x y == gcl_Tavg x y.
Proof.
  intros x y. unfold gcl_sym4, gcl_Tavg. cbv beta. ring.
Qed.

(* 算子不动面：sym4(N) == N（分子群不变 → 均值还原） *)
Lemma gcl_sym4_N : forall x y : Q,
  x * (1 - x) * y * (1 - y)
  == gcl_sym4 (fun a b : Q => a * (1 - a) * b * (1 - b)) x y.
Proof.
  intros x y. unfold gcl_sym4. cbv beta. ring.
Qed.

(* ============================================================ *)
(* §A 系数改进证书面（主定理）：对称化 tight 证书 24N ≤ 1+x+y−2xy                 *)
(* ============================================================ *)

(* τ-共轭槽（轨道覆盖·DIG 双形读出）：dig_sup_uv 在原变元下的 T̄ 形——
   即 copl 像分母的 sup 证书，组论读法下与 dig_sup 构成轨道两位。 *)
Theorem gcl_sup_copl : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  676 * x * (1 - x) * y * (1 - y) <= 61 * (x + y - x * y).
Proof. intros x y Hx Hy. exact (dig_sup_uv x y Hx Hy). Qed.

(* 对称化 tight 证书（主定理·新数学）：0≤x,y≤1 ⟹ 24N ≤ 1+x+y−2xy，
   即 N/Tavg ≤ 1/12——比 DIG 档 61/676 更锐（−7.65%），且 1/12 穿越
   原族逐点极限 θ*=φ⁻⁵（组平均削金点脊）。
   证明链（m=x+y, k=xy; B=6(m−2)²+2）：
   Φ=1+m−2k−24N ≥ 1+m−26k+24mk−6m²k = 1+m−kB ≥ 1+m−(m²/4)B
     = (m−1)²(1+(3/2)m(2−m)) ≥ 0。 *)
Theorem gcl_sup_avg : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  24 * x * (1 - x) * y * (1 - y) <= 1 + x + y - 2 * x * y.
Proof.
  intros x y [Hx1 Hx2] [Hy1 Hy2].
  (* m = x+y ∈ [0,2]，k = xy ≥ 0，4k ≤ m² *)
  assert (Hm0 : 0 <= x + y).
  { apply (Qle_trans 0 (0 + 0) (x + y)).
    - rewrite Qplus_0_l. apply Qle_refl.
    - apply (Qplus_le_compat 0 x 0 y); assumption. }
  assert (Hm2 : x + y <= 2).
  { apply (Qle_trans (x + y) (1 + 1) 2).
    - apply (Qplus_le_compat x 1 y 1); assumption.
    - assert (Heq : 1 + 1 == 2) by ring.
      rewrite Heq. apply Qle_refl. }
  assert (Hk0 : 0 <= x * y) by (apply Qmult_le_0_compat; assumption).
  assert (Hdsq : 0 <= (x + y) * (x + y) - 4 * (x * y)).
  { assert (Hd : (x + y) * (x + y) - 4 * (x * y) == (x - y) * (x - y)) by ring.
    rewrite Hd. apply dmw2_sq_ge0. }
  assert (H4k : 4 * (x * y) <= (x + y) * (x + y))
    by (apply (dmw2_sub_ge0 (4 * (x * y)) ((x + y) * (x + y))); exact Hdsq).
  assert (HkQ : x * y <= (x + y) * (x + y) * (1#4)).
  { assert (Heq : (x + y) * (x + y) * (1#4) - x * y
               == ((x + y) * (x + y) - 4 * (x * y)) * (1#4)) by ring.
    apply (dmw2_sub_ge0 (x * y) ((x + y) * (x + y) * (1#4))).
    rewrite Heq. apply Qmult_le_0_compat.
    - exact Hdsq.
    - unfold Qle. simpl. lia. }
  (* B = 26−24m+6m² = 6(m−2)²+2 ≥ 2 > 0 *)
  assert (HB : 0 <= 26 - 24 * (x + y) + 6 * (x + y) * (x + y)).
  { assert (Hid : 26 - 24 * (x + y) + 6 * (x + y) * (x + y)
               == 6 * (2 - (x + y)) * (2 - (x + y)) + 2) by ring.
    rewrite Hid.
    assert (Hs : 0 <= (2 - (x + y)) * (2 - (x + y))) by apply dmw2_sq_ge0.
    assert (HX : 0 <= 6 * (2 - (x + y)) * (2 - (x + y))).
    { apply Qmult_le_0_compat.
      - apply (dmw2_mult2_ge0 6 (2 - (x + y)))
        ; [ unfold Qle; simpl; lia | ].
        apply (dmw2_le_sub (x + y) 2). exact Hm2.
      - apply (dmw2_le_sub (x + y) 2). exact Hm2. }
    apply (Qle_trans 0 (6 * (2 - (x + y)) * (2 - (x + y)))
                      (6 * (2 - (x + y)) * (2 - (x + y)) + 2)).
    - exact HX.
    - apply dmw2_add_ge0_le. unfold Qle. simpl. lia. }
  (* 步一：24k² ≤ 6m²k（4k ≤ m² 乘 6k ≥ 0） *)
  assert (H6k : 0 <= 6 * (x * y))
    by (apply (dmw2_mult2_ge0 6 (x * y)); [ unfold Qle; simpl; lia | exact Hk0 ]).
  assert (HS1 : 24 * (x * y) * (x * y) <= 6 * (x + y) * (x + y) * (x * y)).
  { pose proof (Qmult_le_compat_r (4 * (x * y)) ((x + y) * (x + y))
                  (6 * (x * y)) H4k H6k) as H.
    assert (E1 : (4 * (x * y)) * (6 * (x * y)) == 24 * (x * y) * (x * y)) by ring.
    assert (E2 : (x + y) * (x + y) * (6 * (x * y))
              == 6 * (x + y) * (x + y) * (x * y)) by ring.
    rewrite E1, E2 in H. exact H. }
  (* 步二：kB ≤ (m²/4)B（k ≤ m²/4 与 B ≥ 0） *)
  assert (Hle2 : 1 + x + y - (x + y) * (x + y) * (1#4)
                        * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))
              <= 1 + x + y - (x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))).
  { apply (dmw2_minus_le (1 + x + y)
             ((x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))
             ((x + y) * (x + y) * (1#4)
               * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))).
    pose proof (Qmult_le_compat_r (x * y) ((x + y) * (x + y) * (1#4))
                  (26 - 24 * (x + y) + 6 * (x + y) * (x + y)) HkQ HB) as H.
    exact H. }
  (* 步三：末式因子分解（(m−1)²(1+(3/2)m(2−m)) ≥ 0） *)
  assert (Hprod : 0 <= ((x + y) - 1) * ((x + y) - 1)
                        * (1 + (3#2) * ((x + y) * (2 - (x + y))))).
  { apply Qmult_le_0_compat.
    - apply dmw2_sq_ge0.
    - apply (Qle_trans 0 1 (1 + (3#2) * ((x + y) * (2 - (x + y))))).
      + unfold Qle. simpl. lia.
      + apply (dmw2_add_ge0_le 1 ((3#2) * ((x + y) * (2 - (x + y))))).
        apply (dmw2_mult2_ge0 (3#2) ((x + y) * (2 - (x + y))))
        ; [ unfold Qle; simpl; lia | ].
        apply (dmw2_mult2_ge0 (x + y) (2 - (x + y)))
        ; [ exact Hm0 | apply (dmw2_le_sub (x + y) 2); exact Hm2 ]. }
  (* 链式合成 *)
  assert (Hle1 : 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 6 * (x + y) * (x + y) * (x * y)
              <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 24 * (x * y) * (x * y)).
  { apply (dmw2_minus_le (1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y))
             (24 * (x * y) * (x * y))
             (6 * (x + y) * (x + y) * (x * y))).
    exact HS1. }
  assert (Hchain : ((x + y) - 1) * ((x + y) - 1)
                     * (1 + (3#2) * ((x + y) * (2 - (x + y))))
              <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                       - 24 * (x * y) * (x * y)).
  { assert (Efin : ((x + y) - 1) * ((x + y) - 1)
                      * (1 + (3#2) * ((x + y) * (2 - (x + y))))
               == 1 + x + y - (x + y) * (x + y) * (1#4)
                        * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))) by ring.
    rewrite Efin.
    apply (Qle_trans _ (1 + x + y - (x * y)
                          * (26 - 24 * (x + y) + 6 * (x + y) * (x + y)))).
    - exact Hle2.
    - assert (Hd2 : 1 + x + y - (x * y) * (26 - 24 * (x + y) + 6 * (x + y) * (x + y))
                 == 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                        - 6 * (x + y) * (x + y) * (x * y)) by ring.
      rewrite Hd2. exact Hle1. }
  assert (HPhi0 : 0 <= 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                        - 24 * (x * y) * (x * y)).
  { apply (Qle_trans 0 (((x + y) - 1) * ((x + y) - 1)
                          * (1 + (3#2) * ((x + y) * (2 - (x + y)))))).
    - exact Hprod.
    - exact Hchain. }
  (* 终步：Φ ≥ 0 ⟹ 24N ≤ 1+x+y−2xy *)
  assert (E0 : 1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y)
            == 1 + x + y - 26 * (x * y) + 24 * (x + y) * (x * y)
                     - 24 * (x * y) * (x * y)) by ring.
  apply (Qle_trans (24 * x * (1 - x) * y * (1 - y))
    (24 * x * (1 - x) * y * (1 - y)
       + (1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y)))
    (1 + x + y - 2 * x * y)).
  - apply dmw2_add_ge0_le.
    rewrite E0. exact HPhi0.
  - assert (HeqF : 24 * x * (1 - x) * y * (1 - y)
                + (1 + x + y - 2 * x * y - 24 * x * (1 - x) * y * (1 - y))
                == 1 + x + y - 2 * x * y) by ring.
    rewrite HeqF. apply Qle_refl.
Qed.

(* 主接口（Set 面）：N ≤ (1/12)·Tavg 于全方块 *)
Theorem gcl_avg_cert : forall x y : Q,
  0 <= x <= 1 -> 0 <= y <= 1 ->
  QleT' (12 * x * (1 - x) * y * (1 - y)) (gcl_Tavg x y).
Proof.
  intros x y Hx Hy.
  pose proof (gcl_sup_avg x y Hx Hy) as H.
  assert (H12 : 0 <= (1#2)) by (unfold Qle; simpl; lia).
  pose proof (Qmult_le_compat_r (24 * x * (1 - x) * y * (1 - y))
                (1 + x + y - 2 * x * y) (1#2) H H12) as Hm.
  assert (E1 : (24 * x * (1 - x) * y * (1 - y)) * (1#2)
            == 12 * x * (1 - x) * y * (1 - y)) by ring.
  assert (E2 : (1 + x + y - 2 * x * y) * (1#2)
            == (1#2) * (1 + x + y - 2 * x * y)) by ring.
  rewrite E1, E2 in Hm.
  unfold gcl_Tavg. apply Qle_to_QleT'. exact Hm.
Qed.

(* tight 锚：等号于 τ-不动点 (1/2,1/2)——24N = 1+x+y−2xy = 3/2，
   证书常数 1/12 为 sup 精确值（不可再降于本族） *)
Lemma gcl_anchor_avg_tight :
  24 * (1#2) * (1 - (1#2)) * (1#2) * (1 - (1#2))
  == 1 + (1#2) + (1#2) - 2 * (1#2) * (1#2).
Proof. vm_compute. reflexivity. Qed.

(* 族内极限穿越判别（整数证书）：1/12 < θ* = (5√5−11)/2 = φ⁻⁵
   ⟺ 30√5 > 67 ⟺ 30²·5 = 4500 > 67² = 4489——对称化系数层的族内极限
   严格低于原族逐点极限（组平均的结构性产出记录） *)
Lemma gcl_limit_cross_cert : QltT 4489 4500.
Proof. exact (id_refl (A:=bool) (x:=Qlt_bool 4489 4500)). Qed.

(* ============================================================ *)
(* §C 竞争/分离骨架面：3/4 率（对称化档 (1/4)(1/12)^m）                                           *)
(* ============================================================ *)

(* 对称化档机件权重：族界面 (1/4)·(1/12)^m（供下游测度档推算） *)
Definition gcl_weight_G (m : nat) : Q := (1#4) * q_pow (1#12) m.

Lemma gcl_weight_G_ge0 : forall m : nat, QleT' 0 (gcl_weight_G m).
Proof.
  intro m. apply Qle_to_QleT'. apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply q_pow_nonneg. unfold Qle. simpl. lia.
Qed.

(* 权重锐化锚：(1/4)(1/12) ≤ (1/4)(61/676)（⟺ 676 ≤ 732；Qle_bool 字面） *)
Lemma gcl_weight_sharpen_G : QleT' (gcl_weight_G 1) (dig_weight 1).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool (gcl_weight_G 1) (dig_weight 1))).
Qed.

(* 竞争恒等式：9^(m+1)·(1/4)·(1/12)^m = (9/4)·(3/4)^m（9·(1/12)=3/4） *)
Lemma gcl_comp_id_G : forall m : nat,
  q_pow 9 (Datatypes.S m) * gcl_weight_G m == (9#4) * q_pow (3#4) m.
Proof.
  intro m. unfold gcl_weight_G.
  assert (Hpm : q_pow 9 m * q_pow (1#12) m == q_pow (3#4) m).
  { rewrite <- (zb2_q_pow_mul 9 (1#12) m).
    assert (H912 : 9 * (1#12) == (3#4)) by ring.
    rewrite H912. reflexivity. }
  assert (Hre : q_pow 9 (Datatypes.S m) * ((1#4) * q_pow (1#12) m)
             == (9 * (1#4)) * (q_pow 9 m * q_pow (1#12) m))
    by (rewrite (q_pow_succ 9 m); ring).
  rewrite Hre, Hpm.
  assert (H94 : 9 * (1#4) == (9#4)) by ring.
  rewrite H94. reflexivity.
Qed.

(* 竞争基档：(9/4)·(3/4)³ = 243/256 < 1（字面判定——阈值 m ≥ 3） *)
Lemma gcl_comp_base_G : QltT ((9#4) * q_pow (3#4) 3) 1.
Proof.
  exact (id_refl (A:=bool) (x:=Qlt_bool ((9#4) * q_pow (3#4) 3) 1)).
Qed.

(* 阈值锐度锚：(9/4)·(3/4)² = 81/64 ≥ 1——m=2 不足，m ≥ 3 为锐阈值 *)
Lemma gcl_comp_base2_ge_G : QleT' 1 ((9#4) * q_pow (3#4) 2).
Proof.
  exact (id_refl (A:=bool) (x:=Qle_bool 1 ((9#4) * q_pow (3#4) 2))).
Qed.

(* 竞争步进：(9/4)·(3/4)^(m+1) ≤ (9/4)·(3/4)^m *)
Lemma gcl_comp_step_G : forall m : nat,
  QleT' ((9#4) * q_pow (3#4) (Datatypes.S m)) ((9#4) * q_pow (3#4) m).
Proof.
  intro m.
  assert (Hge0 : 0 <= (9#4) * q_pow (3#4) m).
  { apply Qmult_le_0_compat.
    - unfold Qle. simpl. lia.
    - apply q_pow_nonneg. unfold Qle. simpl. lia. }
  assert (Hs34 : (3#4) <= 1) by (unfold Qle; simpl; lia).
  apply Qle_to_QleT'.
  assert (Hrw : (9#4) * q_pow (3#4) (Datatypes.S m)
             == (3#4) * ((9#4) * q_pow (3#4) m))
    by (rewrite (q_pow_succ (3#4) m); ring).
  rewrite Hrw.
  pose proof (Qmult_le_compat_r (3#4) 1 ((9#4) * q_pow (3#4) m)
                Hs34 Hge0) as Hle.
  assert (Hr2 : 1 * ((9#4) * q_pow (3#4) m) == (9#4) * q_pow (3#4) m) by ring.
  rewrite Hr2 in Hle. exact Hle.
Qed.

(* 竞争平移：对平移量 d 归纳 *)
Lemma gcl_comp_drop_G : forall (d m : nat),
  QleT' ((9#4) * q_pow (3#4) (m + d)) ((9#4) * q_pow (3#4) m).
Proof.
  induction d as [| d IH]; intro m.
  - assert (Hd : (m + 0 = m)%nat) by apply Nat.add_0_r.
    rewrite Hd. apply Qle_to_QleT'. apply Qle_refl.
  - assert (Hs : (m + Datatypes.S d = Datatypes.S (m + d))%nat)
      by apply Nat.add_succ_r.
    rewrite Hs.
    apply (qleT'_trans ((9#4) * q_pow (3#4) (Datatypes.S (m + d)))
                       ((9#4) * q_pow (3#4) (m + d))
                       ((9#4) * q_pow (3#4) m)).
    + apply gcl_comp_step_G.
    + apply IH.
Qed.

(* 竞争判定：m ≥ 3 ⟹ (9/4)·(3/4)^m < 1
   （DIG 档 549/676 率阈值为 m ≥ 4——对称化系数层 4→3 移位，
     双侧锐度锚 gcl_comp_base_G / gcl_comp_base2_ge_G 齐备） *)
Lemma gcl_comp_verdict_G : forall m : nat, (3 <= m)%nat -> QltT ((9#4) * q_pow (3#4) m) 1.
Proof.
  induction m as [| m IH]; intro Hm.
  - exfalso. lia.
  - destruct (le_lt_dec 3 m) as [Hle | Hlt].
    + apply (qleT'_ltT_ltT ((9#4) * q_pow (3#4) (Datatypes.S m))
                           ((9#4) * q_pow (3#4) m) 1).
      * apply gcl_comp_step_G.
      * apply IH. exact Hle.
    + assert (Heq : (Datatypes.S m = 3)%nat) by lia.
      rewrite Heq. exact gcl_comp_base_G.
Qed.

(* 通用分离骨架（族参数化·零前提缺口·插槽形）：设 Fam 为任一对称化截断族
   的积分值函数（非负·族界 ≤ (1/4)(1/12)^m 给定），d 满足 Hanson 链
   0 ≤ d ≤ 3^(m+1)，则 m ≥ 3 时 d²·Fam(m) < 1。
   —— 缺口位（GAPASUME 画像·如实申报）：具体对称化族（Tavg 分母版截断族）
      未铸，Fam 为具名插槽；插槽供件即触发下游 μ_lib 实降。 *)
Theorem gcl_sep_generic : forall (Fam : nat -> Q) (m : nat) (d : Q),
  (3 <= m)%nat ->
  QleT' 0 d ->
  QleT' d (q_pow 3 (Datatypes.S m)) ->
  QleT' 0 (Fam m) ->
  QleT' (Fam m) (gcl_weight_G m) ->
  QltT (d * d * Fam m) 1.
Proof.
  intros Fam m d Hm Hd0 Hd Hf0 Hf.
  pose proof (dig_weight_sq (Datatypes.S m) d Hd0 Hd) as Hsq.
  pose proof (QleT'_to_Qle _ _ Hsq) as Hsqq.
  pose proof (QleT'_to_Qle _ _ Hf0) as Hf0q.
  pose proof (QleT'_to_Qle _ _ Hf) as Hfq.
  assert (H9 : 0 <= q_pow 9 (Datatypes.S m))
    by (apply q_pow_nonneg; unfold Qle; simpl; lia).
  assert (Hstep1 : d * d * Fam m <= q_pow 9 (Datatypes.S m) * Fam m)
    by (apply (Qmult_le_compat_r (d * d) (q_pow 9 (Datatypes.S m))
                                 (Fam m) Hsqq Hf0q)).
  assert (Hstep2 : q_pow 9 (Datatypes.S m) * Fam m
                <= q_pow 9 (Datatypes.S m) * gcl_weight_G m).
  { assert (H2' : Fam m * q_pow 9 (Datatypes.S m)
               <= gcl_weight_G m * q_pow 9 (Datatypes.S m))
      by (apply (Qmult_le_compat_r (Fam m) (gcl_weight_G m)
                                   (q_pow 9 (Datatypes.S m)) Hfq H9)).
    assert (Hc1 : q_pow 9 (Datatypes.S m) * Fam m
               == Fam m * q_pow 9 (Datatypes.S m)) by ring.
    assert (Hc2 : gcl_weight_G m * q_pow 9 (Datatypes.S m)
               == q_pow 9 (Datatypes.S m) * gcl_weight_G m) by ring.
    rewrite Hc1, <- Hc2. exact H2'. }
  assert (Hchain : d * d * Fam m <= (9#4) * q_pow (3#4) m).
  { apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * gcl_weight_G m)).
    - apply (Qle_trans _ (q_pow 9 (Datatypes.S m) * Fam m)).
      + exact Hstep1.
      + exact Hstep2.
    - exact (dmw2_le_eq _ _ (gcl_comp_id_G m)). }
  pose proof (QltT_to_Qlt _ _ (gcl_comp_verdict_G m Hm)) as Hv.
  pose proof (Qle_lt_trans _ _ _ Hchain Hv) as Hfin.
  apply Qlt_to_QltT. exact Hfin.
Qed.

(* ============================================================ *)
(* §D 提取与假设审计（零全局假设复核）                                            *)
(* ============================================================ *)

Separate Extraction gcl_comp_verdict_G gcl_sep_generic gcl_avg_cert
  gcl_sym4 gcl_Tavg gcl_act gcl_weight_G.

Print Assumptions gcl_N_invar.
Print Assumptions gcl_T_orbit_Gsw.
Print Assumptions gcl_T_orbit_Gco.
Print Assumptions gcl_sym4_Tavg.
Print Assumptions gcl_sym4_N.
Print Assumptions gcl_sup_copl.
Print Assumptions gcl_sup_avg.
Print Assumptions gcl_avg_cert.
Print Assumptions gcl_anchor_avg_tight.
Print Assumptions gcl_limit_cross_cert.
Print Assumptions gcl_weight_G_ge0.
Print Assumptions gcl_weight_sharpen_G.
Print Assumptions gcl_comp_id_G.
Print Assumptions gcl_comp_base_G.
Print Assumptions gcl_comp_base2_ge_G.
Print Assumptions gcl_comp_step_G.
Print Assumptions gcl_comp_drop_G.
Print Assumptions gcl_comp_verdict_G.
Print Assumptions gcl_sep_generic.
