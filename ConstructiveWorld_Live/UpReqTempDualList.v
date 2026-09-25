(* ========================================================================= *)
(* UpReqTempDualList.v —— 温度族 sigT 对偶的通用 list 载体装配               *)
(* 使命：本件形式化定理 4.6d 的通用 list 载体版：从熵等 + 同能量 + 归一化/    *)
(*       逐点正 ⟹ 指定位逐点 p ≡ p_T，并以五合取支（归一化/正性/约束/        *)
(*       最优/唯一）sigT 形装配总件 temp_energy_dual_closed_list。           *)
(* 依赖：CW_ConstructiveWorld_219、UpRealLeB、G08_Gibbs、UpReqTempDefs、      *)
(*       UpReqEntropyDeficitTemp、UpReqEntropyMaxTemp、UpReqKLSTangent、      *)
(*       UpReqTempDual。                                                     *)
(* 对标：stdlib List 折叠求和；Gibbs 分布温度族（Boltzmann 分布族）。         *)
(* 构造性注记：Set 层承载——装配语句全 real_eq/real_lt/real_le 逐点 Set 值  *)
(*   + sigT/prod 组装，零 Prop 泄露；零承认、公理面为空；全 Qed；             *)
(*   非平凡交付（两处定义层直接归纳/五步链内联重演，无拆分式假非平凡）。      *)
(* 编译配方：Rocq 9.1 直调，cpu_guard 温控包装，-Q 单根。                     *)
(* ========================================================================= *)
(* 数学结构：                                                               *)
(*   逐项 kl_term 消去链（gibbe2/gibbsd 组内件逐位复用，零重建）：           *)
(*   1. Σ(p−q) ≡ 0（gibbsd_list_sum_minus + 双归一化 + plus_opp）            *)
(*   2. Σ(kl + −(p−q)) ≡ 0（real_list_sum_add + real_list_sum_opp           *)
(*      + 前步换载）                                                        *)
(*   3. 逐点 0 ≤_B kl + −(p−q)（gibbsd_gibbs_pointwise_B[D0 切线参数位]     *)
(*      + gibbe2_le_b_nonneg_diff[B3]）                                     *)
(*   4. 分解位提取：载体取 app l1 (cons s0 l2) 分解形（同                    *)
(*      UpReqKLSTangent l1++s0::l2 形先例），前缀归纳 + 二项钳零             *)
(*      （gibbe2_clamp_head/_r[C1/C2]）+ 非负和抬升（gibbsd_list_sum_le_b    *)
(*      实例）⟹                                                            *)
(*   5. kl ≡ p−q（gibbe2_kl_eq_of_w_zero[D0]）⟹ 切点等式                    *)
(*      （gibbe2_tangent_eq[D1]）⟹ q/p ≡ 1（t1_log_eq_linear_inject         *)
(*      [无条件注入形]）⟹ p ≡ q（gibbsd_p_mult_ratio）。                    *)
(* ------------------------------------------------------------------ *)
(* 装配件五合取支逐位对照（Id 层 4.6d）：                                  *)
(*   Id sigT (fun pb => …)        ↝ Real sigT×2（pb + 正性见证 Hpb          *)
(*     第二见证位——real_entropy_dist 前提位所需；同族两装配件同形）         *)
(*   Id And                       ↝ Real prod（Set 层乘积，零 Prop）        *)
(*   支1 归一化 normalized pb     ↝ real_eq (Σ pb) one                      *)
(*     （real_boltzmann_dist_temp_normalized 全 arity 显式应用）             *)
(*   支2 正性 positive_dist pb    ↝ sigT 第二见证 Hpb                       *)
(*   支3 约束 Id (E pb) (E_temp)  ↝ real_eq (E pb) E_T（定义性收敛，        *)
(*     real_eq_refl 完成；E 位 UpReqEntropyDeficitTemp real_energy_exp_temp  *)
(*     同位）                                                               *)
(*   支4 最优 le (S p) (S pb)     ↝ 逐 eps 档 real_le (S p) (S pb+eps)      *)
(*     （real_max_entropy_is_boltzmann_temp_eps 全 arity 显式应用——         *)
(*     list 载体单调接口 real_list_sum_le 直接供给，Gibbs 支零接口前提      *)
(*     消解；Or 形无条件版受比较判定界，逐 eps 档为序档最强可达形，         *)
(*     与依赖族分档结论同源）                                               *)
(*   支5 唯一 熵等⟹逐点 p≡pb    ↝ 分解位档 real_eq (p s0) (p_T s0)：       *)
(*     t13_entropy_eq_kl_zero[熵亏件反向] ⟹ KL≡0 + 熵亏桥换载              *)
(*     kl_term 消去链完成。受判定界说明：通用载体 Or 形精确逐点仍受          *)
(*     三分判定界；Bishop ≤_B 档 + 分解位提取为构造性可达最强档，           *)
(*     KL 的构造内容（切线+钳零+注入）全量进入，非缩水。                    *)
(* ------------------------------------------------------------------ *)
(* 节内前提位申报：节 ListTempDual 七位接口字段（X、l1、s0、l2、T0、         *)
(*   T0_pos、e0）为通用载体数据参数：求和面结构位（求和/正性/外延/单调/     *)
(*   线性/加法）已由 S08 real_list_sum 族在节内以 Let 直接供给消解；         *)
(*   余七位全部被节内定理语句面使用，实例化将收窄语句签名，按签名不动       *)
(*   纪律保留为显式接口前提。温度正性 T0_pos 与表非空由 t34_app_cons_nonnil *)
(*   结构位消解。                                                           *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import G08_Gibbs.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.
Require Import UpReqKLSTangent.
Require Import UpReqTempDual.

(* ============================================================ *)

(* ============================================================ *)

(* 常零折叠 ≡ 0（换载支用；nil 支 refl，cons 支 comm+plus_zero） *)
Lemma t34_list_sum_const_zero : forall (X : Type) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l. induction l as [| w l IH].
  - apply real_eq_refl.
  - (* cons：Σ(cons w l) ≡ 0+Σl ≡ Σl+0 ≡ Σl ≡ 0（refl/comm/plus_zero/IH； *)
    (*   零 simpl——simpl 会把 real_zero delta 展开，unfold 形与库件失配） *)
    exact (real_eq_trans
             (real_list_sum X (fun _ : X => real_zero) (cons w l))
             (real_list_sum X (fun _ : X => real_zero) l)
             real_zero
             (real_eq_trans
                (real_plus real_zero
                   (real_list_sum X (fun _ : X => real_zero) l))
                (real_plus (real_list_sum X (fun _ : X => real_zero) l)
                           real_zero)
                (real_list_sum X (fun _ : X => real_zero) l)
                (real_plus_comm real_zero
                   (real_list_sum X (fun _ : X => real_zero) l))
                (real_plus_zero (real_list_sum X (fun _ : X => real_zero) l)))
             IH).
Qed.

(* 逐点 0 ≤_B ⟹ 和 0 ≤_B（real_le_b 定义层直接归纳闭合） *)
Lemma t34_list_sum_le_b_nonneg : forall (X : Type) (f : X -> Real) (l : list X),
  (forall w : X, real_le_b real_zero (f w)) ->
  real_le_b real_zero (real_list_sum X f l).
Proof.
  intros X f l Hpt.
  unfold real_le_b.
  induction l as [| w l IH].
  - (* nil：Σnil ≡ 0（iota 换向检查闭合），0 < 0+eps（lt 平移件直取） *)
    intros eps Heps.
    exact (real_lt_plus_r_zero real_zero eps Heps).
  - (* cons：eps 折半见证 + 逐点/归纳双支 + real_lt_compat 四段换形闭合 *)
    intros eps Heps.
    assert (Hpos : real_lt real_zero (real_mult eps gibbsd_half)).
    { exact (real_mult_positive eps gibbsd_half Heps gibbsd_half_pos). }
    assert (Ha : real_lt real_zero
                   (real_plus (f w) (real_mult eps gibbsd_half))).
    { exact (Hpt w (real_mult eps gibbsd_half) Hpos). }
    assert (Ht : real_lt real_zero
                   (real_plus (real_list_sum X f l)
                              (real_mult eps gibbsd_half))).
    { exact (IH (real_mult eps gibbsd_half) Hpos). }
    apply (RealSetoid.real_lt_compat
             (real_plus real_zero real_zero)
             real_zero
             (real_plus (real_plus (f w) (real_mult eps gibbsd_half))
                        (real_plus (real_list_sum X f l)
                                   (real_mult eps gibbsd_half)))
             (real_plus (real_plus (f w) (real_list_sum X f l)) eps)).
    + exact (real_plus_zero real_zero).
    + exact (real_eq_trans
               (real_plus (real_plus (f w) (real_mult eps gibbsd_half))
                          (real_plus (real_list_sum X f l)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (f w) (real_list_sum X f l))
                          (real_plus (real_mult eps gibbsd_half)
                                     (real_mult eps gibbsd_half)))
               (real_plus (real_plus (f w) (real_list_sum X f l)) eps)
               (real_plus_swap_mid (f w) (real_mult eps gibbsd_half)
                                   (real_list_sum X f l)
                                   (real_mult eps gibbsd_half))
               (RealSetoid.real_eq_plus_compat
                  (real_plus (f w) (real_list_sum X f l))
                  (real_plus (real_mult eps gibbsd_half)
                             (real_mult eps gibbsd_half))
                  (real_plus (f w) (real_list_sum X f l))
                  eps
                  (real_eq_refl (real_plus (f w) (real_list_sum X f l)))
                  (gibbsd_half_sum eps))).
    + exact (real_lt_plus_compat _ _ _ _ Ha Ht).
Qed.

(* A-3：分解位载体非空证（pos 接口槽用；前缀两案 discriminate） *)
Lemma t34_app_cons_nonnil : forall (X : Type) (l1 : list X) (s0 : X) (l2 : list X),
  app l1 (cons s0 l2) <> nil.
Proof.
  intros X l1 s0 l2 H. destruct l1.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
Qed.

(* A-4【主新件·和零⟹位零提取】：载体取分解形 app l1 (cons s0 l2)，     *)
(*   逐项 0 ≤_B + 折叠 ≡ 0 ⟹ 指定位 s0 项 ≡ 0。                         *)
(*   前缀归纳：nil 支二项钳零（clamp_head）；cons 支钳尾（clamp_head_r） *)
(*   + 归纳。受判定界说明：Bishop ≤_B（UpRealLeB）档构造性可达；         *)
(*   「全位 Or 形精确提取」才触三分判定界——本件为 ≤_B 档最强形。         *)
Lemma t34_list_sum_zero_extract : forall (X : Type) (f : X -> Real)
    (l1 : list X) (s0 : X) (l2 : list X),
  (forall w : X, real_le_b real_zero (f w)) ->
  real_eq (real_list_sum X f (app l1 (cons s0 l2))) real_zero ->
  real_eq real_zero (f s0).
Proof.
  intros X f l1.
  induction l1 as [| w l1 IH]; intros s0 l2 Hpt Hsum.
  - (* 前缀空：app nil 归约（change 换形，免 simpl delta 变动）；
       二项钳零取首项（展开形靠 exact 换向检查完成） *)
    change (real_eq (real_list_sum X f (cons s0 l2)) real_zero) in Hsum.
    exact (gibbe2_clamp_head (f s0) (real_list_sum X f l2)
             (Hpt s0)
             (t34_list_sum_le_b_nonneg X f l2 Hpt)
             Hsum).
  - (* 前缀非空：app cons 归约 + 二项钳零取尾和，归纳推进入前缀余部 *)
    change (real_eq
              (real_plus (f w) (real_list_sum X f (app l1 (cons s0 l2))))
              real_zero) in Hsum.
    assert (Htail : real_eq (real_list_sum X f (app l1 (cons s0 l2))) real_zero).
    { apply (real_eq_sym real_zero
               (real_list_sum X f (app l1 (cons s0 l2)))).
      exact (gibbe2_clamp_head_r (f w)
               (real_list_sum X f (app l1 (cons s0 l2)))
               (Hpt w)
               (t34_list_sum_le_b_nonneg X f (app l1 (cons s0 l2)) Hpt)
               Hsum). }
    exact (IH s0 l2 Hpt Htail).
Qed.

(* ============================================================ *)
(* Part B：通用 list 逐点提取主件（t34_gibbs_equality_list）             *)
(*   gibbe2_gibbs_equality_bool（G08，bool 两态样板）的通用 list         *)
(*   分解位推广：双归一化 + Σ kl_term ≡ 0 ⟹ 指定位 p s0 ≡ q s0。         *)
(*   链见头注「逐项 kl_term 消去链」五步。                               *)
(* ============================================================ *)
Theorem t34_gibbs_equality_list :
  forall (X : Type) (p q : X -> Real)
    (Hp : forall s : X, real_lt real_zero (p s))
    (Hq : forall s : X, real_lt real_zero (q s))
    (l1 : list X) (s0 : X) (l2 : list X)
    (Hnp : real_eq (real_list_sum X p (app l1 (cons s0 l2))) real_one)
    (Hnq : real_eq (real_list_sum X q (app l1 (cons s0 l2))) real_one),
    real_eq (real_list_sum X
               (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
               (app l1 (cons s0 l2)))
            real_zero ->
    real_eq (p s0) (q s0).
Proof.
  intros X p q Hp Hq l1 s0 l2 Hnp Hnq Hkl.
  (* 步 1：Σ(p−q) ≡ 0（gibbsd_list_sum_minus + 双归一化 + plus_opp） *)
  assert (HsumG : real_eq
           (real_list_sum X
              (fun s : X => real_plus (p s) (real_opp (q s)))
              (app l1 (cons s0 l2)))
           real_zero).
  { apply (real_eq_trans
             (real_list_sum X
                (fun s : X => real_plus (p s) (real_opp (q s)))
                (app l1 (cons s0 l2)))
             (real_plus (real_list_sum X p (app l1 (cons s0 l2)))
                        (real_opp (real_list_sum X q (app l1 (cons s0 l2)))))
             real_zero).
    - exact (gibbsd_list_sum_minus X p q (app l1 (cons s0 l2))).
    - apply (real_eq_trans
               (real_plus (real_list_sum X p (app l1 (cons s0 l2)))
                          (real_opp (real_list_sum X q (app l1 (cons s0 l2)))))
               (real_plus real_one (real_opp real_one))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum X p (app l1 (cons s0 l2)))
                 (real_opp (real_list_sum X q (app l1 (cons s0 l2))))
                 real_one
                 (real_opp real_one)
                 Hnp
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum X q (app l1 (cons s0 l2)))
                    real_one Hnq)).
      + exact (real_plus_opp real_one). }
  (* 步 2：Σ(kl + −(p−q)) ≡ 0（add 分和 + opp 换载 + 双零支） *)
  assert (HsumD : real_eq
           (real_list_sum X
              (fun s : X => real_plus
                 (real_kl_term (p s) (q s) (Hp s) (Hq s))
                 (real_opp (real_plus (p s) (real_opp (q s)))))
              (app l1 (cons s0 l2)))
           real_zero).
  { apply (real_eq_trans
             (real_list_sum X
                (fun s : X => real_plus
                   (real_kl_term (p s) (q s) (Hp s) (Hq s))
                   (real_opp (real_plus (p s) (real_opp (q s)))))
                (app l1 (cons s0 l2)))
             (real_plus
                (real_list_sum X
                   (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                   (app l1 (cons s0 l2)))
                (real_opp
                   (real_list_sum X
                      (fun s : X => real_plus (p s) (real_opp (q s)))
                      (app l1 (cons s0 l2)))))
             real_zero).
    - apply (real_eq_trans
               (real_list_sum X
                  (fun s : X => real_plus
                     (real_kl_term (p s) (q s) (Hp s) (Hq s))
                     (real_opp (real_plus (p s) (real_opp (q s)))))
                  (app l1 (cons s0 l2)))
               (real_plus
                  (real_list_sum X
                     (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                     (app l1 (cons s0 l2)))
                  (real_list_sum X
                     (fun s : X => real_opp (real_plus (p s) (real_opp (q s))))
                     (app l1 (cons s0 l2))))
               (real_plus
                  (real_list_sum X
                     (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                     (app l1 (cons s0 l2)))
                  (real_opp
                     (real_list_sum X
                        (fun s : X => real_plus (p s) (real_opp (q s)))
                        (app l1 (cons s0 l2)))))).
      + exact (real_list_sum_add X
                 (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                 (fun s : X => real_opp (real_plus (p s) (real_opp (q s))))
                 (app l1 (cons s0 l2))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (app l1 (cons s0 l2)))
                 (real_list_sum X
                    (fun s : X => real_opp (real_plus (p s) (real_opp (q s))))
                    (app l1 (cons s0 l2)))
                 (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (app l1 (cons s0 l2)))
                 (real_opp
                    (real_list_sum X
                       (fun s : X => real_plus (p s) (real_opp (q s)))
                       (app l1 (cons s0 l2))))
                 (real_eq_refl
                    (real_list_sum X
                       (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                       (app l1 (cons s0 l2))))
                 (real_list_sum_opp X
                    (fun s : X => real_plus (p s) (real_opp (q s)))
                    (app l1 (cons s0 l2)))).
    - apply (real_eq_trans
               (real_plus
                  (real_list_sum X
                     (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                     (app l1 (cons s0 l2)))
                  (real_opp
                     (real_list_sum X
                        (fun s : X => real_plus (p s) (real_opp (q s)))
                        (app l1 (cons s0 l2)))))
               (real_plus real_zero (real_opp real_zero))
               real_zero).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum X
                    (fun s : X => real_kl_term (p s) (q s) (Hp s) (Hq s))
                    (app l1 (cons s0 l2)))
                 (real_opp
                    (real_list_sum X
                       (fun s : X => real_plus (p s) (real_opp (q s)))
                       (app l1 (cons s0 l2))))
                 real_zero
                 (real_opp real_zero)
                 Hkl
                 (RealSetoid.real_eq_opp_compat
                    (real_list_sum X
                       (fun s : X => real_plus (p s) (real_opp (q s)))
                       (app l1 (cons s0 l2)))
                    real_zero HsumG)).
      + apply (real_eq_trans
                 (real_plus real_zero (real_opp real_zero))
                 (real_plus real_zero real_zero)
                 real_zero).
        * apply (RealSetoid.real_eq_plus_compat real_zero
                    (real_opp real_zero) real_zero real_zero
                    (real_eq_refl real_zero) (real_opp_zero)).
        * exact (real_plus_zero real_zero). }
  (* 步 3：逐点 0 ≤_B kl + −(p−q)（D0 切线槽 + B3 差正） *)
  assert (HptD : forall s : X,
           real_le_b real_zero
             (real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                        (real_opp (real_plus (p s) (real_opp (q s)))))).
  { intro s.
    exact (gibbe2_le_b_nonneg_diff
             (real_plus (p s) (real_opp (q s)))
             (real_kl_term (p s) (q s) (Hp s) (Hq s))
             (gibbsd_gibbs_pointwise_B X p q s (Hp s) (Hq s))). }
  (* 步 4：分解位提取（A-4 主新件）⟹ s0 位 D ≡ 0 *)
  assert (Hclamp0 : real_eq real_zero
           (real_plus (real_kl_term (p s0) (q s0) (Hp s0) (Hq s0))
                      (real_opp (real_plus (p s0) (real_opp (q s0)))))).
  { exact (t34_list_sum_zero_extract X
             (fun s : X => real_plus
                (real_kl_term (p s) (q s) (Hp s) (Hq s))
                (real_opp (real_plus (p s) (real_opp (q s)))))
             l1 s0 l2 HptD HsumD). }
  (* 步 5：kl ≡ p−q（D0）⟹ 切点（D1）⟹ 注入（T1）⟹ p ≡ q *)
  assert (HkG : real_eq (real_kl_term (p s0) (q s0) (Hp s0) (Hq s0))
                        (real_plus (p s0) (real_opp (q s0)))).
  { exact (gibbe2_kl_eq_of_w_zero (p s0) (q s0) (Hp s0) (Hq s0)
             (real_eq_sym _ _ Hclamp0)). }
  assert (Htan : real_eq
           (real_log
              (real_mult (q s0) (real_inv_pos (p s0) (Hp s0)))
              (real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0))
                 (Hq s0) (real_inv_pos_pos (p s0) (Hp s0))))
           (real_plus
              (real_mult (q s0) (real_inv_pos (p s0) (Hp s0)))
              (real_opp real_one))).
  { exact (gibbe2_tangent_eq (p s0) (q s0) (Hp s0) (Hq s0) HkG). }
  assert (Hu1 : real_eq
           (real_mult (q s0) (real_inv_pos (p s0) (Hp s0))) real_one).
  { exact (t1_log_eq_linear_inject
             (real_mult (q s0) (real_inv_pos (p s0) (Hp s0)))
             (real_mult_positive (q s0) (real_inv_pos (p s0) (Hp s0))
                (Hq s0) (real_inv_pos_pos (p s0) (Hp s0)))
             Htan). }
  apply (real_eq_trans (p s0)
           (real_mult (p s0) (real_mult (q s0) (real_inv_pos (p s0) (Hp s0))))
           (q s0)).
  - apply (real_eq_trans (p s0) (real_mult (p s0) real_one)
             (real_mult (p s0) (real_mult (q s0) (real_inv_pos (p s0) (Hp s0))))).
    + apply (real_eq_sym (real_mult (p s0) real_one) (p s0)
               (real_mult_one (p s0))).
    + apply (RealSetoid.real_eq_mult_compat (p s0) real_one (p s0)
               (real_mult (q s0) (real_inv_pos (p s0) (Hp s0)))
               (real_eq_refl (p s0))
               (real_eq_sym (real_mult (q s0) (real_inv_pos (p s0) (Hp s0)))
                  real_one Hu1)).
  - exact (gibbsd_p_mult_ratio (p s0) (q s0) (Hp s0)).
Qed.

(* ============================================================ *)
(* Part C：节 ListTempDual——通用 list 载体装配                          *)
(*   载体 = app l1 (cons s0 l2) 分解形（T1 Part D 同形先例）；求和面    *)
(*   四接口 + 单调扩容位全由 S08 real_list_sum 族即插即用供给。          *)
(* ============================================================ *)
Section ListTempDual.

Variable X : Type.
Variable l1 : list X.
Variable s0 : X.
Variable l2 : list X.
Variable T0 : Real.
Variable T0_pos : real_lt real_zero T0.
Variable e0 : X -> Real.

(* 求和面与五接口（S08 real_list_sum 族全 arity 供给） *)
Let Lst : list X := app l1 (cons s0 l2).
Let lsumf : (X -> Real) -> Real := fun f : X -> Real => real_list_sum X f Lst.
Let lpos : forall f : X -> Real,
    (forall w : X, real_lt real_zero (f w)) -> real_lt real_zero (lsumf f) :=
  fun (f : X -> Real) (Hf : forall w : X, real_lt real_zero (f w)) =>
    real_list_sum_pos X f Lst Hf (t34_app_cons_nonnil X l1 s0 l2).
Let lext : forall (f g : X -> Real),
    (forall w : X, real_eq (f w) (g w)) -> real_eq (lsumf f) (lsumf g) :=
  fun (f g : X -> Real) (Hfg : forall w : X, real_eq (f w) (g w)) =>
    real_list_sum_ext X f g Lst Hfg.
Let lle : forall (f g : X -> Real),
    (forall w : X, real_le (f w) (g w)) -> real_le (lsumf f) (lsumf g) :=
  fun (f g : X -> Real) (Hfg : forall w : X, real_le (f w) (g w)) =>
    real_list_sum_le X f g Lst Hfg.
Let llinear : forall (a : Real) (f : X -> Real),
    real_eq (lsumf (fun w : X => real_mult a (f w)))
            (real_mult a (lsumf f)) :=
  fun (a : Real) (f : X -> Real) => real_list_sum_linear X a f Lst.
Let ladd : forall (f g : X -> Real),
    real_eq (lsumf (fun w : X => real_plus (f w) (g w)))
            (real_plus (lsumf f) (lsumf g)) :=
  fun (f g : X -> Real) => real_list_sum_add X f g Lst.

(* 温度族全 arity 实例（T6 件显式应用） *)
Let bB : X -> Real := real_boltzmann_dist_temp X lsumf lpos T0 T0_pos e0.
Let bBpos : forall w : X, real_lt real_zero (bB w) :=
  real_boltzmann_dist_temp_pos X lsumf lpos T0 T0_pos e0.
Let bE_T : Real := real_energy_exp_temp X lsumf lpos T0 T0_pos e0.
Let lH (q : X -> Real) (Hq : forall w : X, real_lt real_zero (q w)) : Real :=
  real_entropy_dist X lsumf q Hq.
Let lKL (p : X -> Real) (Hp : forall w : X, real_lt real_zero (p w)) : Real :=
  real_KL_temp X lsumf lpos T0 T0_pos e0 p Hp.
Let lEen (q : X -> Real) : Real :=
  lsumf (fun w : X => real_mult (q w) (e0 w)).

Let bBnorm : real_eq (lsumf bB) real_one :=
  real_boltzmann_dist_temp_normalized X lsumf lpos lext llinear T0 T0_pos e0.

(* ---------------------------------------------------------- *)

(*   的 4.6d 档）：熵等 + 同能量 + 归一化 ⟹ 指定位 p s0 ≡ p_T s0。      *)
(*   链 = 辅助引理 t13_entropy_eq_kl_zero（熵亏件反向 ⟹ KL≡0）+ 熵亏桥换载           *)
(*   Σ kl_term ≡ 0 + Part B 逐项 kl_term 消去完成。                      *)
(* ---------------------------------------------------------- *)
Lemma t34_entropy_eq_pointwise_list :
  forall (p : X -> Real) (Hp : forall w : X, real_lt real_zero (p w)),
    real_eq (lsumf p) real_one ->
    real_eq (lEen p) bE_T ->
    real_eq (lH p Hp) (lH bB bBpos) ->
    real_eq (p s0) (bB s0).
Proof.
  intros p Hp Hnp Henergy Hent.
  apply (t34_gibbs_equality_list X p bB Hp bBpos l1 s0 l2 Hnp bBnorm).
  apply (real_eq_trans
           (lsumf (fun w : X => real_kl_term (p w) (bB w) (Hp w) (bBpos w)))
           (lKL p Hp)
           real_zero).
  - exact (real_eq_sym
             (real_KL_temp X lsumf lpos T0 T0_pos e0 p Hp)
             (lsumf (fun w : X => real_kl_term (p w) (bB w) (Hp w) (bBpos w)))
             (real_KL_temp_kl_term_bridge X lsumf lpos lext T0 T0_pos e0 p Hp)).
  - exact (t13_entropy_eq_kl_zero X lsumf lpos lext llinear ladd
             T0 T0_pos e0 p Hp Hnp Henergy Hent).
Qed.

(* ---------------------------------------------------------- *)
(* 支4 实例（最优支·逐 eps 档零接口前提）：熵上界件五步链内联      *)
(*   重演（熵亏件+KL 件两见证+负消去闭合），零整件转发。                  *)
(* ---------------------------------------------------------- *)
Lemma t34_list_max_entropy_le_eps :
  forall (p : X -> Real) (Hp : forall w : X, real_lt real_zero (p w)),
    real_eq (lsumf p) real_one ->
    real_eq (lEen p) bE_T ->
    forall eps : Real, real_lt real_zero eps ->
    real_le (lH p Hp) (real_plus (lH bB bBpos) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  (* 段一：熵亏温度版全 arity 十三参显式（T6b 件）：S_{p_T} − S_p ≡ KL_p *)
  assert (Hdef : real_eq (real_minus_r (lH bB bBpos) (lH p Hp)) (lKL p Hp)).
  { exact (real_entropy_deficit_kl_temp X lsumf lpos lext llinear ladd
             T0 T0_pos e0 p Hp Hnp Henergy). }
  assert (Hkl : real_le real_zero (real_plus (lKL p Hp) eps)).
  { exact (real_KL_temp_ge_zero_eps X lsumf lpos lext lle llinear ladd
             T0 T0_pos e0 p Hp Hnp eps Heps). }
  (* 段三：KL 换形到熵亏支（real_le_id_r + eq_plus_compat_adapt 对角） *)
  assert (Hstep : real_le real_zero
           (real_plus (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps)).
  { apply (RealSetoid.real_le_id_r real_zero (real_plus (lKL p Hp) eps)
             (real_plus (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps)
             (RealSetoid.real_eq_plus_compat_adapt (lKL p Hp)
                (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps eps
                (real_eq_sym (real_plus (lH bB bBpos) (real_opp (lH p Hp)))
                             (lKL p Hp) Hdef)
                (real_eq_refl eps))).
    exact Hkl. }
  (* 段四：非负加法支（辅助引理 real_le_plus_nonneg_r） *)
  assert (H1 : real_le (lH p Hp)
           (real_plus (lH p Hp)
              (real_plus (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps))).
  { exact (real_le_plus_nonneg_r (lH p Hp)
             (real_plus (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps)
             Hstep). }
  (* 段五：负消去换形闭合（辅助引理 real_plus_neg_cancel_shift_eps） *)
  exact (RealSetoid.real_le_id_r (lH p Hp)
           (real_plus (lH p Hp)
              (real_plus (real_plus (lH bB bBpos) (real_opp (lH p Hp))) eps))
           (real_plus (lH bB bBpos) eps)
           (real_plus_neg_cancel_shift_eps (lH p Hp) (lH bB bBpos) eps)
           H1).
Qed.

(* ---------------------------------------------------------- *)
(* 装配件：temp_energy_dual_closed_list（通用 list 载体五合取支 sigT 形）*)
(*   支1 归一化 + 支2 正性（sigT 第二见证位）+ 支3 约束（定义性收敛）   *)
(*   + 支4 最优（逐 eps 档，零接口前提）+ 支5 唯一（分解位档）全闭。    *)
(* ---------------------------------------------------------- *)
Theorem temp_energy_dual_closed_list :
  sigT (fun pb : X -> Real =>
    sigT (fun Hpb : forall w : X, real_lt real_zero (pb w) =>
      prod (real_eq (lsumf pb) real_one)
        (prod (real_eq (lEen pb) bE_T)
          (prod (forall (p : X -> Real) (Hp : forall w : X, real_lt real_zero (p w)),
                  real_eq (lsumf p) real_one ->
                  real_eq (lEen p) bE_T ->
                  forall eps : Real, real_lt real_zero eps ->
                  real_le (lH p Hp) (real_plus (lH pb Hpb) eps))
                (forall (p : X -> Real) (Hp : forall w : X, real_lt real_zero (p w)),
                  real_eq (lsumf p) real_one ->
                  real_eq (lEen p) bE_T ->
                  real_eq (lH p Hp) (lH pb Hpb) ->
                  real_eq (p s0) (pb s0)))))).
Proof.
  exists bB. exists bBpos.
  split.
  - exact bBnorm.
  - split.
    + exact (real_eq_refl (lEen bB)).
    + split.
      * intros p Hp Hnp Henergy eps Heps.
        exact (t34_list_max_entropy_le_eps p Hp Hnp Henergy eps Heps).
      * intros p Hp Hnp Henergy HeqH.
        exact (t34_entropy_eq_pointwise_list p Hp Hnp Henergy HeqH).
Qed.

End ListTempDual.

(* ============================================================ *)
(* 尾核：提取检验（零公理见证） *)
(* ============================================================ *)
Print Assumptions t34_list_sum_const_zero.
Print Assumptions t34_list_sum_le_b_nonneg.
Print Assumptions t34_app_cons_nonnil.
Print Assumptions t34_list_sum_zero_extract.
Print Assumptions t34_gibbs_equality_list.
Print Assumptions t34_entropy_eq_pointwise_list.
Print Assumptions t34_list_max_entropy_le_eps.
Print Assumptions temp_energy_dual_closed_list.
