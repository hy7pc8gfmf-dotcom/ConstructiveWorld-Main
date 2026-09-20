(* ============================================================ *)
(* UpAblTwLeFeed.v —— tw_h_le 两点核差界的形式供给件                     *)
(*                                                                *)
(* 【使命】为 UpTempWindow 的 Section TempWindow 接口语句 tw_h_le         *)
(*   （逐点绝对值界 |w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)·(1/N)，节卸载后      *)
(*   外形）供给独立证明：语句与接口语句逐字对齐（世界接口                 *)
(*   Tok/states/states_nonempty/zz/Delta/Delta_pos 逐字同位），           *)
(*   外层谓词取 Bishop B 形（real_le_b，UpRealLeB 中可达的最强形）。      *)
(*                                                                *)
(* 【形态差异注记（三条）】                                               *)
(*   ① 三角不等式路线的余量差：两点核差三角不等式                         *)
(*     uabS4_abs_diff_triangle_le_B 经中点 m=E2L·u 在窗口三点上实例化     *)
(*     （本件转换层 ntl_tw_diff_tri_*），给出 |w−u| ≤ |w−m|+|m−u| ≤       *)
(*     (E2−2·E2L+1)·u，较接口语句的锐界 (E2−1)·u 多出                     *)
(*     2·(1−E2L)·u ≥ 0（E2L ≤ 1）——锐界不可经单次三角不等式直达，        *)
(*     故锐界主件改走「绝对值两支重组＋右吸收正余量」路线。                *)
(*   ② B 形与 plain 形：接口语句实形为 plain Or 编码序                     *)
(*     （real_le = Or(lt,eq)）；主件 A 取 B 形（real_le_b，Set 层         *)
(*     forall 型）。plain⟹B 单向转换引理 real_le_to_le_b 在库；           *)
(*     B⟹plain 方向按本库形态 doctrine 不可达（实数层构造序的形态         *)
(*     边界）。故主件 A 交付 B 形，plain 形由 ntl_tw_h_le_feed 以         *)
(*     两支重组独立供给（tw_abs_le 内构 Or 分支），不调用语句本体。        *)
(*   ③ 前提同位：两支路线与语句本体同需 Delta_pos（负分支                  *)
(*     「1−E2L ≤ E2−1」步经 tw_u2_pos 实例化，正性证书同源）——            *)
(*     主件两件逐字保留接口全形（Delta_pos 在场且被使用），如实注记：      *)
(*     接口无增无减，差异仅在外层谓词与证明路线。                          *)
(* 【供给关系注记】主件 B 形两支均经 uabS4_le_add_r 右吸收 eps——该引理被   *)
(*   实质使用（非平凡）；转换层三角实例为逐字实例化（见形态差异①）。       *)
(*                                                                *)
(* 【依赖】CW_ConstructiveWorld_219＋UpRealLeB＋S08_RealMainlineDPO＋     *)
(*   UpTempWindow（接口语句源）＋UpAblAbsSumLeB（三角与右吸收供给源）。    *)
(*   本件不触碰任何既有文件；不入 order.txt/_CoqProject。                 *)
(* 【对标】数学原型：温度窗口下逐点分布对均匀分布的指数逼近界；            *)
(*   mathlib/stdlib 无直接构造对应物。                                   *)
(* 【构造性注记】零承认词面、无节内假设声明、无经典逻辑、全件 Qed 闭合；   *)
(*   语句全 Set 层值；证明全构造，语句面无裸命题层。                       *)
(* 【编译配方】Rocq 9.1 直调 coqc 编译（不带 -Q 包映射），cpu_guard 包裹   *)
(*   限载；输出一律 -o 临时目录，树内 .vo 不重写，信任缓存分毫不动。       *)
(*                                                                *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpTempWindow.
Require Import UpAblAbsSumLeB.

(* ============================================================ *)
(* Part 0 · 签名核验（依赖签名漂移即编译报错）                          *)
(* ============================================================ *)

Check tw_h_le.                   (* 接口语句实形（节卸载后） *)
Check tw_unif_dist.              (* 1/N（卸载后三参） *)
Check tw_wT.                     (* 窗口权重（卸载后七参） *)
Check tw_E2.                     (* e^{2Δ/T}（Delta 首参） *)
Check tw_E2L.                    (* e^{−2Δ/T} *)
Check uabS4_le_add_r.            (* 正余量右吸收（主件使用） *)
Check uabS4_abs_diff_triangle_le_eps. (* 两点核差三角不等式（逐 eps 形，转换层用） *)
Check uabS4_abs_diff_triangle_le_B.   (* 两点核差三角不等式（B 形，转换层用） *)
Check real_le_closure_b_one.     (* B 形单步闭包引理 *)
Check real_le_to_le_b.           (* plain⟹B 单向转换引理 *)
Check tw_abs_le.                 (* |x| ≤ c 两支组合器 *)
Check tw_ring_sub_mult.          (* x·y + −y == (x + −1)·y *)
Check tw_ring_sub_mult_l.        (* y + −(x·y) == (1 + −x)·y *)
Check tw_wT_le_E2invN.           (* 正分支源：w ≤ E2·(1/N) *)
Check tw_E2LinvN_le_wT.          (* 负分支源：E2L·(1/N) ≤ w *)
Check tw_one_minus_exp_le.       (* 1−e^{−E} ≤ e^{E}−1 *)
Check real_le_plus_compat.       (* 加法保序 *)
Check real_le_mult_compat.       (* 正系数乘法保序 *)
Check real_le_trans.             (* 序传递 *)
Check real_opp_plus.             (* −(a+b) == −a + −b *)
Check real_opp_opp.              (* −(−x) == x *)
Check real_plus_comm.            (* 交换 *)
Check real_inv_pos_pos.          (* inv 正性 *)
Check real_minus_r.              (* a−b := a + −b *)

(* ============================================================ *)
(* Part 1 · 转换层：两点核差三角不等式的窗口三点实例                    *)
(*   三点实例化：a := w_T(x)、b := E2L·(1/N)、c := 1/N。               *)
(*   余量差见头注形态差异①：本层两件较接口语句的锐界更宽。             *)
(* ============================================================ *)

Corollary ntl_tw_diff_tri_B : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_plus
       (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                  (real_mult (tw_E2L Delta T Ht)
                             (tw_unif_dist Tok states states_nonempty))))
       (real_abs (real_minus_r
                    (real_mult (tw_E2L Delta T Ht)
                               (tw_unif_dist Tok states states_nonempty))
                    (tw_unif_dist Tok states states_nonempty)))).
Proof.
  intros Tok states states_nonempty zz Delta T Ht x.
  exact (uabS4_abs_diff_triangle_le_B
           (tw_wT Tok states states_nonempty zz T Ht x)
           (real_mult (tw_E2L Delta T Ht)
                      (tw_unif_dist Tok states states_nonempty))
           (tw_unif_dist Tok states states_nonempty)).
Qed.

Corollary ntl_tw_diff_tri_eps : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok) (e : Real),
  real_lt real_zero e ->
  real_le
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_plus
       (real_plus
          (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                     (real_mult (tw_E2L Delta T Ht)
                                (tw_unif_dist Tok states states_nonempty))))
          (real_abs (real_minus_r
                       (real_mult (tw_E2L Delta T Ht)
                                  (tw_unif_dist Tok states states_nonempty))
                       (tw_unif_dist Tok states states_nonempty))))
       e).
Proof.
  intros Tok states states_nonempty zz Delta T Ht x e He.
  exact (uabS4_abs_diff_triangle_le_eps
           (tw_wT Tok states states_nonempty zz T Ht x)
           (real_mult (tw_E2L Delta T Ht)
                      (tw_unif_dist Tok states states_nonempty))
           (tw_unif_dist Tok states states_nonempty) e He).
Qed.

(* ============================================================ *)
(* Part 2 · 两支基件：接口语句锐界的两支（B 形主件与 plain 形供给件共用）*)
(*   正分支：w − (1/N) ≤ (E2 − 1)·(1/N)——tw_wT_le_E2invN ＋ 加法保序   *)
(*         ＋ tw_ring_sub_mult 换形。                                   *)
(*   负分支：−(w − (1/N)) ≤ (E2 − 1)·(1/N)——tw_E2LinvN_le_wT 经负号    *)
(*         翻转得 u−w ≤ u−E2L·u ≡ (1−E2L)·u ≤ (E2−1)·u                  *)
(*         （tw_one_minus_exp_le 实例）。                                *)
(* ============================================================ *)

Lemma ntl_tw_arm_upper : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                  (tw_unif_dist Tok states states_nonempty))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta Hlo Hhi T Ht x.
  apply (tw_le_eq_r
           (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                         (tw_unif_dist Tok states states_nonempty))
           (real_minus_r (real_mult (tw_E2 Delta T Ht)
                                    (tw_unif_dist Tok states states_nonempty))
                         (tw_unif_dist Tok states states_nonempty))
           (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                      (tw_unif_dist Tok states states_nonempty))).
  - apply (real_le_plus_compat
             (tw_wT Tok states states_nonempty zz T Ht x)
             (real_mult (tw_E2 Delta T Ht)
                        (tw_unif_dist Tok states states_nonempty))
             (real_opp (tw_unif_dist Tok states states_nonempty))
             (real_opp (tw_unif_dist Tok states states_nonempty))).
    + exact (tw_wT_le_E2invN Tok states states_nonempty zz Delta Hlo Hhi T Ht x).
    + apply real_le_refl.
  - exact (tw_ring_sub_mult (tw_E2 Delta T Ht)
                            (tw_unif_dist Tok states states_nonempty)).
Qed.

Lemma ntl_tw_arm_lower : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  assert (HinvN : real_lt real_zero (tw_unif_dist Tok states states_nonempty))
    by (unfold tw_unif_dist; apply real_inv_pos_pos).
  (* 步1：u − w ≤ u − E2L·u（负号翻转负分支源） *)
  assert (Hstep1 : real_le
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty)))).
  { apply (real_le_plus_compat
             (tw_unif_dist Tok states states_nonempty)
             (tw_unif_dist Tok states states_nonempty)
             (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
             (real_opp (real_mult (tw_E2L Delta T Ht)
                                  (tw_unif_dist Tok states states_nonempty)))).
    - apply real_le_refl.
    - apply (tw_le_opp_compat
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty))
               (tw_wT Tok states states_nonempty zz T Ht x)).
      exact (tw_E2LinvN_le_wT Tok states states_nonempty zz Delta Hlo Hhi T Ht x). }
  (* 步2：u − E2L·u ≡ (1−E2L)·u（换形） *)
  assert (Hreshape : real_eq
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
               (real_mult (tw_E2L Delta T Ht)
                          (tw_unif_dist Tok states states_nonempty)))
            (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                       (tw_unif_dist Tok states states_nonempty)))
    by exact (tw_ring_sub_mult_l (tw_E2L Delta T Ht)
                                 (tw_unif_dist Tok states states_nonempty)).
  (* 步3：(1−E2L)·u ≤ (E2−1)·u（1−e^{−E} ≤ e^{E}−1 实例） *)
  assert (Hstep2 : real_le
            (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                       (tw_unif_dist Tok states states_nonempty))
            (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                       (tw_unif_dist Tok states states_nonempty)))
    by exact (real_le_mult_compat
                (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                (tw_unif_dist Tok states states_nonempty) HinvN
                (tw_one_minus_exp_le (tw_u2 Delta T Ht)
                                     (tw_u2_pos Delta HDelta T Ht))).
  (* 核心链：u − w ≤ (E2−1)·u *)
  assert (Hcore : real_le
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                       (tw_unif_dist Tok states states_nonempty))).
  { apply (real_le_trans
             (real_minus_r (tw_unif_dist Tok states states_nonempty)
                           (tw_wT Tok states states_nonempty zz T Ht x))
             (real_minus_r (tw_unif_dist Tok states states_nonempty)
                (real_mult (tw_E2L Delta T Ht)
                           (tw_unif_dist Tok states states_nonempty)))
             (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                        (tw_unif_dist Tok states states_nonempty))).
    - exact Hstep1.
    - apply (real_le_trans
               (real_minus_r (tw_unif_dist Tok states states_nonempty)
                  (real_mult (tw_E2L Delta T Ht)
                             (tw_unif_dist Tok states states_nonempty)))
               (real_mult (real_plus real_one (real_opp (tw_E2L Delta T Ht)))
                          (tw_unif_dist Tok states states_nonempty))
               (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                          (tw_unif_dist Tok states states_nonempty))).
      + exact (inr Hreshape).
      + exact Hstep2. }
  (* 对称换形：u − w ≡ −(w − u)（opp_plus ＋ opp_opp ＋ comm 三步） *)
  assert (Hsym : real_eq
            (real_minus_r (tw_unif_dist Tok states states_nonempty)
                          (tw_wT Tok states states_nonempty zz T Ht x))
            (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                                    (tw_unif_dist Tok states states_nonempty)))).
  { eapply real_eq_trans.
    - apply real_plus_comm.
    - apply real_eq_sym.
      eapply real_eq_trans.
      + apply real_opp_plus.
      + apply (RealSetoid.real_eq_plus_compat
                 (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
                 (real_opp (real_opp (tw_unif_dist Tok states states_nonempty)))
                 (real_opp (tw_wT Tok states states_nonempty zz T Ht x))
                 (tw_unif_dist Tok states states_nonempty)).
        * apply real_eq_refl.
        * apply real_opp_opp. }
  (* 合成：tw_le_eq_l（le a b ＋ eq a c ⟹ le c b） *)
  exact (tw_le_eq_l
           (real_minus_r (tw_unif_dist Tok states states_nonempty)
                         (tw_wT Tok states states_nonempty zz T Ht x))
           (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
                      (tw_unif_dist Tok states states_nonempty))
           (real_opp (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                                   (tw_unif_dist Tok states states_nonempty)))
           Hcore Hsym).
Qed.

(* ============================================================ *)
(* Part 3 · 主件 A：接口语句锐界的 B 形供给（可达最强形）                *)
(*   语句：接口语句实形（UpTempWindow 节卸载后）外层谓词取 real_le_b，   *)
(*   其余逐字同位。证明：real_le_closure_b_one 单步收拢 ＋ 两支经        *)
(*   经 uabS4_le_add_r 右吸收正余量 eps。                               *)
(* ============================================================ *)

Corollary ntl_tw_h_le_b_feed : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  apply real_le_closure_b_one. intros e He.
  apply tw_abs_le.
  - exact (uabS4_le_add_r _ _ _
             (ntl_tw_arm_upper Tok states states_nonempty zz Delta Hlo Hhi T Ht x)
             He).
  - exact (uabS4_le_add_r _ _ _
             (ntl_tw_arm_lower Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x)
             He).
Qed.

(* ============================================================ *)
(* Part 4 · 主件 B：plain 形供给件（语句与接口语句实形逐字对齐）         *)
(*   语句＝tw_h_le 节卸载后外形逐字（世界接口同位同序）；证明＝两支      *)
(*   重组（tw_abs_le 内构 Or 分支），不调用语句本体（独立重建，          *)
(*   与语句本体结论内容等价——如实注记：本件为该界的 plain 形供给）。    *)
(* ============================================================ *)

Corollary ntl_tw_h_le_feed : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  apply tw_abs_le.
  - exact (ntl_tw_arm_upper Tok states states_nonempty zz Delta Hlo Hhi T Ht x).
  - exact (ntl_tw_arm_lower Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x).
Qed.

(* 转换演示：plain 形供给件经单向转换引理得 B 形＝主件 A 同语句          *)
Corollary ntl_tw_h_le_feed_to_b : forall (Tok : Set) (states : list Tok)
  (states_nonempty : Not (Id states nil)) (zz : Tok -> Real) (Delta : Real)
  (HDelta : real_lt real_zero Delta)
  (Hlo : forall x : Tok, real_le (real_opp Delta) (zz x))
  (Hhi : forall x : Tok, real_le (zz x) Delta)
  (T : Real) (Ht : real_lt real_zero T) (x : Tok),
  real_le_b
    (real_abs (real_minus_r (tw_wT Tok states states_nonempty zz T Ht x)
                            (tw_unif_dist Tok states states_nonempty)))
    (real_mult (real_plus (tw_E2 Delta T Ht) (real_opp real_one))
               (tw_unif_dist Tok states states_nonempty)).
Proof.
  intros Tok states states_nonempty zz Delta HDelta Hlo Hhi T Ht x.
  exact (real_le_to_le_b _ _
           (ntl_tw_h_le_feed Tok states states_nonempty zz Delta
                             HDelta Hlo Hhi T Ht x)).
Qed.

(* ============================================================ *)
(* 假设审计：全件 Closed（零外部未证假设）                               *)
(* ============================================================ *)

Print Assumptions ntl_tw_diff_tri_eps.
Print Assumptions ntl_tw_diff_tri_B.
Print Assumptions ntl_tw_arm_upper.
Print Assumptions ntl_tw_arm_lower.
Print Assumptions ntl_tw_h_le_b_feed.
Print Assumptions ntl_tw_h_le_feed.
Print Assumptions ntl_tw_h_le_feed_to_b.
