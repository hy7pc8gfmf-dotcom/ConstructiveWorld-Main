(* ============================================================ *)
(* UpAblTwLeFeed.v —— tw_h_le 槽两点核差 B 形直配供给件（新独立件）      *)
(*                                                                *)
(* 席位：N3R（UpTempWindow tw_h_le 两点核差 B 形直配席）· 20260920      *)
(* 零承认件：无承认词面、无假设槽位声明、无经典逻辑、全件 Qed 闭合。     *)
(*   语句全 Set 层值（real_le/real_lt/real_le_b 均 Set）；             *)
(*   证明全构造（Or 逐支、供体右吸收直喂）；语句面无裸「命题层」。          *)
(*                                                                *)
(* 主件定谳：UpTempWindow.v:1413 槽 tw_h_le（逐点绝对值界               *)
(*   |w_T(x) − 1/N| ≤ (e^{2Δ/T} − 1)·(1/N)，Section TempWindow         *)
(*   卸载后外形）的 B 形直配：语句与槽实形逐字对齐（世界接口              *)
(*   Tok/states/states_nonempty/zz/Delta/Delta_pos/双界逐字同位），     *)
(*   外层谓词升 Bishop B 形（real_le_b，UpRealLeB:72 可达最强形）。     *)
(*                                                                *)
(* 形态差显式申报（照 AB2 B8 增薄先例，三条）：                          *)
(*   ① 三角形增薄差：供体两点核差三角（uabS4_abs_diff_triangle_le_B）    *)
(*     过中点 m=E2L·u 实例化于窗口三点（本件转换层 ntl_tw_diff_tri_*）    *)
(*     给出 |w−u| ≤ |w−m|+|m−u| ≤ (E2−2·E2L+1)·u，较槽锐界               *)
(*     (E2−1)·u 增薄 2·(1−E2L)·u ≥ 0（E2L ≤ 1），锐界不可经单次三角      *)
(*     直达——故三角实例按「适配消费级」交付（逐字实例化，如实定性），     *)
(*     槽锐界主件改走「臂式 eps 族＋供体正余量右吸收」路线。              *)
(*   ② B 形与 plain 形的形态差：槽实形为 plain Or 编码序                  *)
(*     （real_le = Or(lt,eq)）；本件主件为 B 形（real_le_b，Set 层       *)
(*     forall 型）。plain⟹B 单向桥在库（real_le_to_le_b）；B⟹plain      *)
(*     方向按族 doctrine 不可达（族I 墙 E751 判词口径）。故主件交付      *)
(*     B 形直配，plain 回收件（ntl_tw_h_le_feed）以臂式重组独立供给      *)
(*     （tw_abs_le 内构 Or 分支），语句与槽实形逐字同形，不调用槽本体。  *)
(*   ③ 前提消费同位：臂式路线与槽本体同需 Delta_pos（下臂                     *)
(*     「1−E2L ≤ E2−1」步经 tw_u2_pos 实例化，正性证书同源）——              *)
(*     主件两件逐字保留槽形全接口（Delta_pos 在场且消费），如实申报：        *)
(*     接口无增薄无削减，差异仅在外层谓词与证明路线。                         *)
(*                                                                *)
(* 供体消费定性：主件 B 形两臂均经 uabS4_le_add_r 右吸收 eps＝供体       *)
(*   真消费（非平凡）；转换层三角实例＝逐字实例化＝适配消费级（如实      *)
(*   定性，见形态差①）。                                                *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219＋UpRealLeB＋S08_RealMainlineDPO＋     *)
(*   UpTempWindow（槽源，Require 消费）＋UpAblAbsSumLeB（S4 供体）。     *)
(*   本件不触碰任何既有文件；不入 order.txt/_CoqProject。                *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpTempWindow.
Require Import UpAblAbsSumLeB.

(* ============================================================ *)
(* Part 0 · 冻结现态复刻：武器在库打表（签名漂移即 fail-loud）          *)
(* ============================================================ *)

Check tw_h_le.                   (* UpTempWindow:1413 槽实形（卸载后） *)
Check tw_unif_dist.              (* 1/N（卸载后三参） *)
Check tw_wT.                     (* 窗口权重（卸载后七参） *)
Check tw_E2.                     (* e^{2Δ/T}（Delta 首参） *)
Check tw_E2L.                    (* e^{−2Δ/T} *)
Check uabS4_le_add_r.            (* 供体正余量右吸收（主件消费位） *)
Check uabS4_abs_diff_triangle_le_eps. (* 供体两点核差逐 eps（转换层） *)
Check uabS4_abs_diff_triangle_le_B.   (* 供体两点核差 B 形（转换层） *)
Check real_le_closure_b_one.     (* B 形单步完成机 *)
Check real_le_to_le_b.           (* plain⟹B 单向桥 *)
Check tw_abs_le.                 (* |x| ≤ c 双臂组合器 *)
Check tw_ring_sub_mult.          (* x·y + −y == (x + −1)·y *)
Check tw_ring_sub_mult_l.        (* y + −(x·y) == (1 + −x)·y *)
Check tw_wT_le_E2invN.           (* 上臂源：w ≤ E2·(1/N) *)
Check tw_E2LinvN_le_wT.          (* 下臂源：E2L·(1/N) ≤ w *)
Check tw_one_minus_exp_le.       (* 1−e^{−E} ≤ e^{E}−1 *)
Check real_le_plus_compat.       (* 加法保序 *)
Check real_le_mult_compat.       (* 正系数乘法保序 *)
Check real_le_trans.             (* 序传递 *)
Check real_opp_plus.             (* −(a+b) == −a + −b *)
Check real_opp_opp.              (* −(−x) == x *)
Check real_plus_comm.            (* 交换 *)
Check real_inv_pos_pos.          (* inv 正性 *)
Check real_minus_r.              (* a−b := a + −b（S12） *)

(* ============================================================ *)
(* Part 1 · 转换层：供体两点核差形窗口直配实例（适配消费级）            *)
(*   三点实例化：a := w_T(x)、b := E2L·(1/N)、c := 1/N。               *)
(*   增薄差申报见头注形态差①：本层两件较槽锐界严格增薄。               *)
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
(* Part 2 · 臂基件：槽锐界两臂（B 形主件与 plain 回收件共用）           *)
(*   上臂：w − (1/N) ≤ (E2 − 1)·(1/N)——tw_wT_le_E2invN ＋ 加法保序     *)
(*         ＋ tw_ring_sub_mult 换形。                                   *)
(*   下臂：−(w − (1/N)) ≤ (E2 − 1)·(1/N)——tw_E2LinvN_le_wT 经负号      *)
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
  (* 步1：u − w ≤ u − E2L·u（负号翻转下臂源） *)
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
  (* 收束：tw_le_eq_l（le a b ＋ eq a c ⟹ le c b） *)
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
(* Part 3 · 主件 A：槽锐界 B 形直配（可达最强形）                        *)
(*   语句：槽实形（UpTempWindow:1413 卸载后）外层谓词升 real_le_b，      *)
(*   其余逐字同位。证明：real_le_closure_b_one 单步完成 ＋ 两臂经        *)
(*   供体正余量右吸收 uabS4_le_add_r 分摊 eps＝供体真消费。              *)
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
(* Part 4 · 主件 B：plain 回收件（语句与槽实形逐字对齐）                 *)
(*   语句＝tw_h_le 卸载后外形逐字（世界接口同位同序）；证明＝臂式       *)
(*   重组（tw_abs_le 内构 Or 分支），不调用槽本体（独立重实现，          *)
(*   与槽本体结论内容等价——如实申报：本件为槽界的 plain 面回收）。      *)
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

(* 桥演示：plain 回收件经单向桥升 B 形＝主件 A 同语句（plain⟹B 在库） *)
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
(* 公理面自审：全件 Closed（零外部未证假设）                             *)
(* ============================================================ *)

Print Assumptions ntl_tw_diff_tri_eps.
Print Assumptions ntl_tw_diff_tri_B.
Print Assumptions ntl_tw_arm_upper.
Print Assumptions ntl_tw_arm_lower.
Print Assumptions ntl_tw_h_le_b_feed.
Print Assumptions ntl_tw_h_le_feed.
Print Assumptions ntl_tw_h_le_feed_to_b.
