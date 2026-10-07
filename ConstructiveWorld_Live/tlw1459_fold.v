(* ================================================================== *)
(* TLW1459Fold —— 增长律闭合定理（显式预算界）与格形态双向带              *)
(*                                                                    *)
(* 数学使命：对任意有理数 q，在显式预算界 Bexp(q) := S(pie_modulus       *)
(*   (ck q / 2)) 之内存在分离阶 n0（bool 分离判定器出窗），n0 不越预算   *)
(*   界；其中 ck q 为分离距离 kernel 见证的首分量（定义化直取）。组件：  *)
(*   参数化换基族 tlw1448_rebase（预算基 bexp 与搜索器 nsep_rebase）、   *)
(*   kernel margin 定义化引出 tlw1448_transfer（ck 与 Bexp）、档二上界   *)
(*   tlw1448_l2escape（距离证书 ⟹ 显式窗阶出窗）。合成件一给出双向带：  *)
(*   格序下界（第 m 格含 q 则 m < 8·n0+9，格障碍逆否）与预算上界         *)
(*   （换基搜索器 ≤ n0 ≤ Bexp q）。                                     *)
(*                                                                    *)
(* 依赖清单：Stdlib QArith/List/Bool/Arith/Setoid/Morphisms/Lia/Qminmax；*)
(*   S01_BaseRing LW0LeibWindow LW5SepComplexity tlw1448_rebase          *)
(*   tlw1448_transfer tlw1448_l2escape                                  *)
(*                                                                    *)
(* 对标行：LW5SepComplexity :778（lw5n_shape_band 形态定理）与 :716      *)
(*   （lw5n_cell_obstacle 格障碍，零预算前提）；LW1PiMeasure :373        *)
(*   （lw1m_dist_outwin）；LW0LeibWindow :63（leiblw_Id：项目 Id 的     *)
(*   同构单点形，一行互译）。                                           *)
(*                                                                    *)
(* 构造性注记：全 Set/Type 层；零 Axiom/Admitted；零 Prop 泄露（nat 序   *)
(*   分量以 NatLe 的 Id-of-bool 形承载，Prop 位序不出现在语句面）；      *)
(*   闭合定理 witness 取 Bexp q 自身（定义项展开，非存在性提取）。       *)
(*                                                                    *)
(* 编译配方：coqc -native-compiler no -q -Q . "" tlw1459_fold.v          *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import LW0LeibWindow.
Require Import LW5SepComplexity.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1448_l2escape.

(* 闭合定理：显式预算界内的分离阶存在（语句面与档二结论同用项目 Id，零换形） *)
Theorem tlw1459_fold_closed : forall q : Q,
  sigT (fun n0 : nat =>
    And (Id (lw5n_sep_dec q n0) true)
        (NatLe n0 (tlw1448_Bexp q))).
Proof.
  intros q.
  destruct (tlw1448_kernel_dist_ck q) as [Hc Hd].
  exists (tlw1448_Bexp q).
  split.
  - (* n0 := Bexp q 处出窗：kernel margin 的正性与距离证书过档二上界
       （QltT 到 QltT' 换形走 tlw1448_qltT_to_qltT'） *)
    exact (tlw1448_l2_escape q (tlw1448_ck q)
             (tlw1448_qltT_to_qltT' _ _ Hc) Hd).
  - (* 预算界自反：n0 即 Bexp q *)
    apply NatLe_lift. apply Nat.le_refl.
Qed.

(* 互译副本：同一闭合定理的 leiblw_Id 语句面（与项目 Id 一行互译） *)
Theorem tlw1459_fold_closed_leiblw : forall q : Q,
  sigT (fun n0 : nat =>
    And (leiblw_Id (lw5n_sep_dec q n0) true)
        (NatLe n0 (tlw1448_Bexp q))).
Proof.
  intros q. destruct (tlw1459_fold_closed q) as [n0 [Hsep Hle]].
  exists n0. split.
  - destruct Hsep. apply leiblw_id_intro.
  - exact Hle.
Qed.

(* 双向带：格序下界与预算上界在显式预算基上合成。
   内容四支：n0 处分离；第 m 格含 q 则 m < 8·n0+9（格障碍逆否，零预算
   前提）；换基搜索器不越 n0；n0 不越 Bexp q。 *)
Theorem tlw1459_band : forall (q : Q) (m : nat),
  Qle (lw5n_cell_lo m) q -> Qle q (lw5n_cell_hi m) ->
  sigT (fun n0 : nat =>
    And (leiblw_Id (lw5n_sep_dec q n0) true)
        (And (NatLe (Datatypes.S m) (8 * n0 + 9)%nat)
             (And (NatLe (tlw1448_nsep_rebase tlw1448_ck q) n0)
                  (NatLe n0 (tlw1448_Bexp q))))).
Proof.
  intros q m Hlo Hhi.
  destruct (tlw1459_fold_closed q) as [n0 [Hsep Hle]].
  exists n0. split.
  - destruct Hsep. apply leiblw_id_intro.
  - split.
    + (* 格序下界：8·n0+9 ≤ m 时第 m 格含 q 蕴含 q 入第 n0 窗
         （lw5n_cell_obstacle），与 n0 处分离相抵 *)
      apply NatLe_lift.
      destruct (Nat.le_gt_cases (8 * n0 + 9) m) as [Hge | Hlt].
      * exfalso.
        pose proof (lw5n_cell_obstacle q m n0 Hge Hlo Hhi) as Hf.
        assert (Hl : leiblw_Id (lw5n_sep_dec q n0) true).
        { destruct Hsep. apply leiblw_id_intro. }
        apply leiblw_id_inv in Hl. rewrite Hl in Hf. inversion Hf.
      * exact Hlt.
    + split.
      * (* 换基搜索器不越分离阶（参数化不越定理在 ck 实例处） *)
        assert (Hsepl : leiblw_Id (lw5n_sep_dec q n0) true).
        { destruct Hsep. apply leiblw_id_intro. }
        apply NatLe_lift.
        exact (tlw1448_nsep_rebase_least tlw1448_ck q n0
                 (NatLe_drop n0 (tlw1448_Bexp q) Hle) Hsepl).
      * exact Hle.
Qed.

(* ---- 假设审计（应全 Closed）---- *)
Print Assumptions tlw1459_fold_closed.
Print Assumptions tlw1459_fold_closed_leiblw.
Print Assumptions tlw1459_band.

(* ---- 提取探针（Obj.magic 计数如实登记；ck 走 projT1 路径为观察点）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1459_fold_ext.ml" tlw1448_ck tlw1448_Bexp tlw1459_fold_closed.
