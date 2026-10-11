(* 模块：tlw1703_nsep_minimal_bexp.v —— 最小分离窗阶的显式预算基重述层。
   数学使命：lw5n_nsep_minimal（LW5SepComplexity.v :513）的语句面以旧预算
   lw5n_bnd 的足用性前提承载，而该预算对分离见证不足用（22/7 实例核算；
   LW5SepComplexity.v :412 注记「预算的足用性不在本件主张」）。本模块在
   显式预算基 tlw1448_Bexp q := S(pie_modulus(tlw1448_ck q / 2)) 上重述
   最小性刻画并移除该前提：换基搜索器 tlw1448_nsep_rebase tlw1448_ck q
   无条件停在预算基内的最小命中级——预算基内存在命中由闭合定理
   tlw1459_fold_closed_leiblw 供给，命中、预算上界、最小性（下方无命中）、
   搜索停点四支合一；并给出与原语句面同形的刻画定理（预算前提换为 Bexp 基）
   与命中前提的无条件供给定理。
   依赖清单：Stdlib QArith/Bool/Arith/Lia；S01_BaseRing（NatLe/NatLe_lift/
   NatLe_drop）；LW0LeibWindow（leiblw_Id/leiblw_id_intro/leiblw_id_inv）；
   LW5SepComplexity（lw5n_sep_dec/lw5n_find）；tlw1448_rebase（tlw1448_bexp/
   tlw1448_nsep_rebase/_bound/_hit/_least）；tlw1448_transfer（tlw1448_ck/
   tlw1448_Bexp）；tlw1459_fold（tlw1459_fold_closed_leiblw）。
   对标行：LW5SepComplexity.v :513（lw5n_nsep_minimal 旧预算基原形，本件
   语句面为其 Bexp 基同构重述）；tlw1459_fold.v :74（tlw1459_band 四支形，
   本件主定理补全其最小性支）；tlw1448_rebase.v :59（命中机件）。
   构造性注记：全 Set/Type 层；零 Axiom/Admitted；零经典逻辑；结论位承载
   于 leiblw_Id/NatLe/sigT/And:=prod；nat 序仅出现于前提位与最小性分量的
   前提位（forall m, m < n0 -> ...，与 lw5n_nsep_minimal 原形同工艺）；
   证明体含分情形与算术推导链；提取面 Obj.magic=0；文末 Print Assumptions
   全 Closed。
   编译配方：coqc -native-compiler no -q -Q . "" tlw1703_nsep_minimal_bexp.v
   （双 export COQLIB/ROCQLIB；工作目录为认证 vo 播种闭包）。
*)

From Stdlib Require Import QArith.QArith Bool.Bool Arith.Arith.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import LW0LeibWindow.
Require Import LW5SepComplexity.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1459_fold.

(* 主定理：换基搜索停在显式预算基内的最小命中级（四支合一，零前提） *)
Theorem tlw1703_nsep_minimal_bexp : forall q : Q,
  sigT (fun n0 : nat =>
    And (leiblw_Id (lw5n_sep_dec q n0) true)
        (And (NatLe n0 (tlw1448_Bexp q))
             (And (forall m : nat, (m < n0)%nat ->
                     leiblw_Id (lw5n_sep_dec q m) false)
                  (leiblw_Id (tlw1448_nsep_rebase tlw1448_ck q) n0)))).
Proof.
  intros q.
  destruct (tlw1459_fold_closed_leiblw q) as [n0 [Hhit Hle]].
  exists (tlw1448_nsep_rebase tlw1448_ck q).
  split.
  - (* 命中支：闭合定理见证在预算基内，命中机件移至搜索停点 *)
    exact (tlw1448_nsep_rebase_hit tlw1448_ck q n0
             (NatLe_drop n0 (tlw1448_Bexp q) Hle) Hhit).
  - split.
    + (* 预算上界支：搜索不越显式预算基 *)
      apply NatLe_lift. exact (tlw1448_nsep_rebase_bound tlw1448_ck q).
    + split.
      * (* 最小性支：严格低于停点处无命中。
           反证：若 m 处命中，则不越定理给出停点 <= m，与 m < 停点相抵 *)
        intros m Hm. destruct (lw5n_sep_dec q m) eqn:E.
        -- exfalso.
           pose proof (tlw1448_nsep_rebase_bound tlw1448_ck q) as Hb.
           assert (Hb2 : (tlw1448_nsep_rebase tlw1448_ck q
                          <= tlw1448_Bexp q)%nat) by exact Hb.
           assert (Hmb : (m <= tlw1448_Bexp q)%nat) by lia.
           assert (Hhitm : leiblw_Id (lw5n_sep_dec q m) true).
           { rewrite E. apply leiblw_id_intro. }
           pose proof (tlw1448_nsep_rebase_least tlw1448_ck q m Hmb Hhitm)
             as Hr.
           lia.
        -- apply leiblw_id_intro.
      * (* 停点支：搜索结果即该最小命中级 *)
        apply leiblw_id_intro.
Qed.

(* 刻画定理：与 lw5n_nsep_minimal 语句面同形，预算前提换为 Bexp 基 *)
Theorem tlw1703_nsep_minimal_char : forall (q : Q) (n0 : nat),
  (n0 <= tlw1448_Bexp q)%nat ->
  leiblw_Id (lw5n_sep_dec q n0) true ->
  (forall m : nat, (m < n0)%nat -> leiblw_Id (lw5n_sep_dec q m) false) ->
  leiblw_Id (tlw1448_nsep_rebase tlw1448_ck q) n0.
Proof.
  intros q n0 Hb Hn Hmin.
  assert (Hhit := tlw1448_nsep_rebase_hit tlw1448_ck q n0 Hb Hn).
  pose proof (tlw1448_nsep_rebase_least tlw1448_ck q n0 Hb Hn) as Hle.
  destruct (Nat.eq_dec (tlw1448_nsep_rebase tlw1448_ck q) n0) as [E|E].
  - rewrite E. apply leiblw_id_intro.
  - exfalso.
    assert (Hlt : (tlw1448_nsep_rebase tlw1448_ck q < n0)%nat) by lia.
    specialize (Hmin _ Hlt).
    assert (Ht : lw5n_sep_dec q (tlw1448_nsep_rebase tlw1448_ck q) = true)
      by (apply leiblw_id_inv; exact Hhit).
    rewrite Ht in Hmin. inversion Hmin.
Qed.

(* 命中前提的无条件供给定理：组合件 uacm_pi_strong_sep_combo 的命中前提
   （lw5n_sep_dec (a/b) (lw5n_nsep (a/b)) 出 true 的假设位）在换基搜索器与
   显式预算基上由闭合定理直接供给，记录形（逐行取自主定理输入链） *)
Theorem tlw1703_rebase_hit_unconditional : forall q : Q,
  leiblw_Id (lw5n_sep_dec q (tlw1448_nsep_rebase tlw1448_ck q)) true.
Proof.
  intros q.
  destruct (tlw1459_fold_closed_leiblw q) as [n0 [Hhit Hle]].
  exact (tlw1448_nsep_rebase_hit tlw1448_ck q n0
           (NatLe_drop n0 (tlw1448_Bexp q) Hle) Hhit).
Qed.

(* ---- 假设审计（应全 Closed）---- *)
Print Assumptions tlw1703_nsep_minimal_bexp.
Print Assumptions tlw1703_nsep_minimal_char.
Print Assumptions tlw1703_rebase_hit_unconditional.

(* ---- 提取检验（Obj.magic 应为 0）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1703_ext.ml" tlw1448_nsep_rebase tlw1448_Bexp tlw1703_nsep_minimal_bexp.
