(* ============================================================ *)
(* NsepBudgetExhaustion.v —— 预算耗尽见证件：lw5n 预算足用性前提的显式 *)
(*   反例（q = 22/7，机器验证）。                                     *)
(*   使命 (Mission): 预算化最小分离索引搜索 nsep_first 的无条件命中形  *)
(*   经足用合成归约至单一前提「对每 q 存在命中阶 n0 <= lw5n_bnd q」；  *)
(*   本件构造性否证该前提：q0 落入第 0 至预算端点 34 全部窗，预算全程 *)
(*   耗尽——搜索输出端点且端点判定非命中，无条件形在 q0 处取值 false。 *)
(*   依赖 (Dependencies): LW0LeibWindow（leiblw_Id/id_eq/id_inv/       *)
(*   leiblw_Qleb）、S01_BaseRing（And := A*B 的 Set 面合取）、         *)
(*   NsepFindGeneric（nsep_find）、LW5SepComplexity（lw5n_find/        *)
(*   lw5n_bnd/lw5n_nsep/lw5n_sep_dec/lw5n_win_nested）、NsepBudget     *)
(*   Verify（q0/两计算钉/lw5n_inwin_q0_all 拆件）；Stdlib QArith/      *)
(*   ZArith/Arith/Bool/Lia/Extraction.                                 *)
(*   对标 (References): LW5SepComplexity.v lw5n_find :412/lw5n_bnd     *)
(*   :427/lw5n_nsep :429/lw5n_win_nested :228；NsepFindGeneric.v :45。 *)
(*   手术 (Surgery, 件B 两刀): ①常量化——全阶窗内引理不走             *)
(*   lw5n_shape_mono 全量物化，改走 lw5n_win_nested 解析嵌套＋第 34    *)
(*   级两枚 Q 序钉（见 NsepBudgetVerify.v）；②fixpoint 桥去污——       *)
(*   原稿 §3 直接 destruct nsep_find_exhaust 使内核 Qed 对账两个不同  *)
(*   fixpoint（lw5n_find :412 与 nsep_find :45），逐级展开强算 34 级  *)
(*   窗判定（born 成本爆炸根因，实测 Qed 冻结）；本件以桥引理         *)
(*   lw5n_find_nsep_find（纯符号 case 分析）先重写后 destruct。        *)
(*   构造性 (Constructivity): 零公理/零承认式/零经典逻辑；§1-§2 主   *)
(*   结论面全 Set；§3 两枚否证语句为纯 Prop 位（Nat.le 序＋bool 等词 *)
(*   承载，leiblw_Id 面由证明体内 id 引理转置——原语句面 Set 级 And  *)
(*   配 Prop 位不可触（REPL 实测），B 档随件申报，沿 lw5n_shape_band  *)
(*   先例不入提取单；本件零 vm_compute；提取面 Obj.magic = 0。         *)
(*   编译配方：先单发 NsepBudgetVerify.v，再单发本件（-Q 沙箱在前     *)
(*   -Q 树根在后）；被依赖件 NsepFindGeneric.v 同世界先编。           *)
(* ============================================================ *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import LW0LeibWindow.
Require Import S01_BaseRing.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.
Require Import NsepBudgetVerify.

(* ============================================================ *)
(* §0 等词接口补充：leiblw_Id 的 false 面提取（库内 leiblw_id_eq/      *)
(*    leiblw_id_inv 仅覆盖 bool 的 =true 面）。                         *)
(* ============================================================ *)

Lemma leiblw_id_false_inv : forall b : bool, leiblw_Id b false -> b = false.
Proof.
  intros b H. destruct b as [|].
  - inversion H.
  - reflexivity.
Qed.

(* ============================================================ *)
(* §1 通用耗尽引理：区间内逐阶非命中则搜索输出预算端点且端点处非命中。 *)
(* ============================================================ *)

Lemma nsep_find_exhaust :
  forall (dec : Q -> nat -> bool) (q : Q) (fuel n : nat),
  (forall m : nat, (n <= m)%nat -> (m <= n + fuel)%nat ->
                   leiblw_Id (dec q m) false) ->
  And (leiblw_Id (nsep_find dec q n fuel) (n + fuel)%nat)
      (leiblw_Id (dec q (nsep_find dec q n fuel)) false).
Proof.
  intros dec q fuel. induction fuel as [|f IH]; intros n H.
  - simpl. split.
    + replace (n + 0)%nat with n by lia. apply leiblw_id_intro.
    + apply H; lia.
  - assert (Hn : dec q n = false)
      by (apply leiblw_id_false_inv; apply H; lia).
    assert (Hr : And (leiblw_Id (nsep_find dec q (Datatypes.S n) f)
                                (Datatypes.S n + f)%nat)
                     (leiblw_Id (dec q (nsep_find dec q (Datatypes.S n) f))
                                false)).
    { apply (IH (Datatypes.S n)). intros m Hm1 Hm2. apply H; lia. }
    destruct Hr as [Hend Hout]. simpl. rewrite Hn.
    replace (n + Datatypes.S f)%nat with (Datatypes.S n + f)%nat by lia.
    split.
    + exact Hend.
    + exact Hout.
Qed.

(* ============================================================ *)
(* §2 预算耗尽推论：q0 的搜索输出预算端点 34，且端点处判定非命中。      *)
(*    桥引理先重写（lw5n_find ≡ nsep_find lw5n_sep_dec 逐点，纯符号     *)
(*    case 分析）再 destruct，内核 Qed 零窗计算（手术刀②，见头注）。    *)
(*    （原 §2 实例锚点与计算钉、全阶窗内引理均已拆入                    *)
(*    NsepBudgetVerify.v，经 Require 在位；本节编号顺延。）             *)
(* ============================================================ *)

Lemma lw5n_find_nsep_find : forall q n fuel,
  lw5n_find q n fuel = nsep_find lw5n_sep_dec q n fuel.
Proof.
  intros q n fuel. revert n. induction fuel as [|f IH]; intros n.
  - reflexivity.
  - cbn [lw5n_find nsep_find]. destruct (lw5n_sep_dec q n).
    + reflexivity.
    + rewrite (IH (Datatypes.S n)). reflexivity.
Qed.

Lemma nsep_q0_no_hit_hyp :
  forall m : nat, (0 <= m)%nat -> (m <= 0 + 34)%nat ->
    leiblw_Id (lw5n_sep_dec q0 m) false.
Proof.
  intros m Hm1 Hm2. unfold lw5n_sep_dec.
  assert (Hb : (m <= 34)%nat) by lia.
  pose proof (lw5n_inwin_q0_all m Hb) as Hw.
  apply leiblw_id_inv in Hw. rewrite Hw. apply leiblw_id_intro.
Qed.

Lemma lw5n_nsep_q0_exhaust :
  And (leiblw_Id (lw5n_nsep q0) 34%nat)
      (leiblw_Id (lw5n_sep_dec q0 (lw5n_nsep q0)) false).
Proof.
  unfold lw5n_nsep. rewrite lw5n_find_nsep_find. rewrite lw5n_bnd_q0.
  destruct (nsep_find_exhaust lw5n_sep_dec q0 34 0 nsep_q0_no_hit_hyp)
    as [Hend Hout].
  replace (0 + 34)%nat with 34%nat in Hend by lia.
  split.
  - exact Hend.
  - exact Hout.
Qed.

Lemma lw5n_nsep_q0_at_bnd : leiblw_Id (lw5n_nsep q0) (lw5n_bnd q0).
Proof. rewrite lw5n_bnd_q0. exact (fst lw5n_nsep_q0_exhaust). Qed.

(* ============================================================ *)
(* §3 否证面：预算内无命中阶；无条件形在 q0 处取值 false。语句为        *)
(*    纯 Prop 位（Nat.le 序＋bool 等词；B 档，沿 lw5n_shape_band        *)
(*    先例，不入提取单）。                                              *)
(* ============================================================ *)

Theorem nsep_no_hit_q0 :
  ~ (exists n0 : nat, (n0 <= lw5n_bnd q0)%nat /\
                      lw5n_sep_dec q0 n0 = true).
Proof.
  intros [n0 [Hb Hs]].
  rewrite lw5n_bnd_q0 in Hb.
  assert (Hw : lw5n_inwin q0 n0 = true)
    by (apply leiblw_id_inv; apply lw5n_inwin_q0_all; exact Hb).
  unfold lw5n_sep_dec in Hs. apply negb_true_iff in Hs.
  rewrite Hw in Hs. discriminate Hs.
Qed.

Theorem nsep_uncond_false_q0 :
  ~ (forall q : Q, lw5n_sep_dec q (lw5n_nsep q) = true).
Proof.
  intro H.
  pose proof (H q0) as Hq.
  pose proof (snd lw5n_nsep_q0_exhaust) as Hf.
  apply leiblw_id_false_inv in Hf.
  rewrite Hq in Hf. discriminate Hf.
Qed.

(* ============================================================ *)
(* §4 提取核查与假设审计。                                              *)
(* ============================================================ *)

Separate Extraction lw5n_sep_dec lw5n_bnd lw5n_nsep.

Print Assumptions leiblw_id_false_inv.
Print Assumptions nsep_find_exhaust.
Print Assumptions lw5n_nsep_q0_exhaust.
Print Assumptions lw5n_nsep_q0_at_bnd.
Print Assumptions nsep_no_hit_q0.
Print Assumptions nsep_uncond_false_q0.
