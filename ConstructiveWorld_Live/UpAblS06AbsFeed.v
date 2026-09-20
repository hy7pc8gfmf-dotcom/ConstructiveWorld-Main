(* ============================================================ *)
(* UpAblS06AbsFeed.v —— S06 经典 R 世界 abs_sum_le 槽×2 直配件（N5 席）      *)
(*                                                                *)
(* 席位：N5（S06 槽直配席）· 20260920 ｜ 零承认件：全件 Qed 闭合、零公理、      *)
(*   零承认词面、零经典逻辑；语句面仅 real_le_b/real_eq 集合层谓词，无裸命题。   *)
(*                                                                *)
(* 【形态桥定谳（头注即定谳正文）】                                       *)
(*   S06 两槽（S06_DiffSamplingGibbs.v:4360-4375 abs_kernel_bound、           *)
(*   :4893-4935 eviction_steady_deviation）的求和算子形＝SumOver 类           *)
(*   （S01:1398-1435）字段 abs_sum_le 的直接消费位，载体为接口投影 @R RI       *)
(*   （RealInterfaceEnhanced 任意实例、le 字段不透明）。供体 B.3              *)
(*   （uabS4c_abs_sum_le_B_slot）为任意 S:Set+抽象 sumf 的槽位本位 B 形，       *)
(*   值域为具体 Real（sigT 柯西序列，S02:394）。四维形态差逐条申报：            *)
(*   ①载体维：@R RI（接口投影）vs 具体 Real——树内无接口实例桥，且 E182 已判    *)
(*     Id 版接口不可实例化至 Real 层（S08:2893 判词在案），故 S06 槽语句的       *)
(*     @le RI 面不可由供体字面覆盖——直配＝「S06 槽形的 B 层镜像供给」，          *)
(*     槽形逐位保持（|Σ f·q| ≤_B Σ |f|·q），载体落在具体 Real；               *)
(*   ②序维：接口 @le RI 不透明 vs real_le_b（Bishop 形，UpRealLeB:72）——      *)
(*     供体结论为可达最强形；接口面仅有单向桥（S4B 报告 §3 机理位在案）；        *)
(*   ③相等维：Id（接口）vs real_eq（逐 eps）——转换层以 real_eq 运输；         *)
(*   ④求和维：sum_over_S 类字段 vs 抽象 sumf——此维同构（任意 S:Set+           *)
(*     (S→Real)→Real 算子形一致；供体三前件与 SumOver 字段 sum_over_S_ext/    *)
(*     add/le 逐位镜像），故本件以三前件显式量化直取供体。                      *)
(*                                                                *)
(* 【两槽逐槽处置】                                                      *)
(*   槽1（abs_kernel_bound 形）：真实施工全款——供给 Corollary                  *)
(*     s6f_abs_kernel_bound_slot：供体 B.2 在 g:=f·q 上直取＋点态转换层        *)
(*     （|x·q| ≡ |x|·q，q ≥_B 0：|q|≡q 逐 eps 尾部 chased＋Qabs_mult 恒等＋     *)
(*     real_eq_mult_compat）＋sum_ext 和面运输＋B 形右端相等运输（A.4，         *)
(*     供体 A.5 的对偶位，树内原缺，本件补齐）。                                *)
(*   槽2（eviction_steady_deviation 形）：零施工定谳登记——S06:4919 的           *)
(*     abs_sum_le 消费面＝类字段裸应用（零特化：abs_sum_le (fun s' => ...)      *)
(*     逐字），其槽位本位供给＝供体 B.2 本身（同语句覆盖），其余差分改写/线性     *)
(*     提出面为接口 Id 代数重述（零消费）——按令不硬凑，零施工定谳入账。          *)
(*                                                                *)
(* 【依赖】Require 消费 UpAblAbsSumLeB3（H1 供体件）＋CW 世界＋UpRealLeB        *)
(*   ＋S08；本件为独立新增，禁碰 S06/供体/任何既有文件，不入 order.txt/_CoqProject。 *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring QArith.Qabs QArith.Qminmax.
From Stdlib Require Import Lia.
From Stdlib Require Import Lqa.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.
Require Import UpAblAbsSumLeB3.

(* ============================================================ *)
(* Part 0 · 冻结现态复刻：武器在库打表（签名漂移即 fail-loud）              *)
(* ============================================================ *)

Check real_le_b.              (* UpRealLeB:72 Bishop 形 ≤（语句面谓词） *)
Check real_eq.                (* S02:396 逐 eps 相等（集合层） *)
Check real_abs.               (* S03:6510 逐点 Qabs *)
Check real_abs_proj.          (* 逐点投影 *)
Check real_mult.              (* S02:649 *)
Check real_mult_proj.         (* S02:1310 逐点投影 *)
Check real_const.             (* S02:858 *)
Check real_const_proj.        (* S02:1322 逐点投影 *)
Check real_eq_trans.          (* 等式传递 *)
Check real_eq_refl.           (* 等式自反 *)
Check real_eq_of_zero_diff.   (* S02:2317 逐点零差分 ⟹ real_eq *)
Check RealSetoid.real_eq_mult_compat. (* S07:282 乘法相等兼容 *)
Check uabS4c_abs_sum_le_B_slot. (* 供体 B.2 主定理（End 后全称化） *)
Check uabS4c_abs_sum_le_eps_slot. (* 供体 B.3 逐 eps 回收（槽2 覆盖供给位） *)
Check Qabs_Qmult.             (* Q 层：Qabs (u·v) == Qabs u·Qabs v *)
Check Qabs_pos.               (* Q 层：0 ≤ u ⟹ Qabs u == u *)
Check Qabs_neg.               (* Q 层：0 ≤ −u ⟹ Qabs u == −u *)
Check Qlt_shift_div_l.        (* Q 层半分正性 *)
Check Qlt_to_QltT.
Check QltT_to_Qlt.
Check Qlt_le_dec.             (* Q 可判定符号（非经典） *)
Check Qle_Qabs.               (* Q 层：u ≤ Qabs u *)
Check Qlt_le_trans.
Check NatLe_lift.
Check NatLe_drop.

(* ============================================================ *)
(* Part A · 转换层（点态 abs 换形＋B 形右端相等运输）                       *)
(* ============================================================ *)

(* A.0 Q 层正常性桥：0 < e（有理）⟹ 0 <_lt real_const e
   （见证：半量 d:=e·½，N:=0，逐点 real_const_proj 投影即 e。
     环境坑：lra 对 Q 除法失灵（T1 探针在案），半量一律走 ·(1#2) 乘法形） *)
Lemma s6f_q_const_pos : forall e : Q,
  QltT 0 e -> real_lt real_zero (real_const e).
Proof.
  intros e He.
  assert (Hhalfq : Qlt 0 (e * (1#2))).
  { apply QltT_to_Qlt in He. lra. }
  assert (Hhalf : QltT 0 (e * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  exists (e * (1#2))%Q. split.
  - exact Hhalf.
  - exists O. intros n Hn.
    apply Qlt_to_QltT.
    rewrite real_const_proj.
    assert (Hz : projT1 real_zero n == 0) by reflexivity.
    rewrite Hz.
    lra.
Qed.

(* A.1 非负实数的 abs 恒等：0 ≤_B q ⟹ |q| ≡ q。
   机理：B 形在 half 预算上取尾部（q_n > −e/2 最终），尾部二分：
   q_n<0 支 −2q_n < e；q_n≥0 支 Qabs q_n == q_n 零差。 *)
Lemma s6f_abs_nonneg_eq : forall q : Real,
  real_le_b real_zero q -> real_eq (real_abs q) q.
Proof.
  intros q Hq.
  unfold real_eq. intros eps0 Heps0.
  (* B 形预算取半量（·(1#2) 乘法形）：尾部 q_n > d0 − eps0/2 > −eps0/2，
     二分后 lt 支 −2q_n < eps0、ge 支零差 *)
  assert (Hhalfq : Qlt 0 (eps0 * (1#2))).
  { apply QltT_to_Qlt in Heps0. lra. }
  assert (Hhalf : QltT 0 (eps0 * (1#2))) by (apply Qlt_to_QltT; exact Hhalfq).
  destruct (Hq (real_const (eps0 * (1#2))) (s6f_q_const_pos (eps0 * (1#2)) Hhalf))
    as [d0 [Hd0 [N0 HN0]]].
  exists N0. intros n Hn.
  apply Qlt_to_QltT.
  rewrite real_abs_proj.
  pose proof (HN0 n Hn) as Hp. apply QltT_to_Qlt in Hp.
  rewrite real_plus_proj in Hp.
  rewrite real_const_proj in Hp.
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz in Hp.
  assert (Hd0q : Qlt 0 d0) by (apply QltT_to_Qlt; exact Hd0).
  destruct (Qlt_le_dec (projT1 q n) 0) as [Hqn | Hqn].
  - assert (Habs : Qabs (projT1 q n) == - projT1 q n)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hqn).
    rewrite Habs.
    assert (Hp2 : Qlt 0 (- projT1 q n - projT1 q n)) by lra.
    assert (Habs2 : Qabs (- projT1 q n - projT1 q n)
                    == - projT1 q n - projT1 q n)
      by (apply Qabs_pos; apply Qlt_le_weak; exact Hp2).
    rewrite Habs2.
    lra.
  - assert (Habs : Qabs (projT1 q n) == projT1 q n)
      by (apply Qabs_pos; exact Hqn).
    rewrite Habs.
    assert (Hz2 : projT1 q n - projT1 q n == 0) by lra.
    rewrite Hz2.
    assert (Hz3 : Qabs 0 == 0) by reflexivity.
    rewrite Hz3.
    apply QltT_to_Qlt. exact Heps0.
Qed.

(* A.2 双 abs 乘积恒等（无条件）：|x·q| ≡ |x|·|q|。
   机理：real_eq_of_zero_diff 逐点零差＋Qabs_mult 恒等（Q 层非经典）。 *)
Lemma s6f_abs_abs_mult_eq : forall x q : Real,
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) (real_abs q)).
Proof.
  intros x q. apply real_eq_of_zero_diff. intro n.
  rewrite !real_abs_proj.
  rewrite !real_mult_proj.
  rewrite !real_abs_proj.
  rewrite Qabs_Qmult.
  lra.
Qed.

(* A.3 点态换形主件（槽1 转换层核心）：0 ≤_B q ⟹ |x·q| ≡ |x|·q。
   链：|x·q| ≡ |x|·|q|（A.2）≡ |x|·q（A.1＋乘法相等兼容）。 *)
Lemma s6f_abs_mult_eq : forall x q : Real,
  real_le_b real_zero q ->
  real_eq (real_abs (real_mult x q)) (real_mult (real_abs x) q).
Proof.
  intros x q Hq.
  eapply real_eq_trans.
  - apply s6f_abs_abs_mult_eq.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply s6f_abs_nonneg_eq. exact Hq.
Qed.

(* A.4 B 形右端相等运输（供体 A.5 的对偶位，树内原缺，本件补齐）：
   a ≡ b 且 Y ≤_B a ⟹ Y ≤_B b。
   机理：margin d 复用——real_eq 在预算 d 上取 |a_n−b_n|<d 尾部，
   与 Y+a 侧 margin 缝合（max 尾），Q 层 lra 收束。 *)
Lemma s6f_leb_req_right : forall a b Y : Real,
  real_eq a b -> real_le_b Y a -> real_le_b Y b.
Proof.
  intros a b Y Hab HYa eps Heps.
  pose proof (HYa eps Heps) as HYa'.
  unfold real_le_b in HYa'. unfold real_lt in HYa'.
  destruct HYa' as [d [Hd [N1 HN1]]].
  (* 半量见证：h := d·½——等式预算恰取半量，缝合后 d−h = h 精确收束 *)
  assert (Hh : Qlt 0 (d * (1#2))).
  { apply QltT_to_Qlt in Hd. lra. }
  assert (HhT : QltT 0 (d * (1#2))) by (apply Qlt_to_QltT; exact Hh).
  destruct (Hab (d * (1#2)) HhT) as [N2 HN2].
  exists (d * (1#2)). split.
  - exact HhT.
  - exists (Nat.max N1 N2). intros n Hn.
    assert (Ha1 : NatLe N1 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    assert (Ha2 : NatLe N2 n).
    { apply NatLe_lift.
      assert (Hdrop : (Nat.max N1 N2 <= n)%nat) by exact (NatLe_drop _ _ Hn).
      lia. }
    apply Qlt_to_QltT.
    pose proof (HN1 n Ha1) as Hp1. apply QltT_to_Qlt in Hp1.
    rewrite real_plus_proj in Hp1.
    pose proof (HN2 n Ha2) as Hp2. apply QltT_to_Qlt in Hp2.
    assert (Hge : Qle (projT1 a n - projT1 b n)
                      (Qabs (projT1 a n - projT1 b n)))
      by apply Qle_Qabs.
    assert (Hp2' : Qlt (projT1 a n - projT1 b n) (d * (1#2)))
      by (apply (Qle_lt_trans _ (Qabs (projT1 a n - projT1 b n)) _);
          [exact Hge | exact Hp2]).
    rewrite real_plus_proj.
    lra.
Qed.

(* ============================================================ *)
(* Part B · 槽1 全款供给：abs_kernel_bound 形的槽位本位 B 层镜像            *)
(*   （S06:4363-4366 语句形逐位保持：|Σ f·q| ≤_B Σ |f|·q；载体＝具体 Real；  *)
(*     sumf 抽象＝任意 S:Set 求和算子，三前件＝供体槽位形显式量化）          *)
(* ============================================================ *)

Theorem s6f_abs_kernel_bound_slot :
  forall (S : Set) (sumf : (S -> Real) -> Real),
    (forall f g : S -> Real,
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g)) ->
    (forall f g : S -> Real,
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g))) ->
    (forall f g : S -> Real,
      (forall s : S, real_le_b (f s) (g s)) -> real_le_b (sumf f) (sumf g)) ->
    forall (f q : S -> Real),
      (forall s : S, real_le_b real_zero (q s)) ->
      real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                (sumf (fun s : S => real_mult (real_abs (f s)) (q s))).
Proof.
  intros S sumf Hext Hadd Hleb f q Hq.
  (* 供体 B.2 在 g := f·q 上直取：|Σ f·q| ≤_B Σ |f·q| *)
  assert (Hdon : real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                           (sumf (fun s : S => real_abs (real_mult (f s) (q s)))))
    by (apply (uabS4c_abs_sum_le_B_slot S sumf Hext Hadd Hleb)).
  (* 点态转换层：|f s·q s| ≡ |f s|·q s（q s ≥_B 0） *)
  assert (Hpt : forall s : S, real_eq (real_abs (real_mult (f s) (q s)))
                                      (real_mult (real_abs (f s)) (q s)))
    by (intro s; apply s6f_abs_mult_eq; exact (Hq s)).
  (* 和面外延运输（槽位前件一） *)
  assert (Hsum : real_eq (sumf (fun s : S => real_abs (real_mult (f s) (q s))))
                         (sumf (fun s : S => real_mult (real_abs (f s)) (q s))))
    by (apply Hext; exact Hpt).
  (* B 形右端相等运输（A.4） *)
  exact (s6f_leb_req_right _ _ _ Hsum Hdon).
Qed.

(* ============================================================ *)
(* Part C · 槽2 零施工定谳登记（头注正文，零代码施工）                      *)
(*   S06:4919 的 abs_sum_le 消费面＝类字段裸应用（零特化），其槽位本位供给＝   *)
(*   供体 B.2 本身（uabS4c_abs_sum_le_B_slot 同语句覆盖，Part 0 打表在案）；   *)
(*   差分改写/线性提出面＝接口 Id 代数重述（零消费）。按令不硬凑。            *)
(* ============================================================ *)

(* G2 证据面：全件承认为零自证（PA 六件套） *)
Print Assumptions s6f_q_const_pos.
Print Assumptions s6f_abs_nonneg_eq.
Print Assumptions s6f_abs_abs_mult_eq.
Print Assumptions s6f_abs_mult_eq.
Print Assumptions s6f_leb_req_right.
Print Assumptions s6f_abs_kernel_bound_slot.
