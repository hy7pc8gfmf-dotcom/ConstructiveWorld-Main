(* ============================================================ *)
(* UpAblS06AbsFeed.v —— S06 abs_sum_le 语句形的 B 层供给件         *)
(*                                                                *)
(* 使命：S06 经典 R 世界中两处求和语句（abs_kernel_bound 与        *)
(*   eviction_steady_deviation 形）的结论属 SumOver 类字段 abs_sum_le； *)
(*   本件给出其在具体 Real 载体上的 B 形（real_le_b）供给：其一由  *)
(*   s6f_abs_kernel_bound_slot 全称给出，其二由供体本名定理覆盖。  *)
(*                                                                *)
(* 构造性注记：全件 Qed 闭合、零承认词面、零经典逻辑；语句面仅     *)
(*   real_le_b/real_eq 集合层谓词，无裸命题；六件 Print Assumptions Closed。 *)
(*                                                                *)
(* 形态差四维（供体 uabS4c_abs_sum_le_B_slot 为任意 S:Set＋抽象    *)
(*   sumf 的 B 形供给定理，值域为具体 Real——柯西序列 sigT 形）：   *)
(*   ①载体维：S06 语句以接口投影 @R RI 为载体（RealInterfaceEnhanced *)
(*     任意实例、le 字段不透明），供体载体为具体 Real；树内无     *)
(*     接口实例桥，且 S08 已判 Id 版接口不可实例化至 Real 层，     *)
(*     故 S06 语句的 @le RI 面不可由供体字面覆盖——本件＝          *)
(*     同语句形落在具体 Real 载体（|Σ f·q| ≤_B Σ |f|·q 逐位保持）； *)
(*   ②序维：接口 @le RI 不透明 vs real_le_b（Bishop 形，UpRealLeB） *)
(*     ——供体结论为可达最强形，接口面仅有单向桥；                 *)
(*   ③相等维：Id（接口）vs real_eq（逐 eps）——转换经 real_eq 运输； *)
(*   ④求和维：sum_over_S 类字段 vs 抽象 sumf——此维同构（算子形    *)
(*     一致、供体三前提对应 sum_over_S_ext/add/le），三前提显式量化。 *)
(*                                                                *)
(* 两处使用位处置：其一（abs_kernel_bound 形）全供给——            *)
(*   s6f_abs_kernel_bound_slot：供体在 g := f·q 上直接应用＋点态   *)
(*   转换（|x·q| ≡ |x|·q，q ≥_B 0：|q| ≡ q 逐 eps 尾部推进＋      *)
(*   Qabs_mult 恒等＋real_eq_mult_compat）＋sum_ext 求和面运输＋   *)
(*   B 形右端相等运输（s6f_leb_req_right，即 uabS4c_leb_req_left   *)
(*   的对偶命题，树内原缺，本件补齐）；其二                        *)
(*   （eviction_steady_deviation 形）零新增构造：S06 对 abs_sum_le *)
(*   的使用＝类字段裸应用（零特化），语句形供给＝供体本身；其余   *)
(*   差分改写/线性提出面为接口 Id 代数重述——不强行特化。          *)
(* 依赖：UpAblAbsSumLeB3（供体 uabS4c_ 系所在）＋CW_ConstructiveWorld_219 *)
(*   ＋UpRealLeB（real_le_b）＋S08_RealMainlineDPO。               *)
(* 对标：Bishop 构造性分析的求和算子与绝对值恒等（stdlib 无直接对应物）。 *)
(* 编译配方：Rocq 9.1 coqc 直调＋cpu_guard 包裹，输出经 -o 临时目录。 *)
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
(* §0 · 依赖签名核验（标识符漂移即编译期暴露） *)
(* ============================================================ *)

Check real_le_b.              (* UpRealLeB 的 Bishop 形 ≤（语句面谓词） *)
Check real_eq.                (* 逐 eps 相等（集合层） *)
Check real_abs.               (* 逐点 Qabs（CW 世界） *)
Check real_abs_proj.          (* 逐点投影 *)
Check real_mult.              (* 逐点乘法 *)
Check real_mult_proj.         (* 逐点投影（乘法） *)
Check real_const.             (* 常值实数 *)
Check real_const_proj.        (* 逐点投影（常值） *)
Check real_eq_trans.          (* 等式传递 *)
Check real_eq_refl.           (* 等式自反 *)
Check real_eq_of_zero_diff.   (* 逐点零差分 ⟹ real_eq *)
Check RealSetoid.real_eq_mult_compat. (* 乘法相等兼容 *)
Check uabS4c_abs_sum_le_B_slot. (* 主供给定理（End 后全称化） *)
Check uabS4c_abs_sum_le_eps_slot. (* 逐 eps 形供给（覆盖其二所需语句） *)
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
(* §A · 转换层（点态 abs 改写＋B 形右端相等运输）                       *)
(* ============================================================ *)

(* A.0 有理正性到实层的桥：0 < e（有理）⟹ real_lt real_zero (real_const e)。
   见证：半量 d := e·½，N := 0，逐点经 real_const_proj 投影即得 e。
   实作注记：lra 对 Q 除法失效，故半量一律写 ·(1#2) 乘法形。 *)
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
   思路：real_le_b 的预算取半（·(1#2) 乘法形）后取尾部（最终 q_n > −eps/2），
   对尾部二分：q_n < 0 情形 −2·q_n < eps；q_n ≥ 0 情形 Qabs q_n == q_n 零差。 *)
Lemma s6f_abs_nonneg_eq : forall q : Real,
  real_le_b real_zero q -> real_eq (real_abs q) q.
Proof.
  intros q Hq.
  unfold real_eq. intros eps0 Heps0.
  (* 预算取半量（·(1#2) 乘法形）：尾部 q_n > d0 − eps0/2 > −eps0/2，
     二分后 q_n<0 情形 −2·q_n < eps0、q_n≥0 情形零差 *)
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
   由 real_eq_of_zero_diff 化为逐点零差，再以 Qabs_mult 恒等收束（Q 层，无经典逻辑）。 *)
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

(* A.3 点态 abs 改写主引理（其一转换层核心）：0 ≤_B q ⟹ |x·q| ≡ |x|·q。
   链：|x·q| ≡ |x|·|q|（A.2）≡ |x|·q（A.1 加 RealSetoid.real_eq_mult_compat）。 *)
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

(* A.4 B 形右端相等运输（uabS4c_leb_req_left 的对偶命题，树内原缺，本件补齐）：
   a ≡ b 且 Y ≤_B a ⟹ Y ≤_B b。
   思路：预算 d 取半（h := d·½）——real_eq 在预算 h 上取 |a_n−b_n| < h 尾部，
   与 Y+a 侧预算 d 按 max 尾对齐，Q 层 lra 收束。 *)
Lemma s6f_leb_req_right : forall a b Y : Real,
  real_eq a b -> real_le_b Y a -> real_le_b Y b.
Proof.
  intros a b Y Hab HYa eps Heps.
  pose proof (HYa eps Heps) as HYa'.
  unfold real_le_b in HYa'. unfold real_lt in HYa'.
  destruct HYa' as [d [Hd [N1 HN1]]].
  (* 半量见证：h := d·½——等式预算恰取半量，于是 d−h = h，max 尾对齐后精确收束 *)
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
(* §B · 其一（abs_kernel_bound 形）的供给：同语句形的 B 层供给              *)
(*   （语句形逐位保持：|Σ f·q| ≤_B Σ |f|·q；载体＝具体 Real；               *)
(*     sumf 抽象＝任意 S:Set 求和算子，三前提＝供体定理前提的显式量化）      *)
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
  (* 供体 uabS4c_abs_sum_le_B_slot 在 g := f·q 上直接应用：|Σ f·q| ≤_B Σ |f·q| *)
  assert (Hdon : real_le_b (real_abs (sumf (fun s : S => real_mult (f s) (q s))))
                           (sumf (fun s : S => real_abs (real_mult (f s) (q s)))))
    by (apply (uabS4c_abs_sum_le_B_slot S sumf Hext Hadd Hleb)).
  (* 点态转换：|f s·q s| ≡ |f s|·q s（q s ≥_B 0） *)
  assert (Hpt : forall s : S, real_eq (real_abs (real_mult (f s) (q s)))
                                      (real_mult (real_abs (f s)) (q s)))
    by (intro s; apply s6f_abs_mult_eq; exact (Hq s)).
  (* 求和算子外延性运输（前提一 Hext） *)
  assert (Hsum : real_eq (sumf (fun s : S => real_abs (real_mult (f s) (q s))))
                         (sumf (fun s : S => real_mult (real_abs (f s)) (q s))))
    by (apply Hext; exact Hpt).
  (* B 形右端相等运输（本件 A.4） *)
  exact (s6f_leb_req_right _ _ _ Hsum Hdon).
Qed.

(* ============================================================ *)
(* §C · 其二（eviction_steady_deviation 形）：零新增构造的已证结论          *)
(*   S06 对 abs_sum_le 的使用＝类字段裸应用（零特化：abs_sum_le (fun s' => ...) *)
(*   原样应用），其语句形供给＝uabS4c_abs_sum_le_B_slot 本身（同语句覆盖，§0 已核验）； *)
(*   差分改写/线性提出面＝接口 Id 代数重述（不使用新供给）。不强行特化。      *)
(* ============================================================ *)

(* 假设审计：六件 Print Assumptions 全 Closed *)
Print Assumptions s6f_q_const_pos.
Print Assumptions s6f_abs_nonneg_eq.
Print Assumptions s6f_abs_abs_mult_eq.
Print Assumptions s6f_abs_mult_eq.
Print Assumptions s6f_leb_req_right.
Print Assumptions s6f_abs_kernel_bound_slot.
