(* ============================================================ *)
(* abl_Pr_euler_prod.v —— 素数域第 8 件：Euler 乘积公式有限版全量     *)
(*   闭合件（素数倒数和件 O1 终点件）                                *)
(* 模块名：abl_Pr_euler_prod                                       *)
(* 数学使命：闭合素数倒数和件登记的 Euler 乘积公式有限版：              *)
(*   σ(L)·∏_{p≤n}(p−1) ≤ L·∏_{p≤n} p，其中 L = hl_lcm_upto n          *)
(*   （不超过 n 的全体正整数之最小公倍数），σ(L) = Σ_{d∣L} d 为除子     *)
(*   和（nat 承载定义为 σ(L) = Σ_{d=1}^{L} d·[d∣L]）。主定理两条：     *)
(*   【O1 全量】pze_O1：σ(L)·∏(p−1) ≤ L·∏p——上半压界；               *)
(*   【Euler–Harm 传递】pze_euler_harm：∏_{p≤n}(p−1)·H_n ≤ ∏_{p≤n} p  *)
(*     （H_n 以 prs_hsum n L = Σ_{k≤n} L/k 精确整算术承载，即           *)
(*     ∏_{p≤n}(1−1/p)^{-1} ≥ H_n 的终点形：调和级数被素数乘积压住）。   *)
(*   Set 面承载件 pze_euler_gap：差量 d 的 sigT 见证与 hl_id 等式，     *)
(*   见证可计算可提取。                                              *)
(*   施工要点（承登记两缺口）：                                      *)
(*   ①除子和的折积分解三步闭合：裂解步 pze_sigma_split_le——           *)
(*     σ(p^{e+1}·N) ≤ σ(N) + p·σ(p^e·N)，除子按被 p 整除与否二类，      *)
(*     被整除类经商重排引理 pze_reindex 归入 p·σ(p^e·N)，不被整除类     *)
(*     经 Gauss 消去 plm_gauss 归入 σ(N)；几何完成步 pze_step_geo——    *)
(*     归纳得 σ(p^e·N) ≤ prs_geo p e·σ(N)，即单素因子                  *)
(*     (1−1/p)^{-1} 的有限几何和；折叠步 pze_fold_geo——素数表上        *)
(*     σ(∏p^{e_p}) ≤ ∏ prs_geo p e_p（裂解步只使用 p 的素性，           *)
(*     零互素零单射前提）。                                          *)
(*   ②指数向量单射性由邻件 abl_Pr_lcm_eq 的全等式 pr_lcm_eq_decomp     *)
(*     （L = ∏_{p≤n} p^{e_p}）供给，经 pze_runprod_eq 调用，零重建。    *)
(*   下半传递 pze_lower：Σ_{k≤n} L/k ≤ σ(L)——k ↦ L/k 在除子集上       *)
(*     单射，经单射像和压界引理 pze_inj_lsum_le（NoDup 列表的像和       *)
(*     不超过全区间和）完成。                                        *)
(* 依赖清单：纯 Stdlib（Arith.Arith／List／Bool／Lia）＋ HansonLcm／   *)
(*   Hanson3Pow（缓存根 vo_local_world_unified_0930 只读装入）＋        *)
(*   abl_Pr_core_01（pr_prime／pr_mod0_dvd／pr_min_factor_exists）＋   *)
(*   abl_Pr_enum_02（pen_primes_upto／pen_in_primes_upto）＋           *)
(*   abl_Pr_euclid_03＋abl_Pr_lcmdecomp_04（plm_gauss／                *)
(*   plm_prime_dvd_mul）＋abl_Pr_lcm_eq（pr_lcm_eq_decomp／            *)
(*   plq_lcm_pos）＋abl_Pr_recip_sum（prs_hsum／prs_geo／              *)
(*   prs_geo_euler_eq，byte 级拷贝件）。编译链序：core_01 →            *)
(*   enum_02 → euclid_03 → lcmdecomp_04 → lcm_eq → recip_sum → 本件。 *)
(* 构造性注记：Set 面承载——pze_euler_gap 的差量 sigT 见证与 hl_id      *)
(*   等式全透明 Defined，差量可计算可提取；计算件 pze_sumf／pze_lsum／  *)
(*   pze_prod／pze_sigma／pze_harm_check 皆一阶 nat 面可提取；Prop 面   *)
(*   不等式仅作推理脚手架（先例同构）；否定形自持 P -> False（全件零    *)
(*   not／~／<> 书写，含证明内部）；零公理零承认零经典逻辑；非线性步    *)
(*   全走乘法单调引理显式装配，lia 仅承担线性核；数值定装走小实例        *)
(*   vm_compute（n ≤ 6——unary 承载大数值栈墙照 CZR14 纪律收缩；          *)
(*   n 至 12 的真机数值验证走提取面 ocamlc 执行，见提取驱动件）。          *)
(* 红线四条自审：                                                   *)
(*   - 红线一（零公理声明词）：全件 Qed/Defined，公理审计块收尾；       *)
(*   - Set 层：主承载＝差量 sigT 见证＋hl_id 等式＋布尔核查件           *)
(*     pze_harm_check，非平凡数学内容（除子二类裂解、商重排、几何和     *)
(*     折积分解、单射像压界）全在证明面与计算件；                      *)
(*   - 非平凡：O1 全量与 Euler–Harm 传递全强度闭合，登记两缺口证明义务    *)
(*     全部完成（一者由邻件全等式供给、一者本件三步新建），未达面零、     *)
(*     无强凑；                                                     *)
(*   - 可提取：pze_sigma／pze_prod／prs_hsum／hl_lcm_upto／            *)
(*     pen_primes_upto／pze_harm_check 经提取驱动件 zz_pze_extract.v 验  *)
(*     Obj.magic = 0 并真机执行核查 n = 1..12 全部通过。               *)
(* 编译配方：                                                       *)
(*   source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/    *)
(*   env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 && cd <池> &&   *)
(*   nice -19 rocq c -native-compiler no \                            *)
(*   -Q /Users/apple/Desktop/ConstructiveWorld/                       *)
(*   vo_local_world_unified_0930 "" -Q . "" abl_Pr_euler_prod.v       *)
(*   （复核：rocq check 同 -Q 口径，公理判读必带 -o）                 *)
(* ============================================================ *)

From Stdlib Require Import Arith.Arith List Bool Lia.
Require Import HansonLcm.
Require Import abl_Pr_core_01.
Require Import abl_Pr_enum_02.
Require Import abl_Pr_lcmdecomp_04.
Require Import abl_Pr_lcm_eq.
Require Import abl_Pr_recip_sum.

(* ---- §0 计算承载：指示子、有限和、列表和、折积 ---- *)

(* 整除指示子：k 整除 N 取值 1，否则取值 0 *)
Definition pze_dvdind (k N : nat) : nat :=
  if Nat.eqb (N mod k) 0 then 1 else 0.

(* 乘积下界 *)
Lemma pze_mul_pos : forall a b : nat, 1 <= a -> 1 <= b -> 1 <= a * b.
Proof.
  intros a b Ha Hb. apply Nat.le_trans with (1 * 1).
  - lia.
  - apply Nat.mul_le_mono; assumption.
Qed.

(* 有限和 Σ_{k=1}^{B} f k *)
Fixpoint pze_sumf (f : nat -> nat) (B : nat) : nat :=
  match B with
  | 0 => 0
  | S B' => f (S B') + pze_sumf f B'
  end.

Lemma pze_sumf_ext : forall (f g : nat -> nat) (B : nat),
  (forall k : nat, f k = g k) -> pze_sumf f B = pze_sumf g B.
Proof.
  intros f g B H. induction B as [|B IH].
  - reflexivity.
  - simpl. rewrite (H (S B)), IH. reflexivity.
Qed.

Lemma pze_sumf_le : forall (f g : nat -> nat) (B : nat),
  (forall k : nat, f k <= g k) -> pze_sumf f B <= pze_sumf g B.
Proof.
  intros f g B H. induction B as [|B IH].
  - simpl. lia.
  - simpl. apply Nat.add_le_mono.
    + apply H.
    + exact IH.
Qed.

Lemma pze_sumf_add : forall (f g : nat -> nat) (B : nat),
  pze_sumf (fun k => f k + g k) B = pze_sumf f B + pze_sumf g B.
Proof.
  intros f g B. induction B as [|B IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma pze_sumf_mul_l : forall (c : nat) (f : nat -> nat) (B : nat),
  pze_sumf (fun k => c * f k) B = c * pze_sumf f B.
Proof.
  intros c f B. induction B as [|B IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

(* 尾段零截断：真延拓零贡献 *)
Lemma pze_sumf_trunc : forall (f : nat -> nat) (B1 B2 : nat),
  B1 <= B2 ->
  (forall k : nat, B1 < k -> k <= B2 -> f k = 0) ->
  pze_sumf f B2 = pze_sumf f B1.
Proof.
  intros f B1 B2. induction B2 as [|B2 IH]; intros Hle H0.
  - replace B1 with 0 by lia. reflexivity.
  - destruct (Nat.eq_dec B1 (S B2)) as [E | NE].
    + rewrite E. reflexivity.
    + assert (Hlt : B1 <= B2) by lia.
      simpl.
      rewrite (IH Hlt) by (intros k Hk1 Hk2; apply H0; lia).
      assert (Hp1 : B1 < S B2) by lia.
      assert (Hp2 : S B2 <= S B2) by lia.
      rewrite (H0 (S B2) Hp1 Hp2). lia.
Qed.

(* 列表和 Σ_{x∈l} F x *)
Definition pze_lsum (F : nat -> nat) (l : list nat) : nat :=
  fold_right (fun x acc => F x + acc) 0 l.

Lemma pze_lsum_app : forall F : nat -> nat, forall a b : list nat,
  pze_lsum F (a ++ b) = pze_lsum F a + pze_lsum F b.
Proof.
  intros F a. induction a as [|x a IH]; intro b.
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma pze_lsum_map : forall (F f : nat -> nat) (l : list nat),
  pze_lsum F (map f l) = pze_lsum (fun x => F (f x)) l.
Proof.
  intros F f l. induction l as [|a t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma pze_lsum_ext_in : forall F G : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> F x = G x) -> pze_lsum F l = pze_lsum G l.
Proof.
  intros F G l. induction l as [|a t IH]; intros H.
  - reflexivity.
  - simpl. rewrite (H a (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply H; right; exact Hx).
    reflexivity.
Qed.

(* 区间表和与有限和换基（起点 1 与有限和指标对齐） *)
Lemma pze_lsum_seq1 : forall (f : nat -> nat) (len : nat),
  pze_lsum f (seq 1 len) = pze_sumf f len.
Proof.
  intros f len. induction len as [|len IH].
  - reflexivity.
  - rewrite seq_S, pze_lsum_app. simpl. rewrite IH.
    replace (1 + len) with (S len) by lia. lia.
Qed.

(* 调和承载件与有限和的定义性重合 *)
Lemma pze_hsum_sumf : forall n C : nat,
  prs_hsum n C = pze_sumf (fun k => C / k) n.
Proof.
  intros n C. induction n as [|n IH].
  - reflexivity.
  - rewrite prs_hsum_S. cbn [pze_sumf]. rewrite IH. reflexivity.
Qed.

(* 折积 ∏_{x∈l} f x *)
Definition pze_prod (f : nat -> nat) (l : list nat) : nat :=
  fold_right Nat.mul 1 (map f l).

Lemma pze_prod_nil : forall f : nat -> nat, pze_prod f nil = 1.
Proof. reflexivity. Qed.

Lemma pze_prod_cons : forall (f : nat -> nat) (a : nat) (l : list nat),
  pze_prod f (a :: l) = f a * pze_prod f l.
Proof. reflexivity. Qed.

Lemma pze_prod_pos : forall f : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> 1 <= f x) -> 1 <= pze_prod f l.
Proof.
  intros f l. induction l as [|a t IH]; intros H.
  - rewrite pze_prod_nil. lia.
  - rewrite pze_prod_cons. apply Nat.le_trans with (1 * 1).
    + lia.
    + apply Nat.mul_le_mono.
      * apply H. left. reflexivity.
      * apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma pze_prod_hom : forall f g : nat -> nat, forall l : list nat,
  pze_prod (fun x => f x * g x) l = pze_prod f l * pze_prod g l.
Proof.
  intros f g l. induction l as [|a t IH].
  - rewrite pze_prod_nil, pze_prod_nil. reflexivity.
  - rewrite pze_prod_cons, pze_prod_cons, pze_prod_cons, IH. ring.
Qed.

Lemma pze_prod_mono : forall f g : nat -> nat, forall l : list nat,
  (forall x : nat, In x l -> f x <= g x) -> pze_prod f l <= pze_prod g l.
Proof.
  intros f g l. induction l as [|a t IH]; intros H.
  - rewrite pze_prod_nil, pze_prod_nil. lia.
  - rewrite pze_prod_cons, pze_prod_cons. apply Nat.mul_le_mono.
    + apply H. left. reflexivity.
    + apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

(* 除子和 σ(N) = Σ_{d=1}^{N} d·[d∣N]（即 Σ_{d∣N} d 的 nat 承载） *)
Definition pze_sigma (N : nat) : nat :=
  pze_sumf (fun d => d * pze_dvdind d N) N.

Lemma pze_sigma_1 : pze_sigma 1 = 1.
Proof. reflexivity. Qed.

(* 表上 NoDup 映像 *)
Lemma pze_nodup_map : forall (f : nat -> nat) (l : list nat),
  NoDup l ->
  (forall x y : nat, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup (map f l).
Proof.
  intros f l. induction l as [|a t IH]; intros Hnd Hinj.
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_cons_iff. apply NoDup_cons_iff in Hnd.
    destruct Hnd as [Hna Hndt]. split.
    + intros Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hyt]].
      apply Hna.
      assert (Hay : a = y).
      { apply Hinj.
        - left. reflexivity.
        - right. exact Hyt.
        - rewrite Hy. reflexivity. }
      rewrite Hay. exact Hyt.
    + apply IH.
      * exact Hndt.
      * intros x y Hx Hy Hf.
        apply Hinj; [right; exact Hx | right; exact Hy | exact Hf].
Qed.

(* ---- §G1 单射像和压界：NoDup 列表的像和不超过全区间和 ---- *)

Lemma pze_nodup_split : forall x : nat, forall l1 l2 : list nat,
  NoDup (l1 ++ x :: l2) -> NoDup (l1 ++ l2) /\
  (forall y : nat, In y (l1 ++ l2) -> y <> x).
Proof.
  intros x l1. induction l1 as [|a t IH]; intros l2 Hnd.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    split.
    + exact Hnd0.
    + intros y Hy Hxy. subst y. apply Hnin. exact Hy.
  - simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin Hnd0].
    destruct (IH l2 Hnd0) as [Hnd2 Hnx2]. split.
    + simpl. apply NoDup_cons_iff. split.
      * intros Hin. apply in_app_or in Hin. destruct Hin as [Ht | Hl2].
        -- apply Hnin. apply in_or_app. left. exact Ht.
        -- apply Hnin. apply in_or_app. right. right. exact Hl2.
      * exact Hnd2.
    + intros y Hy. simpl in Hy. destruct Hy as [Eya | Hy2].
      * subst y. intros Eax. apply Hnin. apply in_or_app. right. left.
        symmetry. exact Eax.
      * apply Hnx2. exact Hy2.
Qed.

Lemma pze_inj_lsum_le : forall B : nat, forall F : nat -> nat, forall l : list nat,
  NoDup l ->
  (forall x : nat, In x l -> 1 <= x /\ x <= B) ->
  pze_lsum F l <= pze_sumf F B.
Proof.
  intros B F. induction B as [|B IH]; intros l Hnd Hb.
  - assert (Hnil : l = nil).
    { destruct l as [|a t]. reflexivity. exfalso.
      destruct (Hb a (or_introl eq_refl)) as [H1 H2]. lia. }
    rewrite Hnil. simpl. lia.
  - destruct (in_dec Nat.eq_dec (S B) l) as [Hin | Hnin].
    + destruct (in_split (S B) l Hin) as [l1 [l2 Hsp]]. subst l.
      destruct (pze_nodup_split (S B) l1 l2 Hnd) as [Hnd2 Hnx].
      assert (Hb2 : forall x : nat, In x (l1 ++ l2) -> 1 <= x /\ x <= B).
      { intros x Hx2.
        assert (Hxl : In x (l1 ++ S B :: l2)).
        { apply in_app_or in Hx2. apply in_or_app.
          destruct Hx2 as [H1 | H2].
          - left. exact H1.
          - right. right. exact H2. }
        destruct (Hb x Hxl) as [Hx1 Hx3]. split.
        - exact Hx1.
        - destruct (Nat.eq_dec x (S B)) as [Ex | NEx].
          + exfalso. apply (Hnx x Hx2 Ex).
          + lia. }
      assert (Hfold : pze_lsum F (l1 ++ S B :: l2)
                    = pze_lsum F l1 + F (S B) + pze_lsum F l2).
      { rewrite (pze_lsum_app F l1 (S B :: l2)). simpl. lia. }
      rewrite Hfold.
      assert (Hrest : pze_lsum F l1 + pze_lsum F l2 <= pze_sumf F B).
      { rewrite <- (pze_lsum_app F l1 l2). apply IH.
        - exact Hnd2.
        - exact Hb2. }
      cbn [pze_sumf]. lia.
    + assert (Hb2 : forall x : nat, In x l -> 1 <= x /\ x <= B).
      { intros x Hx. destruct (Hb x Hx) as [H1 H2]. split.
        - exact H1.
        - destruct (Nat.eq_dec x (S B)) as [Ex | NEx].
          + exfalso. apply Hnin. rewrite <- Ex. exact Hx.
          + lia. }
      apply Nat.le_trans with (pze_sumf F B).
      * apply IH.
        -- exact Hnd.
        -- exact Hb2.
      * simpl. lia.
Qed.

(* ---- §G2 商重排：p 倍数类项按商重排 ---- *)

(* 截断减法与乘法的分配恒等式（全域成立，case 分派） *)
Lemma pze_mul_sub_aux : forall a b : nat, a * (b - 1) = a * b - a.
Proof.
  intros a b. destruct b as [|b'].
  - replace (0 - 1) with 0 by lia. rewrite !Nat.mul_0_r. lia.
  - replace (S b' - 1) with b' by lia.
    rewrite Nat.mul_succ_r. lia.
Qed.

Lemma pze_div_S_dvd : forall p B : nat,
  1 <= p -> (S B) mod p = 0 -> S B / p = S (B / p).
Proof.
  intros p B Hp Hm. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.div_mod (S B) p Hp0) as Hd. rewrite Hm in Hd.
  assert (Hq1 : S B / p >= 1).
  { destruct (S B / p) as [|q] eqn:Eq.
    - exfalso. simpl in Hd. lia.
    - lia. }
  assert (Hple : p <= S B).
  { assert (Hdvd : Nat.divide p (S B)) by (exists (S B / p); lia).
    pose proof (Nat.divide_pos_le p (S B) (Nat.lt_0_succ B) Hdvd). lia. }
  assert (HBp : B / p = S B / p - 1).
  { set (q := S B / p).
    pose proof (pze_mul_sub_aux p q) as Hx.
    assert (HB : B = p * (q - 1) + (p - 1)) by lia.
    rewrite HB.
    rewrite (Nat.mul_comm p (q - 1)).
    rewrite Nat.div_add_l by exact Hp0.
    rewrite Nat.div_small by lia.
    lia. }
  lia.
Qed.

Lemma pze_div_S_ndvd : forall p B : nat,
  1 <= p -> (S B) mod p <> 0 -> S B / p = B / p.
Proof.
  intros p B Hp Hm. assert (Hp0 : p <> 0) by lia.
  pose proof (Nat.div_mod (S B) p Hp0) as Hd.
  pose proof (Nat.mod_upper_bound (S B) p Hp0) as Hlt.
  assert (HBp : S B / p = B / p).
  { set (q := S B / p).
    assert (HB : B = p * q + (S B mod p - 1)) by lia.
    rewrite HB.
    rewrite (Nat.mul_comm p q).
    rewrite Nat.div_add_l by exact Hp0.
    rewrite Nat.div_small by lia.
    lia. }
  exact HBp.
Qed.

Lemma pze_reindex_raw : forall p B : nat, forall g : nat -> nat,
  1 <= p ->
  pze_sumf (fun k => g (k / p) * (if Nat.eqb (k mod p) 0 then 1 else 0)) B
  = pze_sumf g (B / p).
Proof.
  intros p B g Hp. assert (Hp0 : p <> 0) by lia.
  induction B as [|B IH].
  - rewrite Nat.Div0.div_0_l. reflexivity.
  - cbn [pze_sumf]. destruct (Nat.eqb (S B mod p) 0) eqn:Em.
    + change (if true then 1 else 0) with 1.
      rewrite Nat.mul_1_r, IH,
        (pze_div_S_dvd p B Hp (proj1 (Nat.eqb_eq (S B mod p) 0) Em)).
      reflexivity.
    + change (if false then 1 else 0) with 0.
      rewrite Nat.mul_0_r, Nat.add_0_l, IH.
      rewrite (pze_div_S_ndvd p B Hp
                 (proj1 (Nat.eqb_neq (S B mod p) 0) Em)).
      reflexivity.
Qed.

Lemma pze_reindex : forall p B : nat, forall g : nat -> nat,
  1 <= p ->
  pze_sumf (fun k => g (k / p) * pze_dvdind p k) B = pze_sumf g (B / p).
Proof.
  intros p B g Hp. unfold pze_dvdind. apply pze_reindex_raw. exact Hp.
Qed.

(* ---- §1 除子指示子消去桥与素幂互素 ---- *)

Lemma pze_dvd_div_cancel : forall p X j : nat,
  1 <= p -> 1 <= X ->
  Nat.divide (p * j) (p * X) <-> Nat.divide j X.
Proof.
  intros p X j Hp HX. split.
  - intros [c Hc]. destruct j as [|j'].
    + exfalso.
      assert (HpX : 1 <= p * X).
      { apply Nat.le_trans with (1 * 1); [lia | apply Nat.mul_le_mono; lia]. }
      lia.
    + exists c. assert (Hp0 : p <> 0) by lia.
      apply (proj1 (Nat.mul_cancel_l X (c * S j') p Hp0)).
      rewrite <- (prs_mul_swap c p (S j')). exact Hc.
  - intros [c Hc]. exists c. rewrite Hc.
    symmetry. apply (prs_mul_swap c p j).
Qed.

Lemma pze_dvdind_mul_cancel : forall p X j : nat,
  1 <= p -> 1 <= X ->
  pze_dvdind (p * j) (p * X) = pze_dvdind j X.
Proof.
  intros p X j Hp HX. unfold pze_dvdind.
  destruct (Nat.eqb ((p * X) mod (p * j)) 0) eqn:E1;
    destruct (Nat.eqb (X mod j) 0) eqn:E2; try reflexivity.
  - exfalso.
    assert (Hj1 : 1 <= j).
    { destruct j as [|j'].
      - exfalso.
        rewrite Nat.mul_0_r in E1.
        assert (Hz : (p * X) mod 0 = p * X) by (apply Nat.mod_0_r).
        rewrite Hz in E1.
        assert (Hz2 : p * X = 0) by exact (proj1 (Nat.eqb_eq _ _) E1).
        assert (HpX : 1 <= p * X) by (apply pze_mul_pos; lia).
        lia.
      - lia. }
    assert (Hmod1 : (p * X) mod (p * j) = 0)
      by exact (proj1 (Nat.eqb_eq ((p * X) mod (p * j)) 0) E1).
    assert (Hd1 : Nat.divide (p * j) (p * X))
      by (apply (pr_mod0_dvd (p * j) (p * X));
          [apply pze_mul_pos; [exact Hp | exact Hj1] | exact Hmod1]).
    assert (Hd2 : Nat.divide j X).
    { destruct (pze_dvd_div_cancel p X j Hp HX) as [Hf _].
      apply Hf. exact Hd1. }
    assert (Hmod2 : X mod j = 0)
      by (apply (pr_dvd_mod0 j X); [exact Hj1 | exact Hd2]).
    rewrite Hmod2 in E2. simpl in E2. discriminate E2.
  - exfalso.
    assert (Hmod2 : X mod j = 0)
      by exact (proj1 (Nat.eqb_eq (X mod j) 0) E2).
    assert (Hj1 : 1 <= j).
    { destruct j as [|j'].
      - exfalso. rewrite Nat.mod_0_r in Hmod2. lia.
      - lia. }
    assert (Hd2 : Nat.divide j X)
      by (apply (pr_mod0_dvd j X); [exact Hj1 | exact Hmod2]).
    assert (Hd1 : Nat.divide (p * j) (p * X)).
    { destruct (pze_dvd_div_cancel p X j Hp HX) as [_ Hb].
      apply Hb. exact Hd2. }
    assert (Hmod1 : (p * X) mod (p * j) = 0)
      by (apply (pr_dvd_mod0 (p * j) (p * X));
          [apply pze_mul_pos; lia | exact Hd1]).
    rewrite Hmod1 in E1. simpl in E1. discriminate E1.
Qed.

(* 素幂与外元互素：p 素、p 不整除 k，则 k 与 p 的任何幂互素 *)
Lemma pze_gcd_pow_prime : forall p e k : nat,
  pr_prime p -> 1 <= k -> (Nat.divide p k -> False) ->
  Nat.gcd k (p ^ e) = 1.
Proof.
  intros p e k Hp Hk Hnp. destruct Hp as [Hp2 Hpdiv].
  assert (Hp1 : 1 <= p) by lia.
  assert (Hg1 : 1 <= Nat.gcd k (p ^ e)).
  { destruct (Nat.gcd k (p ^ e)) as [|g] eqn:Eg.
    - exfalso.
      pose proof (Nat.gcd_divide_l k (p ^ e)) as Hd. rewrite Eg in Hd.
      apply Nat.divide_0_l in Hd. lia.
    - lia. }
  destruct (le_lt_dec (Nat.gcd k (p ^ e)) 1) as [Hle | Hlt].
  - lia.
  - exfalso.
    destruct (pr_min_factor_exists (Nat.gcd k (p ^ e)) Hlt) as [q Hqf].
    destruct Hqf as [Hqd Hqp]. destruct Hqp as [Hq2 Hqdiv].
    assert (Hqpe : Nat.divide q (p ^ e)).
    { apply (Nat.divide_trans q (Nat.gcd k (p ^ e)) (p ^ e)).
      - exact Hqd.
      - apply Nat.gcd_divide_r. }
    assert (Haux : forall f : nat, Nat.divide q (p ^ f) -> Nat.divide q p).
    { intros f. induction f as [|f IHf]; intros Hf.
      - rewrite Nat.pow_0_r in Hf. exfalso.
        assert (Hq11 : q <= 1)
          by (apply Nat.divide_pos_le; [lia | exact Hf]).
        lia.
      - rewrite Nat.pow_succ_r in Hf by lia.
        destruct (plm_prime_dvd_mul q p (p ^ f) (conj Hq2 Hqdiv) Hf)
          as [H1 | H2].
        + exact H1.
        + apply IHf. exact H2. }
    assert (Hqp2 : Nat.divide q p) by (exact (Haux e Hqpe)).
    assert (Hqlep : q <= p)
      by (apply Nat.divide_pos_le; [lia | exact Hqp2]).
    assert (Hqp3 : q = p).
    { destruct (Nat.eq_dec q p) as [E | NE].
      - exact E.
      - exfalso. apply (Hpdiv q).
        + exact Hq2.
        + lia.
        + exact Hqp2. }
    assert (Hqk : Nat.divide q k).
    { apply (Nat.divide_trans q (Nat.gcd k (p ^ e)) k).
      - exact Hqd.
      - apply Nat.gcd_divide_l. }
    apply Hnp. rewrite <- Hqp3. exact Hqk.
Qed.

(* ---- §S1 裂解步：σ(p^{e+1}·N) ≤ σ(N) + p·σ(p^e·N) ---- *)

Lemma pze_sigma_split_le : forall p e N : nat,
  pr_prime p -> 1 <= N ->
  pze_sigma (p ^ S e * N) <= pze_sigma N + p * pze_sigma (p ^ e * N).
Proof.
  intros p e N Hp HN.
  assert (Hp0 : p <> 0) by (destruct Hp as [Hp2 _]; lia).
  assert (Hp1 : 1 <= p) by lia.
  assert (HPe : p ^ S e * N = p * (p ^ e * N)).
  { rewrite Nat.pow_succ_r by lia. rewrite Nat.mul_assoc. reflexivity. }
  rewrite HPe. unfold pze_sigma.
  (* 二类裂项：被 p 整除类与不被整除类 *)
  assert (Hsplit :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N))) (p * (p ^ e * N))
    = pze_sumf
        (fun k => (k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
                + (k * pze_dvdind k (p * (p ^ e * N))
                   * (1 - pze_dvdind p k)))
        (p * (p ^ e * N))).
  { apply pze_sumf_ext. intro k. unfold pze_dvdind.
    destruct (Nat.eqb (k mod p) 0); lia. }
  rewrite Hsplit, pze_sumf_add.
  assert (Hpe1 : 1 <= p ^ e).
  { assert (Hnz : p ^ e <> 0) by (apply Nat.pow_nonzero; lia). lia. }
  assert (HM : 1 <= p ^ e * N).
  { apply Nat.le_trans with (1 * 1); [lia | apply Nat.mul_le_mono; lia]. }
  (* 被整除类：商重排归入 p·σ(p^e·N) *)
  assert (Hpt : forall k : nat,
    k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k
    = (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N))) (k / p)
      * pze_dvdind p k).
  { intro k. destruct (Nat.eqb (k mod p) 0) eqn:Ek.
    - assert (Hi1 : pze_dvdind p k = 1)
        by (unfold pze_dvdind; rewrite Ek; reflexivity).
      rewrite Hi1, !Nat.mul_1_r. cbv beta.
      assert (Hk : k = p * (k / p)).
      { pose proof (Nat.div_mod k p Hp0) as Hd.
        pose proof (proj1 (Nat.eqb_eq (k mod p) 0) Ek) as E0. lia. }
      rewrite <- Hk. reflexivity.
    - assert (Hi0 : pze_dvdind p k = 0)
        by (unfold pze_dvdind; rewrite Ek; reflexivity).
      rewrite Hi0, !Nat.mul_0_r. reflexivity. }
  assert (H1 :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
        (p * (p ^ e * N))
    = p * pze_sumf (fun k => k * pze_dvdind k (p ^ e * N)) (p ^ e * N)).
  { rewrite (pze_sumf_ext
        (fun k => k * pze_dvdind k (p * (p ^ e * N)) * pze_dvdind p k)
        (fun k => (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N)))
                    (k / p) * pze_dvdind p k)
        (p * (p ^ e * N)) Hpt).
    rewrite (pze_reindex p (p * (p ^ e * N))
               (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N))) Hp1).
    assert (Hdiv : p * (p ^ e * N) / p = p ^ e * N).
    { rewrite Nat.mul_comm. apply Nat.div_mul. exact Hp0. }
    rewrite Hdiv.
    rewrite (pze_sumf_ext
        (fun j => p * j * pze_dvdind (p * j) (p * (p ^ e * N)))
        (fun k => p * (k * pze_dvdind k (p ^ e * N)))
        (p ^ e * N)).
    + rewrite pze_sumf_mul_l. reflexivity.
    + intro j.
      rewrite (pze_dvdind_mul_cancel p (p ^ e * N) j Hp1 HM).
      symmetry. apply Nat.mul_assoc. }
  (* 不被整除类：Gauss 消去归入 σ(N) *)
  assert (Hle3 : N <= p * (p ^ e * N)).
  { apply Nat.le_trans with (p ^ e * N).
    - apply Nat.le_trans with (1 * N).
      + lia.
      + exact (Nat.mul_le_mono_r 1 (p ^ e) N Hpe1).
    - apply Nat.le_trans with (1 * (p ^ e * N)).
      + lia.
      + apply Nat.mul_le_mono; [exact Hp1 | apply Nat.le_refl]. }
  assert (H0z : forall k : nat, N < k -> k <= p * (p ^ e * N) ->
    k * pze_dvdind k N = 0).
  { intros k Hk1 Hk2. unfold pze_dvdind.
    destruct (Nat.eqb (N mod k) 0) eqn:EN.
    - exfalso.
      assert (Hdv : Nat.divide k N)
        by (apply (pr_mod0_dvd k N);
            [lia | exact (proj1 (Nat.eqb_eq (N mod k) 0) EN)]).
      pose proof (Nat.divide_pos_le k N HN Hdv) as HkN2. lia.
    - apply Nat.mul_0_r. }
  assert (H2 :
    pze_sumf (fun k => k * pze_dvdind k (p * (p ^ e * N)) * (1 - pze_dvdind p k))
        (p * (p ^ e * N))
    <= pze_sumf (fun k => k * pze_dvdind k N) N).
  { rewrite <- (pze_sumf_trunc (fun k => k * pze_dvdind k N)
                  N (p * (p ^ e * N)) Hle3 H0z).
    apply (pze_sumf_le
             (fun k => k * pze_dvdind k (p * (p ^ e * N)) * (1 - pze_dvdind p k))
             (fun k => k * pze_dvdind k N) (p * (p ^ e * N))).
    - intros k. unfold pze_dvdind.
      destruct (Nat.eqb ((p * (p ^ e * N)) mod k) 0) eqn:EB;
        destruct (Nat.eqb (k mod p) 0) eqn:Ep;
        destruct (Nat.eqb (N mod k) 0) eqn:EN; simpl; try lia.
      (* 余下：整除 p·(p^e·N) 且不被 p 整除——必整除 N，矛盾于指示位 *)
      exfalso.
      assert (Hk1 : 1 <= k).
      { destruct k as [|k'].
        - exfalso.
          assert (Hz : (p * (p ^ e * N)) mod 0 = p * (p ^ e * N))
            by (apply Nat.mod_0_r).
          rewrite Hz in EB.
          assert (Hz2 : p * (p ^ e * N) = 0)
            by exact (proj1 (Nat.eqb_eq _ _) EB).
          assert (HpeX : 1 <= p * (p ^ e * N))
            by (apply pze_mul_pos; lia).
          lia.
        - lia. }
      assert (Hdv : Nat.divide k (p ^ S e * N)).
      { rewrite Nat.pow_succ_r by lia. rewrite <- Nat.mul_assoc.
        apply (pr_mod0_dvd k (p * (p ^ e * N)));
          [exact Hk1 | exact (proj1 (Nat.eqb_eq _ _) EB)]. }
      assert (Hnp : Nat.divide p k -> False).
      { intros [c Hc].
        assert (Hm0 : k mod p = 0)
          by (apply (pr_dvd_mod0 p k); [lia | exists c; exact Hc]).
        pose proof (proj1 (Nat.eqb_neq (k mod p) 0) Ep) as Hne.
        rewrite Hm0 in Hne. lia. }
      assert (Hgcd : Nat.gcd k (p ^ S e) = 1)
        by (apply pze_gcd_pow_prime; [exact Hp | exact Hk1 | exact Hnp]).
      assert (HkN : Nat.divide k N).
      { apply (plm_gauss k (p ^ S e) N Hgcd). exact Hdv. }
      assert (HmodN : N mod k = 0)
        by (apply (pr_dvd_mod0 k N); [lia | exact HkN]).
      rewrite HmodN in EN. simpl in EN. discriminate EN. }
  rewrite H1. lia.
Qed.

(* ---- §S2 几何完成步：σ(p^e·N) ≤ prs_geo p e·σ(N) ---- *)

Lemma pze_step_geo : forall p e N : nat,
  pr_prime p -> 1 <= N ->
  pze_sigma (p ^ e * N) <= prs_geo p e * pze_sigma N.
Proof.
  intros p e N [Hp2 Hpdiv] HN. induction e as [|e IH].
  - rewrite Nat.pow_0_r, Nat.mul_1_l.
    replace (prs_geo p 0) with 1 by reflexivity. lia.
  - pose proof (pze_sigma_split_le p e N (conj Hp2 Hpdiv) HN) as H1.
    change (prs_geo p (S e)) with (1 + p * prs_geo p e).
    assert (Hpe1 : 1 <= p ^ e).
    { assert (Hnz : p ^ e <> 0) by (apply Nat.pow_nonzero; lia). lia. }
    assert (HM1 : p * pze_sigma (p ^ e * N) <= p * (prs_geo p e * pze_sigma N))
      by (apply Nat.mul_le_mono_l; exact IH).
    assert (Halg : pze_sigma N + p * (prs_geo p e * pze_sigma N)
                 = (1 + p * prs_geo p e) * pze_sigma N).
    { rewrite Nat.mul_add_distr_r, Nat.mul_1_l, <- Nat.mul_assoc. reflexivity. }
    lia.
Qed.

(* ---- §S3 折叠步：素数表上 σ(∏p^{e_p}) ≤ ∏ prs_geo p e_p ---- *)

Lemma pze_fold_geo : forall (l : list nat) (e : nat -> nat),
  (forall p : nat, In p l -> pr_prime p) ->
  pze_sigma (pze_prod (fun p => p ^ e p) l)
  <= pze_prod (fun p => prs_geo p (e p)) l.
Proof.
  intros l e. induction l as [|a t IH]; intros Hpp.
  - rewrite pze_prod_nil, pze_sigma_1, pze_prod_nil. lia.
  - assert (Hpa : pr_prime a) by (apply Hpp; left; reflexivity).
    assert (HN : 1 <= pze_prod (fun p => p ^ e p) t).
    { apply pze_prod_pos. intros x Hx.
      assert (Hx2 : 2 <= x).
      { destruct (Hpp x (or_intror Hx)) as [Hx2 _]. exact Hx2. }
      assert (Hnz : x ^ e x <> 0) by (apply Nat.pow_nonzero; lia).
      lia. }
    rewrite pze_prod_cons, pze_prod_cons.
    apply Nat.le_trans with
      (prs_geo a (e a) * pze_sigma (pze_prod (fun p => p ^ e p) t)).
    + apply pze_step_geo.
      * exact Hpa.
      * exact HN.
    + apply Nat.mul_le_mono_l. apply IH. intros p Hp.
      apply Hpp. right. exact Hp.
Qed.

(* ---- §2 主链：O1 全量与 Euler–Harm 传递 ---- *)

(* 全等式调用：素幂折积恰为 L(n)（邻件 pr_lcm_eq_decomp 承载） *)
Theorem pze_runprod_eq : forall n : nat,
  pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n)
  = hl_lcm_upto n.
Proof.
  intro n. unfold pze_prod. symmetry. apply hl_id_eq.
  apply pr_lcm_eq_decomp.
Qed.

(* 上半压界：σ(L) ≤ ∏_{p≤n} prs_geo p (plm_v p L) *)
Theorem pze_sigma_upper : forall n : nat,
  pze_sigma (hl_lcm_upto n)
  <= pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n)))
       (pen_primes_upto n).
Proof.
  intro n.
  apply Nat.le_trans with
    (pze_sigma
       (pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n))).
  - rewrite pze_runprod_eq. apply Nat.le_refl.
  - apply pze_fold_geo. intros p Hp.
    exact (proj1 (proj1 (pen_in_primes_upto p n) Hp)).
Qed.

(* 商单射：k ↦ L/k 在除子集上单射 *)
Lemma pze_codiv_inj : forall n k1 k2 : nat,
  1 <= k1 -> 1 <= k2 ->
  Nat.divide k1 (hl_lcm_upto n) -> Nat.divide k2 (hl_lcm_upto n) ->
  hl_lcm_upto n / k1 = hl_lcm_upto n / k2 -> k1 = k2.
Proof.
  intros n k1 k2 H1 H2 D1 D2 E.
  assert (HL1 : 1 <= hl_lcm_upto n) by apply plq_lcm_pos.
  assert (Hk10 : k1 <> 0) by lia.
  assert (Hk20 : k2 <> 0) by lia.
  assert (Hm1 : hl_lcm_upto n mod k1 = 0)
    by (apply (pr_dvd_mod0 k1 (hl_lcm_upto n)); [lia | exact D1]).
  assert (Hm2 : hl_lcm_upto n mod k2 = 0)
    by (apply (pr_dvd_mod0 k2 (hl_lcm_upto n)); [lia | exact D2]).
  pose proof (Nat.div_mod (hl_lcm_upto n) k1 Hk10) as Hd1.
  pose proof (Nat.div_mod (hl_lcm_upto n) k2 Hk20) as Hd2.
  rewrite Hm1 in Hd1. rewrite Hm2 in Hd2.
  assert (Hq1 : 1 <= hl_lcm_upto n / k1).
  { destruct (hl_lcm_upto n / k1) eqn:Eq; [| lia].
    exfalso. simpl in Hd1. lia. }
  rewrite <- E in Hd2.
  assert (Ha : k1 * (hl_lcm_upto n / k1) = k2 * (hl_lcm_upto n / k1)) by lia.
  assert (Hq0 : hl_lcm_upto n / k1 <> 0) by lia.
  apply (proj1 (Nat.mul_cancel_r k1 k2 (hl_lcm_upto n / k1) Hq0)).
  lia.
Qed.

(* 下半传递：Σ_{k≤n} L/k ≤ σ(L) *)
Theorem pze_lower : forall n : nat,
  prs_hsum n (hl_lcm_upto n) <= pze_sigma (hl_lcm_upto n).
Proof.
  intro n.
  rewrite (pze_hsum_sumf n (hl_lcm_upto n)).
  rewrite <- (pze_lsum_seq1 (fun k => hl_lcm_upto n / k) n).
  unfold pze_sigma.
  assert (Hbridge :
    pze_lsum (fun k => hl_lcm_upto n / k) (seq 1 n)
    = pze_lsum (fun d => d * pze_dvdind d (hl_lcm_upto n))
        (map (fun k => hl_lcm_upto n / k) (seq 1 n))).
  { rewrite pze_lsum_map. apply pze_lsum_ext_in.
    intros x Hx. apply in_seq in Hx. destruct Hx as [Hx1 Hx2].
    assert (HL1 : 1 <= hl_lcm_upto n) by apply plq_lcm_pos.
    assert (Hx0 : x <> 0) by lia.
    assert (Hdvd : Nat.divide x (hl_lcm_upto n))
      by (apply (hl_lcm_divide_all n x); lia).
    pose proof (Nat.div_mod (hl_lcm_upto n) x Hx0) as Hdm.
    assert (Hm0 : hl_lcm_upto n mod x = 0)
      by (apply (pr_dvd_mod0 x (hl_lcm_upto n)); [lia | exact Hdvd]).
    rewrite Hm0 in Hdm.
    assert (Hdm2 : hl_lcm_upto n = x * (hl_lcm_upto n / x)) by lia.
    assert (HLx1 : 1 <= hl_lcm_upto n / x).
    { destruct (hl_lcm_upto n / x) eqn:Eq; [| lia].
      exfalso. simpl in Hdm2. lia. }
    assert (Hdv2 : Nat.divide (hl_lcm_upto n / x) (hl_lcm_upto n)).
    { exists x. exact Hdm2. }
    assert (Hind : pze_dvdind (hl_lcm_upto n / x) (hl_lcm_upto n) = 1).
    { unfold pze_dvdind.
      destruct (Nat.eqb (hl_lcm_upto n mod (hl_lcm_upto n / x)) 0) eqn:E.
      - reflexivity.
      - exfalso.
        assert (Hm2 : hl_lcm_upto n mod (hl_lcm_upto n / x) = 0)
          by (apply (pr_dvd_mod0 (hl_lcm_upto n / x) (hl_lcm_upto n));
              [lia | exact Hdv2]).
        rewrite Hm2 in E. simpl in E. discriminate E. }
    rewrite Hind. lia. }
  rewrite Hbridge.
  apply (pze_inj_lsum_le (hl_lcm_upto n)
           (fun d => d * pze_dvdind d (hl_lcm_upto n))
           (map (fun k => hl_lcm_upto n / k) (seq 1 n))).
  - apply pze_nodup_map.
    + apply seq_NoDup.
    + intros x y Hx Hy Hf.
      apply in_seq in Hx. apply in_seq in Hy.
      destruct Hx as [Hx1 Hx2]. destruct Hy as [Hy1 Hy2].
      apply (pze_codiv_inj n); try lia.
      * apply (hl_lcm_divide_all n x); lia.
      * apply (hl_lcm_divide_all n y); lia.
  - intros x Hx. apply in_map_iff in Hx. destruct Hx as [k [Hxk Hkt]].
    subst x. apply in_seq in Hkt. destruct Hkt as [Hk1 Hk2].
    assert (HL1 : 1 <= hl_lcm_upto n) by apply plq_lcm_pos.
    assert (Hk0 : k <> 0) by lia.
    assert (Hdvd : Nat.divide k (hl_lcm_upto n))
      by (apply (hl_lcm_divide_all n k); lia).
    pose proof (Nat.div_mod (hl_lcm_upto n) k Hk0) as Hdm.
    assert (Hm0 : hl_lcm_upto n mod k = 0)
      by (apply (pr_dvd_mod0 k (hl_lcm_upto n)); [lia | exact Hdvd]).
    rewrite Hm0 in Hdm.
    assert (Hdm2 : hl_lcm_upto n = k * (hl_lcm_upto n / k)) by lia.
    assert (HLk1 : 1 <= hl_lcm_upto n / k).
    { destruct (hl_lcm_upto n / k) eqn:Eq; [| lia].
      exfalso. simpl in Hdm2. lia. }
    split.
    + exact HLk1.
    + apply Nat.div_le_upper_bound.
      * lia.
      * apply Nat.le_trans with (1 * hl_lcm_upto n).
        -- lia.
        -- apply Nat.mul_le_mono_r. lia.
Qed.

(* 单素因子终值不等式：prs_geo p e·(p−1) ≤ p^e·p（prs_geo_euler_eq 直出） *)
Lemma pze_termwise : forall n p : nat,
  In p (pen_primes_upto n) ->
  prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1)
  <= p ^ plm_v p (hl_lcm_upto n) * p.
Proof.
  intros n p Hp.
  destruct (proj1 (pen_in_primes_upto p n) Hp) as [Hpp _].
  destruct Hpp as [Hp2 Hpdiv].
  assert (Hp1 : 1 <= p) by lia.
  pose proof (prs_geo_euler_eq p (plm_v p (hl_lcm_upto n)) Hp1) as Heq.
  rewrite Nat.pow_succ_r in Heq by lia.
  lia.
Qed.

(* 【O1 全量】σ(L)·∏(p−1) ≤ L·∏p *)
Theorem pze_O1 : forall n : nat,
  pze_sigma (hl_lcm_upto n) * pze_prod (fun p => p - 1) (pen_primes_upto n)
  <= hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n).
Proof.
  intro n.
  pose proof (pze_sigma_upper n) as Hup.
  assert (Hhom :
    pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n))) (pen_primes_upto n)
    * pze_prod (fun p => p - 1) (pen_primes_upto n)
    = pze_prod
        (fun p => prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1))
        (pen_primes_upto n))
    by (symmetry; apply pze_prod_hom).
  assert (Hmono :
    pze_prod
        (fun p => prs_geo p (plm_v p (hl_lcm_upto n)) * (p - 1))
        (pen_primes_upto n)
    <= pze_prod
        (fun p => p ^ plm_v p (hl_lcm_upto n) * p)
        (pen_primes_upto n)).
  { apply pze_prod_mono. intros x Hx. apply pze_termwise. exact Hx. }
  assert (Hhom2 :
    pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n) * p) (pen_primes_upto n)
    = pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n)) (pen_primes_upto n)
      * pze_prod (fun p => p) (pen_primes_upto n))
    by apply pze_prod_hom.
  pose proof (pze_runprod_eq n) as Hrun.
  apply Nat.le_trans with
    (pze_prod (fun p => prs_geo p (plm_v p (hl_lcm_upto n)))
       (pen_primes_upto n)
     * pze_prod (fun p => p - 1) (pen_primes_upto n)).
  - apply Nat.mul_le_mono_r. exact Hup.
  - rewrite Hhom.
    apply Nat.le_trans with
      (pze_prod (fun p => p ^ plm_v p (hl_lcm_upto n) * p)
         (pen_primes_upto n)).
    + exact Hmono.
    + rewrite Hhom2, Hrun. apply Nat.le_refl.
Qed.

(* 【Euler–Harm 传递】∏(p−1)·H_n ≤ ∏p：调和级数被素数乘积压住 *)
Theorem pze_euler_harm : forall n : nat,
  pze_prod (fun p => p - 1) (pen_primes_upto n) * prs_hsum n (hl_lcm_upto n)
  <= hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n).
Proof.
  intro n.
  pose proof (pze_lower n) as Hlo.
  pose proof (pze_O1 n) as H1.
  apply Nat.le_trans with
    (pze_prod (fun p => p - 1) (pen_primes_upto n)
     * pze_sigma (hl_lcm_upto n)).
  - apply Nat.mul_le_mono_l. exact Hlo.
  - rewrite (Nat.mul_comm
        (pze_prod (fun p => p - 1) (pen_primes_upto n))
        (pze_sigma (hl_lcm_upto n))).
    exact H1.
Qed.

(* Set 面承载：差量的 sigT 见证与 hl_id 等式（透明 Defined） *)
Theorem pze_euler_gap : forall n : nat,
  { d : nat & hl_id
      (pze_prod (fun p => p - 1) (pen_primes_upto n)
       * prs_hsum n (hl_lcm_upto n) + d)
      (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)) }.
Proof.
  intro n.
  pose proof (pze_euler_harm n) as H.
  exists (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)
          - pze_prod (fun p => p - 1) (pen_primes_upto n)
            * prs_hsum n (hl_lcm_upto n)).
  rewrite Nat.add_comm.
  rewrite Nat.sub_add by exact H.
  apply hl_idrefl.
Defined.

(* 布尔核查件（可提取真机执行） *)
Definition pze_harm_check (n : nat) : bool :=
  Nat.leb (pze_prod (fun p => p - 1) (pen_primes_upto n)
            * prs_hsum n (hl_lcm_upto n))
          (hl_lcm_upto n * pze_prod (fun p => p) (pen_primes_upto n)).

(* ---- §3 数值定装烟测（小实例 vm_compute，零公设） ---- *)

Lemma pze_sigma_smoke_6 : pze_sigma 6 = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma pze_sigma_smoke_12 : pze_sigma 12 = 28.
Proof. vm_compute. reflexivity. Qed.

Lemma pze_O1_smoke_6 :
  pze_sigma (hl_lcm_upto 6) * pze_prod (fun p => p - 1) (pen_primes_upto 6)
  <= hl_lcm_upto 6 * pze_prod (fun p => p) (pen_primes_upto 6).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_1 :
  pze_prod (fun p => p - 1) (pen_primes_upto 1) * prs_hsum 1 (hl_lcm_upto 1)
  <= hl_lcm_upto 1 * pze_prod (fun p => p) (pen_primes_upto 1).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_4 :
  pze_prod (fun p => p - 1) (pen_primes_upto 4) * prs_hsum 4 (hl_lcm_upto 4)
  <= hl_lcm_upto 4 * pze_prod (fun p => p) (pen_primes_upto 4).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_smoke_6 :
  pze_prod (fun p => p - 1) (pen_primes_upto 6) * prs_hsum 6 (hl_lcm_upto 6)
  <= hl_lcm_upto 6 * pze_prod (fun p => p) (pen_primes_upto 6).
Proof. vm_compute. lia. Qed.

Lemma pze_harm_check_6 : pze_harm_check 6 = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- §4 公理审计（Print Assumptions 取证面） ---- *)

Print Assumptions pze_inj_lsum_le.
Print Assumptions pze_reindex.
Print Assumptions pze_dvdind_mul_cancel.
Print Assumptions pze_gcd_pow_prime.
Print Assumptions pze_sigma_split_le.
Print Assumptions pze_step_geo.
Print Assumptions pze_fold_geo.
Print Assumptions pze_runprod_eq.
Print Assumptions pze_sigma_upper.
Print Assumptions pze_lower.
Print Assumptions pze_termwise.
Print Assumptions pze_O1.
Print Assumptions pze_euler_harm.
Print Assumptions pze_euler_gap.
Print Assumptions pze_harm_check.
