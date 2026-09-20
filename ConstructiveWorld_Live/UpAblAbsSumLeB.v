(* ============================================================ *)
(* UpAblAbsSumLeB.v —— abs_sum_le 族（族I 墙）可达最强形供给件        *)
(*                                                                *)
(* 席位：S4（TW1ATK 冻结现态续攻席）· 20260920                       *)
(* 零承认件：无承认词面、无假设槽位声明、无经典逻辑、全件 Qed 闭合。 *)
(*   全部语句 Set 层值（real_le/real_lt/real_eq/real_le_b 均 Set），  *)
(*   语句面无裸「命题层」；证明全构造（Or 逐支、sigT 见证直构）。       *)
(*                                                                *)
(* 定谳（本件头注即定谳正文）：                                      *)
(*   族I 墙（abs_sum_le plain Or 形，UpReqSampling:116/:719 槽）     *)
(*   的可达最强形 = Bishop B 形（real_le_b，UpRealLeB:72）：          *)
(*   ① B 形严格强于逐 eps 形（real_le_closure_b_one 单步闭包）；      *)
(*   ② 逐 eps 形经 Or-inl 支直供（real_lt_le_iff_req 左注入）；       *)
(*   ③ plain Or 形不可达（E751 判词维持，本件不触碰）。               *)
(*                                                                *)
(* 三件供给（全部新独立件，非平凡构造）：                              *)
(*   A 两点核差形：|a−c| ≤ (|a−b|+|b−c|)+eps 逐 eps（Or-inl）        *)
(*      ＋ B 形——差缝合 eq 链（assoc/opp/zero 五步）＋三角实例；      *)
(*   B list 折叠形：real_list_sum 折叠三角——归纳承载两点核＋          *)
(*      误差账目（§9.3 口径：单点引入=每步一整单位 e；常数加权=       *)
(*      权函数 W(l)（W(nil)=1，W(cons)=W(rest)+1）线性记账；          *)
(*      末端完成=real_le_closure_b 以 W(l) 显式正性证书升 B 形），    *)
(*      ＋ B 形⟹逐 eps 形回收（inl 注入）；                          *)
(*   C eps₀/2 双杀引理（TW1ATK 发现②定理化）：余量倍率 2 杀——        *)
(*      real_lt (Y+2e) X 与 real_le X (Y+e) 不可能共存（lt 支        *)
(*      传递自撞＋eq 支运输自撞，共用 irrefl 引爆）。                 *)
(*                                                                *)
(* 依赖：CW_ConstructiveWorld_219＋UpRealLeB（同代）＋               *)
(*   S08_RealMainlineDPO（real_list_sum，0916 代在档）。             *)
(* ============================================================ *)

From Stdlib Require Import List.
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import S08_RealMainlineDPO.

(* ============================================================ *)
(* Part 0 · 冻结现态复刻：武器在库打表（签名漂移即 fail-loud）          *)
(* ============================================================ *)

Check real_le_b.              (* UpRealLeB:72  Bishop 形 ≤（可达最强形谓词） *)
Check real_le_closure_b_one.  (* 逐 eps 完成为 B 形（单步闭包） *)
Check real_le_closure_b.      (* D 带证书加权完成（末端完成机） *)
Check real_abs_triangle_le_B. (* |a+b| ≤_B |a|+|b|（TW1ATK 发现一实锚） *)
Check real_abs_triangle_le_eps. (* |a+b| ≤ (|a|+|b|)+eps 逐 eps（两点核实锚） *)
Check real_lt_zero_one.       (* 0 < 1（W(nil) 正性证书） *)
Check real_lt_plus_r_zero.    (* y < y+eps（UpRealLeB:81） *)
Check real_list_sum.          (* S08:288 折叠机器（X 全称） *)
Check RealSetoid.real_eq_abs_compat. (* abs 尊重 real_eq *)
Check real_abs_zero_req.      (* |0| ≡ 0 *)
Check real_lt_irrefl.         (* 反自反（双杀引爆器） *)

(* ============================================================ *)
(* Part A · 缝合基件：正余量右吸收 ＋ 差形两点核                       *)
(* ============================================================ *)

(* 基件：le a b ＋ 0 < c ⟹ le a (b+c)（正余量右吸收）。
   构造：Or 两支分别 lt 传递（b < b+c 经 (b+0) 换形平移）
   ／eq 支运输后同链；统一经 real_lt_le_iff_req 左注入收束。 *)
Lemma uabS4_le_add_r : forall a b c : Real,
  real_le a b -> real_lt real_zero c -> real_le a (real_plus b c).
Proof.
  intros a b c Hab Hc.
  apply (RealSetoid.real_lt_le_iff_req a (real_plus b c)). apply inl.
  destruct Hab as [Hab | Hab].
  - apply (real_lt_trans a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
  - apply (RealSetoid.real_lt_id_l a b (real_plus b c)).
    + exact Hab.
    + apply (RealSetoid.real_lt_id_l b (real_plus b real_zero) (real_plus b c)).
      * apply real_eq_sym. apply real_plus_zero.
      * apply (real_lt_plus_translate b real_zero c). exact Hc.
Qed.

(* A.1 两点核差形（逐 eps，Or-inl）：|a−c| ≤ (|a−b|+|b−c|)+eps。
   构造：差缝合 eq 链 (a−b)+(b−c) ≡ a−c（assoc×2＋opp＋zero 五步，
   逐槽 real_eq_plus_compat 运输），abs 尊重 eq 后两点核三角实例直喂。 *)
Lemma uabS4_abs_diff_triangle_le_eps : forall a b c e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a (real_opp c)))
          (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                (real_abs (real_plus b (real_opp c)))) e).
Proof.
  intros a b c e He.
  assert (Hdiff : real_eq (real_plus (real_plus a (real_opp b))
                                     (real_plus b (real_opp c)))
                          (real_plus a (real_opp c))).
  { eapply real_eq_trans.
    - apply real_eq_sym. apply real_plus_assoc.
    - apply (RealSetoid.real_eq_plus_compat a
               (real_plus (real_opp b) (real_plus b (real_opp c))) a
               (real_opp c)).
      + apply real_eq_refl.
      + eapply real_eq_trans.
        * apply real_plus_assoc.
        * eapply real_eq_trans.
          -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                          (real_opp c) real_zero (real_opp c)).
             ++ apply (real_eq_trans _ _ _ (real_plus_comm (real_opp b) b)).
                apply real_plus_opp.
             ++ apply real_eq_refl.
          -- apply (real_eq_trans _ _ _ (real_plus_comm real_zero (real_opp c))).
             apply real_plus_zero. }
  apply (RealSetoid.real_le_id_l _ _ _
           (RealSetoid.real_eq_abs_compat _ _
              (real_eq_sym (real_plus (real_plus a (real_opp b))
                                      (real_plus b (real_opp c)))
                           (real_plus a (real_opp c)) Hdiff))).
  exact (real_abs_triangle_le_eps (real_plus a (real_opp b))
                                  (real_plus b (real_opp c)) e He).
Qed.

(* A.2 两点核差形（B 形，可达最强形）：|a−c| ≤_B |a−b|+|b−c|。 *)
Theorem uabS4_abs_diff_triangle_le_B : forall a b c : Real,
  real_le_b (real_abs (real_plus a (real_opp c)))
            (real_plus (real_abs (real_plus a (real_opp b)))
                       (real_abs (real_plus b (real_opp c)))).
Proof.
  intros a b c. apply real_le_closure_b_one. intros e He.
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* A.3 族I 墙最小非平凡实例（S:=bool 两点世界）B 形直供
   （TW1ATK 试钉3 收编定谳：两点=族I 墙的最小非平凡世界）。 *)
Theorem uabS4_abs_sum_le_B_pair : forall f : bool -> Real,
  real_le_b (real_abs (real_plus (f true) (f false)))
            (real_plus (real_abs (f true)) (real_abs (f false))).
Proof.
  intros f. exact (real_abs_triangle_le_B (f true) (f false)).
Qed.

(* ============================================================ *)
(* Part B · list 折叠形：加权归纳（§9.3 误差账目）＋末端完成            *)
(* ============================================================ *)

(* 权函数：W(nil)=1，W(w::rest)=W(rest)+1（定义性尾权 +1）。
   误差账目：单点引入每步耗一整单位 e，尾权 W(rest)·e 承接，
   合计 (W(rest)+1)·e ≡ W(cons)·e——账目逐级严格守恒。 *)
Fixpoint uabS4_wlen (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_one
  | w :: rest => real_plus (uabS4_wlen X rest) real_one
  end.

(* 权正性证书：0 < W(l)（归纳：1 > 0；W(rest) > 0 平移至 W(rest)+1）。 *)
Lemma uabS4_wlen_pos : forall (X : Type) (l : list X),
  real_lt real_zero (uabS4_wlen X l).
Proof.
  intros X l. induction l as [| w rest IH].
  - exact real_lt_zero_one.
  - apply (real_lt_trans real_zero (uabS4_wlen X rest)
             (real_plus (uabS4_wlen X rest) real_one)).
    + exact IH.
    + apply real_lt_plus_r_zero. exact real_lt_zero_one.
Qed.

(* 缝合引理（折叠归纳的 cons 一步）：
   两点核（单点引入，余量 e 整单位）＋尾余量（w·e 加权承接）
   ⟹ 折叠目标余量 (w+1)·e。
   构造：real_le_plus_compat 桥接＋assoc×3＋distrib/mult_one
   终运输 eq 链（(w+1)·e ≡ w·e + e ≡ w·e + e 逐槽缝合）。 *)
Lemma uabS4_cons_glue : forall a s t w e : Real,
  real_lt real_zero e ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) (real_abs s)) e) ->
  real_le (real_abs s) (real_plus t (real_mult w e)) ->
  real_le (real_abs (real_plus a s))
          (real_plus (real_plus (real_abs a) t)
                     (real_mult (real_plus w real_one) e)).
Proof.
  intros a s t w e He Hpair Hih.
  assert (Hmid : real_le (real_plus (real_abs a) (real_abs s))
                         (real_plus (real_abs a) (real_plus t (real_mult w e)))).
  { apply (real_le_plus_compat (real_abs a) (real_abs a)
             (real_abs s) (real_plus t (real_mult w e))).
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl (real_abs a))).
    - exact Hih. }
  assert (Hstep : real_le (real_plus (real_plus (real_abs a) (real_abs s)) e)
                          (real_plus (real_plus (real_abs a)
                                     (real_plus t (real_mult w e))) e)).
  { apply (real_le_plus_compat _ _ e e).
    - exact Hmid.
    - exact (RealSetoid.real_eq_le _ _ (real_eq_refl e)). }
  assert (Hchain : real_le (real_abs (real_plus a s))
                           (real_plus (real_plus (real_abs a)
                                      (real_plus t (real_mult w e))) e)).
  { apply (real_le_trans _ _ _ Hpair Hstep). }
  apply (RealSetoid.real_le_id_r (real_abs (real_plus a s))
           (real_plus (real_plus (real_abs a) (real_plus t (real_mult w e))) e)
           (real_plus (real_plus (real_abs a) t)
                      (real_mult (real_plus w real_one) e))).
  - eapply real_eq_trans.
    + apply real_eq_sym. apply real_plus_assoc.
    + eapply real_eq_trans.
      * apply (RealSetoid.real_eq_plus_compat (real_abs a)
                   (real_plus (real_plus t (real_mult w e)) e) (real_abs a)
                   (real_plus t (real_plus (real_mult w e) e))).
        -- apply real_eq_refl.
        -- apply real_eq_sym. apply real_plus_assoc.
      * eapply real_eq_trans.
        -- apply real_plus_assoc.
        -- apply (RealSetoid.real_eq_plus_compat (real_plus (real_abs a) t)
                        (real_plus (real_mult w e) e)
                        (real_plus (real_abs a) t)
                        (real_mult (real_plus w real_one) e)).
           ++ apply real_eq_refl.
           ++ apply real_eq_sym.
              apply (real_eq_trans _ _ _
                       (real_mult_comm (real_plus w real_one) e)).
              apply (real_eq_trans _ _ _ (real_distrib e w real_one)).
              apply (RealSetoid.real_eq_plus_compat (real_mult e w)
                          (real_mult e real_one) (real_mult w e) e).
              ** apply real_mult_comm.
              ** apply real_mult_one.
  - exact Hchain.
Qed.

(* B.1 加权归纳主体（逐 eps 形·权函数记账）：|Σ_l f| ≤ Σ_l|f| + W(l)·e。
   nil：|0| ≡ 0 ≤ 0 + 1·e（正余量右吸收）；cons：两点核整单位喂入
   ＋尾 IH 同权承接＋缝合引理收束。 *)
Lemma uabS4_abs_list_sum_le_wt : forall (X : Type) (f : X -> Real) (l : list X)
                                        (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l)
                     (real_mult (uabS4_wlen X l) e)).
Proof.
  intros X f l. induction l as [| w rest IH]; intro e; intro He.
  - apply (uabS4_le_add_r (real_abs (real_list_sum X f nil)) real_zero
             (real_mult (uabS4_wlen X nil) e)).
    + apply (RealSetoid.real_le_id_l (real_abs real_zero) real_zero real_zero).
      * exact real_abs_zero_req.
      * exact (RealSetoid.real_eq_le real_zero real_zero (real_eq_refl real_zero)).
    + apply (RealSetoid.real_lt_id_r real_zero e (real_mult real_one e)).
      * apply real_eq_sym.
        apply (real_eq_trans _ _ _ (real_mult_comm real_one e)).
        apply real_mult_one.
      * exact He.
  - apply (uabS4_cons_glue (f w) (real_list_sum X f rest)
             (real_list_sum X (fun x => real_abs (f x)) rest)
             (uabS4_wlen X rest) e He).
    + exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest) e He).
    + exact (IH e He).
Qed.

(* B.2 末端完成（可达最强形）：|Σ_l f| ≤_B Σ_l|f|。
   real_le_closure_b 以 D := W(l) 显式正性证书闭合加权族。 *)
Theorem uabS4_abs_list_sum_le_B : forall (X : Type) (f : X -> Real) (l : list X),
  real_le_b (real_abs (real_list_sum X f l))
            (real_list_sum X (fun x => real_abs (f x)) l).
Proof.
  intros X f l.
  apply (real_le_closure_b _ _ (uabS4_wlen X l) (uabS4_wlen_pos X l)).
  intros e He. exact (uabS4_abs_list_sum_le_wt X f l e He).
Qed.

(* B.3 逐 eps 形回收：B 形 ⟹ |Σ_l f| ≤ Σ_l|f| + eps（Or-inl 注入）。
   定谳对照：B 形严格强于逐 eps 形——本件即单步反演。 *)
Theorem uabS4_abs_list_sum_le_eps : forall (X : Type) (f : X -> Real) (l : list X)
                                           (e : Real),
  real_lt real_zero e ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x => real_abs (f x)) l) e).
Proof.
  intros X f l e He.
  apply (RealSetoid.real_lt_le_iff_req _ _). apply inl.
  exact (uabS4_abs_list_sum_le_B X f l e He).
Qed.

(* ============================================================ *)
(* Part C · eps₀/2 双杀引理（TW1ATK 发现②定理化）                     *)
(* ============================================================ *)

(* C.1 余量倍率 2 杀：0 < e ＋ real_lt (Y+2e) X ＋ real_le X (Y+e)
   不可能共存。构造：Or 两支分别收敛到 real_lt (Y+2e) (Y+e)——
   lt 支传递（Y+2e < X < Y+e）；eq 支 RHS 运输（X ≡ Y+e）；
   共用引爆器：e < 2e 平移给出 Y+e < Y+2e，与上式传递自撞 irrefl。
   机理注记：eq 支非自反填充——全余量（倍率 1）时 eq 支与反向
   strict 可共存（TW1ATK 发现②的 xₙ−yₙ＝e+1/n 例），倍率 2 才双杀。 *)
Theorem uabS4_lt_double_margin_le_half_contr : forall X Y e : Real,
  real_lt real_zero e ->
  real_lt (real_plus Y (real_plus e e)) X ->
  real_le X (real_plus Y e) ->
  Empty_set.
Proof.
  intros X Y e He Hfar Hle.
  assert (Hboom : real_lt (real_plus Y (real_plus e e))
                          (real_plus Y e) -> Empty_set).
  { intro Hbad.
    assert (Hfwd : real_lt (real_plus Y e) (real_plus Y (real_plus e e))).
    { apply (real_lt_plus_translate Y e (real_plus e e)).
      apply (RealSetoid.real_lt_id_l e (real_plus e real_zero) (real_plus e e)).
      - apply real_eq_sym. apply real_plus_zero.
      - apply (real_lt_plus_translate e real_zero e). exact He. }
    exact (real_lt_irrefl _ (real_lt_trans _ _ _ Hbad Hfwd)). }
  unfold real_le in Hle. destruct Hle as [Hlt | Heq].
  - exact (Hboom (real_lt_trans _ _ _ Hfar Hlt)).
  - apply Hboom.
    exact (RealSetoid.real_lt_id_r (real_plus Y (real_plus e e)) X
             (real_plus Y e) Heq Hfar).
Qed.

(* C.2 倍率 2 杀的差形实例（族I 两点核对角 consumes）：以差形两点核
   A.2 为 le 供给源：real_lt (b + 2e) a ＋ |a−c| ≤_B |a−b|+|b−c| 型
   余量约束下的双杀实例——B 形在 eps := e 处给出 le a (|a−b|+|b−c|+e)，
   与 C.1 同构消耗。 *)
Theorem uabS4_diff_double_kill : forall a b c e : Real,
  real_lt real_zero e ->
  real_lt (real_plus (real_plus (real_abs (real_plus a (real_opp b)))
                                  (real_abs (real_plus b (real_opp c))))
                     (real_plus e e))
          (real_abs (real_plus a (real_opp c))) ->
  Empty_set.
Proof.
  intros a b c e He Hfar.
  apply (uabS4_lt_double_margin_le_half_contr
           (real_abs (real_plus a (real_opp c)))
           (real_plus (real_abs (real_plus a (real_opp b)))
                      (real_abs (real_plus b (real_opp c)))) e He Hfar).
  exact (uabS4_abs_diff_triangle_le_eps a b c e He).
Qed.

(* ============================================================ *)
(* 公理面自审：全件 Closed（零外部未证假设）                           *)
(* ============================================================ *)

Print Assumptions uabS4_le_add_r.
Print Assumptions uabS4_abs_diff_triangle_le_eps.
Print Assumptions uabS4_abs_diff_triangle_le_B.
Print Assumptions uabS4_abs_sum_le_B_pair.
Print Assumptions uabS4_wlen_pos.
Print Assumptions uabS4_cons_glue.
Print Assumptions uabS4_abs_list_sum_le_wt.
Print Assumptions uabS4_abs_list_sum_le_B.
Print Assumptions uabS4_abs_list_sum_le_eps.
Print Assumptions uabS4_lt_double_margin_le_half_contr.
Print Assumptions uabS4_diff_double_kill.
