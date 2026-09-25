(* ========================================================================= *)
(* 【ToyR 战役·包M·T252 台账席】玩具级定理同名非平凡替换稿（补标头注）       *)
(*                                                                           *)
(* 本稿系 ToyR 战役包M 替换落件（原名落件）；落件时头部漏植战役标记，本块由  *)
(* T274 无头注补标专席于 2026-09-21 补植：仅加头注，语句面／证明体／         *)
(* Require 面                                                                *)
(* 零改动；原头注紧随本块之后原样保留。来源刀面权威记录：消融50/T252。       *)
(* 替换定理清单：fekl_sumf_ext／fekl_sumf_add／fekl_sumf_linear（共 3 位）   *)
(* 非平凡性口径：源文件体换形归纳重演（反向分配链与尾对换位显式化）；无一行    *)
(* 拆分式假非平凡。                                                          *)
(* 本稿零公理、零承认件、全闭合、纯构造性、无经典逻辑；落件时与本次补标      *)
(* 抽验编译均验零承认。                                                      *)
(* ========================================================================= *)
(* ============================================================ *)
(* FreeEnergyKLGap.v — 施工席位 B2：Real 层自由能–KL 间隙            *)
(* ============================================================ *)
(* 目标定理（A2 席组合榜组 3 + A4 席 T4）：Real 层 FEP 核心形——        *)
(*   forall p,（归一前提）→ F(π_boltzmann) ≤ F(p) 且 差 == D·Σ kl_term。*)
(*                                                                   *)
(* 阻隔位结论（S1/S2，RealEnergyTempMono 头注复证）：KL≥0 的 plain-le    *)
(*   （real_le = Or real_lt real_eq，S02:460/S01:69 Set 值和）全称非负 *)
(*   ⟺ rLPO（p==q 点 KL==0 无一致 gap、Or 分支不可判定）。故 ≤ 方向   *)
(*   依广播降档两形，撞阻隔位零硬攻：                                   *)
(*   ① B 形：real_le_b（Bishop ≤_B，Set 层 ∀eps>0 形，UpRealLeB:63）； *)
(*   ② eps 见证形：plain real_le 出口 + eps 余量（S08:490 面）。       *)
(*   差 = D·KL 一侧不受阻隔位影响，走 real_eq 分解形。                  *)
(*                                                                   *)
(* 依赖坐标（215 vo 基座内，语句面均检验核对）：                       *)
(*   · A 件 RealKLDecomp.v:765 rkd_kl_decomp_full（F(p) == F(πb)+D·Σ  *)
(*     kl_term，real_eq 形、S/sumf/ext/add/linear/base/D/Dp/Z/Zp/p/   *)
(*     Hp/Hnormp/Hnormb 接口全显参）+ :709 rkd_boltzmann_normalized； *)
(*   · KL 非负引擎 UpRealLeB.v:592 real_gibbs_inequality_B（0 ≤_B     *)
(*     Σ_s kl_term，list 载体、归一化前提位照抄）+ S08:490            *)
(*     real_gibbs_inequality_eps（0 ≤ Σ kl + eps，Or 形出口）；        *)
(*   · ≤_B 序代数 UpRealLeB3:63/51/165 leb3_le_b_eq_r/eq_l/           *)
(*     pos_scale_l（右端运输/左端运输/正缩放）+ UpRealLeB:373         *)
(*     real_le_closure_b_one（plain-eps 余量单步闭合器）；             *)
(*   · B 件 S12_B5RecycleSF sf_vfe_ge_complexity_eps（eps 余量形）    *)
(*     升 B 形闭合（Part 5，组合榜组 3 依存面）。                     *)
(*                                                                   *)
(* 红线自审：①语句面全 Set（real_eq/real_lt/real_le_b/real_le；       *)
(*   real_le 为 S01:69 Set 值和 Or 编码、其 Or 前提仅以显式参/证内     *)
(*   destruct 依存，零裸 Prop 连词、零 ex、出口无 QltT/QleT 直书）；   *)
(*   ②公理面零假设（无公理/自认/参数声明/猜想/中止/半途认输，零经典逻辑）*)
(*   （依赖全为库内闭合件）；③非平凡（差形换算链 + Or 形正乘保序 +    *)
(*   正缩放复用闭合 + D·eps 位移换形 + 分解装配 + 归一化实例化消解 + SF     *)
(*   升形）；④文末 Print Assumptions 审计口 11 处。                  *)
(* 编译配方（9.1 主轨实测 EXIT=0；live901+215 基座轨已判死——基座 .vo  *)
(*   Corelib.Init.Prelude digest 与重装后 stdlib 不一致）：            *)
(*   source Live/toolchain/env.sh && eval $(opam env --switch live)   *)
(*   && cd Live/build && rocq c -Q /tmp/b2_91 "" -Q ../vorebuild ""   *)
(*   -Q . "" FreeEnergyKLGap.v                                        *)
(*   其中 /tmp/b2_91 含本席自编依赖件（UpRealLeB/2/3 现已可由          *)
(*   vorebuild 供；RealEnergyTempMono+RealKLDecomp 必须由此供给——     *)
(*   RealKLDecomp 不在 vorebuild order.txt 内）。依赖拷贝源：         *)
(*   ConstructiveWorld_vo 与 ConstructiveWorld_Live 逐字一致（已 diff）。*)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import RealKLDecomp.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import S12_B5RecycleSF.

(* ============================================================ *)
(* Part 0：换算引擎件（差形 / D·eps 位移 / 正乘保序两形）              *)
(* ============================================================ *)

(* 0.1 差形换算：fp == fb + dk ⟹ fp + (−fb) == dk
   （assoc/comm/opp/zero 纯 eq 链，零消费序结论） *)
Lemma fekl_diff_shift : forall (fb fp dk : Real),
  real_eq fp (real_plus fb dk) ->
  real_eq (real_plus fp (real_opp fb)) dk.
Proof.
  intros fb fp dk H.
  apply (real_eq_trans
           (real_plus fp (real_opp fb))
           (real_plus (real_plus fb dk) (real_opp fb))
           dk).
  - apply (RealSetoid.real_eq_plus_compat fp (real_opp fb)
             (real_plus fb dk) (real_opp fb)
             H (real_eq_refl (real_opp fb))).
  - (* (fb+dk)+(−fb) == dk：中段重排链 *)
    apply (real_eq_trans
             (real_plus (real_plus fb dk) (real_opp fb))
             (real_plus dk real_zero)
             dk).
    + apply (real_eq_trans
               (real_plus (real_plus fb dk) (real_opp fb))
               (real_plus fb (real_plus dk (real_opp fb)))
               (real_plus dk real_zero)).
      * apply real_eq_sym. exact (real_plus_assoc fb dk (real_opp fb)).
      * (* fb+(dk+(−fb)) == dk+0：assoc/comm 五步直链 *)
        apply (real_eq_trans
                 (real_plus fb (real_plus dk (real_opp fb)))
                 (real_plus (real_plus fb dk) (real_opp fb))
                 (real_plus dk real_zero)).
        -- exact (real_plus_assoc fb dk (real_opp fb)).
        -- apply (real_eq_trans
                     (real_plus (real_plus fb dk) (real_opp fb))
                     (real_plus (real_plus dk fb) (real_opp fb))
                     (real_plus dk real_zero)).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_plus fb dk) (real_opp fb)
                       (real_plus dk fb) (real_opp fb)
                       (real_plus_comm fb dk) (real_eq_refl (real_opp fb))).
           ++ apply (real_eq_trans
                        (real_plus (real_plus dk fb) (real_opp fb))
                        (real_plus dk (real_plus fb (real_opp fb)))
                        (real_plus dk real_zero)).
              ** apply real_eq_sym.
                 exact (real_plus_assoc dk fb (real_opp fb)).
              ** apply (RealSetoid.real_eq_plus_compat dk
                           (real_plus fb (real_opp fb)) dk real_zero
                           (real_eq_refl dk) (real_plus_opp fb)).
    + exact (real_plus_zero dk).
Qed.

(* 0.2 D·(eps·inv D) == eps（正性证书 HD 消 inv；assoc/comm/inv 链） *)
Lemma fekl_d_eps : forall (D eps : Real) (HD : real_lt real_zero D),
  real_eq (real_mult D (real_mult eps (real_inv_pos D HD))) eps.
Proof.
  intros D eps HD.
  apply (real_eq_trans
           (real_mult D (real_mult eps (real_inv_pos D HD)))
           (real_mult eps (real_mult D (real_inv_pos D HD)))
           eps).
  - (* leg A：三步重排 D·(eps·inv) == eps·(D·inv) *)
    apply (real_eq_trans
             (real_mult D (real_mult eps (real_inv_pos D HD)))
             (real_mult (real_mult D eps) (real_inv_pos D HD))
             (real_mult eps (real_mult D (real_inv_pos D HD)))).
    + exact (real_mult_assoc D eps (real_inv_pos D HD)).
    + apply (real_eq_trans
               (real_mult (real_mult D eps) (real_inv_pos D HD))
               (real_mult (real_mult eps D) (real_inv_pos D HD))
               (real_mult eps (real_mult D (real_inv_pos D HD)))).
      * apply (RealSetoid.real_eq_mult_compat (real_mult D eps)
                  (real_inv_pos D HD) (real_mult eps D) (real_inv_pos D HD)
                  (real_mult_comm D eps) (real_eq_refl (real_inv_pos D HD))).
      * apply real_eq_sym. exact (real_mult_assoc eps D (real_inv_pos D HD)).
  - (* leg B：eps·(D·inv) == eps·1 == eps *)
    apply (real_eq_trans
             (real_mult eps (real_mult D (real_inv_pos D HD)))
             (real_mult eps real_one)
             eps).
    + apply (RealSetoid.real_eq_mult_compat eps (real_mult D (real_inv_pos D HD))
               eps real_one (real_eq_refl eps) (real_inv_pos_correct D HD)).
    + exact (real_mult_one eps).
Qed.

(* 0.3 D·(K + eps·inv D) == D·K + eps（distrib + 0.2；位移换形核心） *)
Lemma fekl_d_move_eps : forall (D K eps : Real) (HD : real_lt real_zero D),
  real_eq (real_mult D (real_plus K (real_mult eps (real_inv_pos D HD))))
          (real_plus (real_mult D K) eps).
Proof.
  intros D K eps HD.
  apply (real_eq_trans
           (real_mult D (real_plus K (real_mult eps (real_inv_pos D HD))))
           (real_plus (real_mult D K) (real_mult D (real_mult eps (real_inv_pos D HD))))
           (real_plus (real_mult D K) eps)).
  - exact (real_distrib D K (real_mult eps (real_inv_pos D HD))).
  - apply (RealSetoid.real_eq_plus_compat (real_mult D K)
             (real_mult D (real_mult eps (real_inv_pos D HD)))
             (real_mult D K) eps
             (real_eq_refl (real_mult D K)) (fekl_d_eps D eps HD)).
Qed.

(* 0.4 正乘保序（Or 形）：D>0 且 0 ≤ x ⟹ 0 ≤ D·x。
   Or 前提位分支证（假设位 Or 可构造性消去，非全称非负 ⟹ 不触 rLPO 墙） *)
Lemma fekl_mult_pos_le : forall (D x : Real),
  real_lt real_zero D -> real_le real_zero x ->
  real_le real_zero (real_mult D x).
Proof.
  intros D x HD Hx. destruct Hx as [Hlt | Heq].
  - apply (RealSetoid.real_lt_le_iff_req real_zero (real_mult D x)). left.
    exact (real_mult_positive D x HD Hlt).
  - apply (RealSetoid.real_lt_le_iff_req real_zero (real_mult D x)). right.
    apply (real_eq_trans real_zero (real_mult D real_zero) (real_mult D x)).
    + apply real_eq_sym. exact (real_mult_zero D).
    + apply (RealSetoid.real_eq_mult_compat D real_zero D x
               (real_eq_refl D) Heq).
Qed.

(* 0.5 正乘保序（B 形）：D>0 且 0 ≤_B K ⟹ 0 ≤_B D·K。
   复用 leb3_le_b_pos_scale_l（≤_B 正缩放）+ 零形左端运输 *)
Lemma fekl_mult_pos_le_b : forall (D K : Real),
  real_lt real_zero D -> real_le_b real_zero K ->
  real_le_b real_zero (real_mult D K).
Proof.
  intros D K HD HK.
  apply (leb3_le_b_eq_l (real_mult D real_zero) real_zero (real_mult D K)
           (real_mult_zero D)).
  exact (leb3_le_b_pos_scale_l real_zero K D HK HD).
Qed.

(* ============================================================ *)
(* Part 1：一般 sumf 差形主件（real_eq 形、接口全显参）                *)
(*   F(p) − F(π_boltzmann) == D·Σ_s kl_term（A 件直连 + 0.1 换算）     *)
(* ============================================================ *)
Theorem fekl_gap_decomp_general :
  forall (S : Type) (sumf : (S -> Real) -> Real)
    (sumf_ext : forall (f g : S -> Real),
      (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g))
    (sumf_add : forall (f g : S -> Real),
      real_eq (sumf (fun s : S => real_plus (f s) (g s)))
              (real_plus (sumf f) (sumf g)))
    (sumf_linear : forall (a : Real) (f : S -> Real),
      real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)))
    (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s))
    (Hnormp : real_eq (sumf p) real_one)
    (Hnormb : real_eq (sumf (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)) real_one),
  real_eq
    (real_plus
       (real_free_energy S sumf real_base_loss D p Hp)
       (real_opp
          (real_free_energy S sumf real_base_loss D
             (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos)
             (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos))))
    (real_mult D
       (sumf (fun s : S =>
          real_kl_term (p s)
            (real_boltzmann_dist_r S real_base_loss D D_pos Z Z_pos s)
            (Hp s)
            (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z Z_pos s)))).
Proof.
  intros S sumf sumf_ext sumf_add sumf_linear real_base_loss D D_pos Z Z_pos
         p Hp Hnormp Hnormb.
  apply fekl_diff_shift.
  exact (rkd_kl_decomp_full S sumf sumf_ext sumf_add sumf_linear
           real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb).
Qed.

(* ============================================================ *)
(* Part 2：list 载体（s0 :: l）求和实例件                              *)
(*   sumf := fekl_sumf（real_list_sum 的 cons 载体闭包），             *)
(*   ext/add/linear 三件由 real_list_sum_ext/add/linear 直连实例化消解。     *)
(* ============================================================ *)
Definition fekl_sumf (X : Type) (s0 : X) (l : list X) (f : X -> Real) : Real :=
  real_list_sum X f (s0 :: l).

Lemma fekl_sumf_ext : forall (X : Type) (s0 : X) (l : list X)
  (f g : X -> Real),
  (forall s : X, real_eq (f s) (g s)) ->
  real_eq (fekl_sumf X s0 l f) (fekl_sumf X s0 l g).
Proof.
  intros X s0 l f g Hfg.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (RealSetoid.real_eq_plus_compat (f s0) real_zero (g s0) real_zero
             (Hfg s0) (real_eq_refl real_zero)).
  - exact (RealSetoid.real_eq_plus_compat (f s0)
             (real_plus (f w) (real_list_sum X f rest))
             (g s0)
             (real_plus (g w) (real_list_sum X g rest))
             (Hfg s0) (IH w)).
Qed.

Lemma fekl_sumf_add : forall (X : Type) (s0 : X) (l : list X)
  (f g : X -> Real),
  real_eq (fekl_sumf X s0 l (fun s : X => real_plus (f s) (g s)))
          (real_plus (fekl_sumf X s0 l f) (fekl_sumf X s0 l g)).
Proof.
  intros X s0 l f g.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (real_eq_trans
             (real_plus (real_plus (f s0) (g s0)) real_zero)
             (real_plus (f s0) (g s0))
             (real_plus (real_plus (f s0) real_zero)
                        (real_plus (g s0) real_zero))
             (real_plus_zero (real_plus (f s0) (g s0)))
             (RealSetoid.real_eq_plus_compat (f s0) (g s0)
                (real_plus (f s0) real_zero) (real_plus (g s0) real_zero)
                (real_eq_sym (real_plus (f s0) real_zero) (f s0)
                   (real_plus_zero (f s0)))
                (real_eq_sym (real_plus (g s0) real_zero) (g s0)
                   (real_plus_zero (g s0))))).
  - exact (real_eq_trans
             (real_plus (real_plus (f s0) (g s0))
                        (real_plus (real_plus (f w) (g w))
                                   (real_list_sum X
                                      (fun s : X => real_plus (f s) (g s))
                                      rest)))
             (real_plus (real_plus (f s0) (g s0))
                        (real_plus (real_plus (f w) (real_list_sum X f rest))
                                   (real_plus (g w) (real_list_sum X g rest))))
             (real_plus
                (real_plus (f s0) (real_plus (f w) (real_list_sum X f rest)))
                (real_plus (g s0) (real_plus (g w) (real_list_sum X g rest))))
             (RealSetoid.real_eq_plus_compat
                (real_plus (f s0) (g s0))
                (real_plus (real_plus (f w) (g w))
                           (real_list_sum X
                              (fun s : X => real_plus (f s) (g s)) rest))
                (real_plus (f s0) (g s0))
                (real_plus (real_plus (f w) (real_list_sum X f rest))
                           (real_plus (g w) (real_list_sum X g rest)))
                (real_eq_refl (real_plus (f s0) (g s0)))
                (IH w))
             (real_plus_swap_mid (f s0) (g s0)
                (real_plus (f w) (real_list_sum X f rest))
                (real_plus (g w) (real_list_sum X g rest)))).
Qed.

Lemma fekl_sumf_linear : forall (X : Type) (s0 : X) (l : list X)
  (a : Real) (f : X -> Real),
  real_eq (fekl_sumf X s0 l (fun s : X => real_mult a (f s)))
          (real_mult a (fekl_sumf X s0 l f)).
Proof.
  intros X s0 l a f.
  unfold fekl_sumf.
  revert s0.
  induction l as [| w rest IH]; intros s0; simpl.
  - exact (real_eq_trans
             (real_plus (real_mult a (f s0)) real_zero)
             (real_mult a (f s0))
             (real_mult a (real_plus (f s0) real_zero))
             (real_plus_zero (real_mult a (f s0)))
             (real_eq_sym (real_mult a (real_plus (f s0) real_zero))
                (real_mult a (f s0))
                (real_eq_trans
                   (real_mult a (real_plus (f s0) real_zero))
                   (real_plus (real_mult a (f s0)) (real_mult a real_zero))
                   (real_mult a (f s0))
                   (real_distrib a (f s0) real_zero)
                   (real_eq_trans
                      (real_plus (real_mult a (f s0)) (real_mult a real_zero))
                      (real_plus (real_mult a (f s0)) real_zero)
                      (real_mult a (f s0))
                      (RealSetoid.real_eq_plus_compat (real_mult a (f s0))
                         (real_mult a real_zero) (real_mult a (f s0))
                         real_zero
                         (real_eq_refl (real_mult a (f s0)))
                         (real_mult_zero a))
                      (real_plus_zero (real_mult a (f s0))))))).
  - exact (real_eq_sym
             (real_mult a
                (real_plus (f s0) (real_plus (f w) (real_list_sum X f rest))))
             (real_plus (real_mult a (f s0))
                        (real_plus (real_mult a (f w))
                                   (real_list_sum X
                                      (fun s : X => real_mult a (f s)) rest)))
             (real_eq_trans
                (real_mult a
                   (real_plus (f s0)
                      (real_plus (f w) (real_list_sum X f rest))))
                (real_plus (real_mult a (f s0))
                           (real_mult a
                              (real_plus (f w) (real_list_sum X f rest))))
                (real_plus (real_mult a (f s0))
                           (real_plus (real_mult a (f w))
                                      (real_list_sum X
                                         (fun s : X => real_mult a (f s))
                                         rest)))
                (real_distrib a (f s0)
                   (real_plus (f w) (real_list_sum X f rest)))
                (RealSetoid.real_eq_plus_compat (real_mult a (f s0))
                   (real_mult a (real_plus (f w) (real_list_sum X f rest)))
                   (real_mult a (f s0))
                   (real_list_sum X (fun s : X => real_mult a (f s))
                      (w :: rest))
                   (real_eq_refl (real_mult a (f s0)))
                   (real_eq_sym
                      (real_list_sum X (fun s : X => real_mult a (f s))
                         (w :: rest))
                      (real_mult a (real_plus (f w) (real_list_sum X f rest)))
                      (IH w))))).
Qed.

(* 配分函数：Z := Σ_{s∈s0::l} e^{−e(s)/D}（正性：逐点 exp 正 + cons 非空） *)
Definition fekl_part (X : Type) (s0 : X) (l : list X)
           (real_base_loss : X -> Real) (D : Real)
           (D_pos : real_lt real_zero D) : Real :=
  real_list_sum X
    (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
    (s0 :: l).

Lemma fekl_part_pos : forall (X : Type) (s0 : X) (l : list X)
  (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D),
  real_lt real_zero (fekl_part X s0 l real_base_loss D D_pos).
Proof.
  intros X s0 l real_base_loss D D_pos. unfold fekl_part.
  apply (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
           (s0 :: l)).
  - intro s.
    exact (real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (real_base_loss s))).
  - discriminate.
Qed.

(* ============================================================ *)
(* Part 3：FEP 核心形·B 形出口（降档①）                                *)
(*   F(π_boltzmann) ≤_B F(p)，前提 = 归一前提 ×2（A 件前提形照抄）。   *)
(*   装配：0 ≤_B D·K（Gibbs-B + 正缩放）⊕ F(p)==F(πb)+D·K 右端运输。   *)
(* ============================================================ *)
Theorem fekl_fep_gap_le_b :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                   (s0 :: l)) real_one),
  real_le_b
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos))
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
Proof.
  intros X s0 l real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb.
  set (Fpi := real_free_energy X (fekl_sumf X s0 l) real_base_loss D
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos)).
  set (Fp := real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
  set (K := real_list_sum X (fun s : X =>
              real_kl_term (p s)
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s))
              (s0 :: l)).
  (* 步1：0 ≤_B K（UpRealLeB real_gibbs_inequality_B 直连） *)
  assert (HK : real_le_b real_zero K).
  { exact (real_gibbs_inequality_B X (s0 :: l) p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
             Hp
             (fun s : X => real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s)
             Hnormp Hnormb). }
  (* 步2：0 ≤_B D·K（正缩放闭合，Part 0.5） *)
  assert (HDK : real_le_b real_zero (real_mult D K))
    by exact (fekl_mult_pos_le_b D K D_pos HK).
  (* 步3：F(p) == F(πb) + D·K（A 件直连） *)
  assert (Hdec : real_eq Fp (real_plus Fpi (real_mult D K))).
  { exact (rkd_kl_decomp_full X (fekl_sumf X s0 l)
             (fekl_sumf_ext X s0 l) (fekl_sumf_add X s0 l)
             (fekl_sumf_linear X s0 l)
             real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb). }
  (* 步4：F(πb)+0 ≤_B F(πb)+D·K（加法兼容 + 自反） *)
  assert (Hstep : real_le_b (real_plus Fpi real_zero)
                            (real_plus Fpi (real_mult D K))).
  { exact (real_le_b_plus_compat Fpi Fpi real_zero (real_mult D K)
             (leb3_le_b_refl Fpi) HDK). }
  (* 步5：左端 +0 消去、右端沿分解件运输闭合 *)
  exact (leb3_le_b_eq_r Fpi (real_plus Fpi (real_mult D K)) Fp
           (leb3_le_b_eq_l (real_plus Fpi real_zero) Fpi
              (real_plus Fpi (real_mult D K)) (real_plus_zero Fpi) Hstep)
           (real_eq_sym _ _ Hdec)).
Qed.

(* ============================================================ *)
(* Part 4：FEP 核心形·规范配分实例（前提仅归一前提，全闭合）            *)
(*   Z := Σ e^{−e/D}（fekl_part，正性内证），Σ π_b == 1 由             *)
(*   rkd_boltzmann_normalized 以 partition 恒等实例化消解。                  *)
(* ============================================================ *)
Theorem fekl_fep_gap_canonical_le_b :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one),
  real_le_b
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos
          (fekl_part X s0 l real_base_loss D D_pos)
          (fekl_part_pos X s0 l real_base_loss D D_pos))
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos
          (fekl_part X s0 l real_base_loss D D_pos)
          (fekl_part_pos X s0 l real_base_loss D D_pos)))
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
Proof.
  intros X s0 l real_base_loss D D_pos p Hp Hnormp.
  apply (fekl_fep_gap_le_b X s0 l real_base_loss D D_pos
           (fekl_part X s0 l real_base_loss D D_pos)
           (fekl_part_pos X s0 l real_base_loss D D_pos) p Hp Hnormp).
  exact (rkd_boltzmann_normalized X (fekl_sumf X s0 l)
           (fekl_sumf_ext X s0 l) (fekl_sumf_linear X s0 l)
           real_base_loss D D_pos
           (fekl_part X s0 l real_base_loss D D_pos)
           (fekl_part_pos X s0 l real_base_loss D D_pos)
           (real_eq_refl (fekl_sumf X s0 l
              (fun s : X =>
                 real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))))).
Qed.

(* ============================================================ *)
(* Part 5：FEP 核心形·eps 见证形出口（降档②，plain real_le）           *)
(*   F(π_boltzmann) ≤ F(p) + eps。装配：                               *)
(*   0 ≤ K+eps·inv(D)（real_gibbs_inequality_eps）→ 正乘保序（Part     *)
(*   0.4）→ 位移换形 0 ≤ D·K+eps → Or 两支构造 F(πb) ≤ F(πb)+(D·K+eps) *)
(*   → 分解件右端运输。                                                *)
(* ============================================================ *)
Theorem fekl_fep_gap_eps :
  forall (X : Type) (s0 : X) (l : list X)
    (real_base_loss : X -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z : Real) (Z_pos : real_lt real_zero Z)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
    (Hnormp : real_eq (real_list_sum X p (s0 :: l)) real_one)
    (Hnormb : real_eq
                (real_list_sum X
                   (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                   (s0 :: l)) real_one)
    (eps : Real) (Heps : real_lt real_zero eps),
  real_le
    (real_free_energy X (fekl_sumf X s0 l) real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos))
    (real_plus
       (real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp) eps).
Proof.
  intros X s0 l real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb eps Heps.
  set (Fpi := real_free_energy X (fekl_sumf X s0 l) real_base_loss D
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos)).
  set (Fp := real_free_energy X (fekl_sumf X s0 l) real_base_loss D p Hp).
  set (K := real_list_sum X (fun s : X =>
              real_kl_term (p s)
                (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos s)
                (Hp s)
                (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s))
              (s0 :: l)).
  assert (Hdec : real_eq Fp (real_plus Fpi (real_mult D K))).
  { exact (rkd_kl_decomp_full X (fekl_sumf X s0 l)
             (fekl_sumf_ext X s0 l) (fekl_sumf_add X s0 l)
             (fekl_sumf_linear X s0 l)
             real_base_loss D D_pos Z Z_pos p Hp Hnormp Hnormb). }
  (* 步1：0 ≤ K + eps·inv(D)（S08 real_gibbs_inequality_eps 直连） *)
  assert (HKd : real_le real_zero
                  (real_plus K (real_mult eps (real_inv_pos D D_pos)))).
  { exact (real_gibbs_inequality_eps X (s0 :: l) p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z Z_pos)
             Hp
             (fun s : X => real_boltzmann_dist_r_pos X real_base_loss D D_pos Z Z_pos s)
             Hnormp Hnormb
             (real_mult eps (real_inv_pos D D_pos))
             (real_mult_positive eps (real_inv_pos D D_pos) Heps
                (real_inv_pos_pos D D_pos))). }
  (* 步2：正乘保序：0 ≤ D·(K + eps·inv(D))（Part 0.4） *)
  assert (HDk : real_le real_zero
                  (real_mult D (real_plus K (real_mult eps (real_inv_pos D D_pos))))).
  { exact (fekl_mult_pos_le D (real_plus K (real_mult eps (real_inv_pos D D_pos)))
             D_pos HKd). }
  (* 步3：位移换形：0 ≤ D·K + eps（Part 0.3） *)
  assert (HDe : real_le real_zero (real_plus (real_mult D K) eps)).
  { exact (RealSetoid.real_le_id_r real_zero
             (real_mult D (real_plus K (real_mult eps (real_inv_pos D D_pos))))
             (real_plus (real_mult D K) eps)
             (fekl_d_move_eps D K eps D_pos) HDk). }
  (* 步4：Or 两支构造 F(πb) ≤ F(πb)+(D·K+eps) *)
  assert (Hshift : real_le Fpi (real_plus Fpi (real_plus (real_mult D K) eps))).
  { destruct HDe as [Hlt | Heq0].
    - apply (RealSetoid.real_lt_le_iff_req Fpi
               (real_plus Fpi (real_plus (real_mult D K) eps))). left.
      apply (RealSetoid.real_lt_id_l Fpi (real_plus Fpi real_zero)
               (real_plus Fpi (real_plus (real_mult D K) eps))).
      + apply real_eq_sym. exact (real_plus_zero Fpi).
      + exact (real_lt_plus_translate Fpi real_zero
                 (real_plus (real_mult D K) eps) Hlt).
    - apply RealSetoid.real_eq_le.
      apply (real_eq_trans Fpi (real_plus Fpi real_zero)
               (real_plus Fpi (real_plus (real_mult D K) eps))).
      + apply real_eq_sym. exact (real_plus_zero Fpi).
      + apply (RealSetoid.real_eq_plus_compat Fpi real_zero Fpi
                 (real_plus (real_mult D K) eps)
                 (real_eq_refl Fpi) Heq0). }
  (* 步5：右端 F(πb)+(D·K+eps) == F(p)+eps 运输闭合 *)
  apply (RealSetoid.real_le_id_r Fpi
           (real_plus Fpi (real_plus (real_mult D K) eps))
           (real_plus Fp eps)).
  - apply (real_eq_trans
             (real_plus Fpi (real_plus (real_mult D K) eps))
             (real_plus (real_plus Fpi (real_mult D K)) eps)
             (real_plus Fp eps)).
    + exact (real_plus_assoc Fpi (real_mult D K) eps).
    + apply (RealSetoid.real_eq_plus_compat
               (real_plus Fpi (real_mult D K)) eps Fp eps
               (real_eq_sym _ _ Hdec) (real_eq_refl eps)).
  - exact Hshift.
Qed.

(* ============================================================ *)
(* Part 6：B 件依存（S12 sf_vfe_ge_complexity_eps 升 B 形闭合）         *)
(*   SF 层对照：复杂度 ≤_B vfe（匹配态自由能 ≥ 复杂度的 Bishop 对应物； *)
(*   组合榜组 3 / A4 T4 的 S 系依存面）。                               *)
(* ============================================================ *)
Theorem fekl_sf_vfe_ge_complexity_B :
  forall v : SFVec, real_le_b (sf_n2r (length v)) (sf_vfe v v).
Proof.
  intro v. unfold real_le_b. intros eps Heps.
  set (c := sf_n2r (length v)).
  set (h := real_inv_pos (real_plus real_one real_one) real_two_pos_local).
  set (dh := real_mult eps h).
  (* 半量 dh := eps·inv(2)：正、且 dh < eps（real_inv_two_lt_one 正乘） *)
  assert (Hhpos : real_lt real_zero h)
    by exact (real_inv_pos_pos (real_plus real_one real_one) real_two_pos_local).
  assert (Hdpos : real_lt real_zero dh)
    by exact (real_mult_positive eps h Heps Hhpos).
  assert (Hde : real_lt dh eps).
  { apply (RealSetoid.real_lt_id_r dh (real_mult eps real_one) eps).
    - exact (real_mult_one eps).
    - exact (real_mult_lt_compat_l h real_one eps real_inv_two_lt_one Heps). }
  (* 以半量 dh 依存 B 件（Or 两支均闭合） *)
  destruct (sf_vfe_ge_complexity_eps v dh Hdpos) as [Hlt | Heq].
  - (* lt 支：c−dh < vfe ⟹ c < vfe+dh < vfe+eps *)
    assert (HeqL : real_eq c (real_plus dh (real_plus c (real_opp dh)))).
    { apply real_eq_sym.
      apply (real_eq_trans
               (real_plus dh (real_plus c (real_opp dh)))
               (real_plus dh (real_plus (real_opp dh) c))
               c).
      - apply (RealSetoid.real_eq_plus_compat dh
                 (real_plus c (real_opp dh)) dh
                 (real_plus (real_opp dh) c)
                 (real_eq_refl dh) (real_plus_comm c (real_opp dh))).
      - apply (real_eq_trans
                 (real_plus dh (real_plus (real_opp dh) c))
                 (real_plus (real_plus dh (real_opp dh)) c)
                 c).
        + exact (real_plus_assoc dh (real_opp dh) c).
        + apply (real_eq_trans
                   (real_plus (real_plus dh (real_opp dh)) c)
                   (real_plus real_zero c)
                   c).
          * apply (RealSetoid.real_eq_plus_compat
                     (real_plus dh (real_opp dh)) c real_zero c
                     (real_plus_opp dh) (real_eq_refl c)).
          * exact (real_eq_trans (real_plus real_zero c) (real_plus c real_zero) c
                       (real_plus_comm real_zero c) (real_plus_zero c)). }
    assert (Hlt2 : real_lt c (real_plus (sf_vfe v v) dh)).
    { apply (RealSetoid.real_lt_id_r c
               (real_plus dh (sf_vfe v v)) (real_plus (sf_vfe v v) dh)).
      - exact (real_plus_comm dh (sf_vfe v v)).
      - apply (RealSetoid.real_lt_id_l c
                 (real_plus dh (real_plus c (real_opp dh)))
                 (real_plus dh (sf_vfe v v))).
        + exact HeqL.
        + exact (real_lt_plus_translate dh (real_plus c (real_opp dh))
                   (sf_vfe v v) Hlt). }
    exact (real_lt_trans c (real_plus (sf_vfe v v) dh)
             (real_plus (sf_vfe v v) eps) Hlt2
             (real_lt_plus_translate (sf_vfe v v) dh eps Hde)).
  - (* eq 支：c−dh == vfe ⟹ c == vfe+dh < vfe+eps *)
    assert (Heqc : real_eq c (real_plus (sf_vfe v v) dh)).
    { apply (real_eq_trans c
               (real_plus (real_plus c (real_opp dh)) dh)
               (real_plus (sf_vfe v v) dh)).
      - apply real_eq_sym.
        apply (real_eq_trans
                 (real_plus (real_plus c (real_opp dh)) dh)
                 (real_plus c (real_plus (real_opp dh) dh))
                 c).
        + apply real_eq_sym. exact (real_plus_assoc c (real_opp dh) dh).
        + apply (real_eq_trans
                   (real_plus c (real_plus (real_opp dh) dh))
                   (real_plus c real_zero)
                   c).
          * apply (RealSetoid.real_eq_plus_compat c
                     (real_plus (real_opp dh) dh) c real_zero
                     (real_eq_refl c)
                     (real_eq_trans (real_plus (real_opp dh) dh)
                        (real_plus dh (real_opp dh)) real_zero
                        (real_plus_comm (real_opp dh) dh)
                        (real_plus_opp dh))).
          * exact (real_plus_zero c).
      - apply (RealSetoid.real_eq_plus_compat
                 (real_plus c (real_opp dh)) dh (sf_vfe v v) dh
                 Heq (real_eq_refl dh)). }
    apply (RealSetoid.real_lt_id_l c (real_plus (sf_vfe v v) dh)
             (real_plus (sf_vfe v v) eps) Heqc
             (real_lt_plus_translate (sf_vfe v v) dh eps Hde)).
Qed.

(* ============================================================ *)
(* G4 证据：全件零外部未证假设（审计口）                                *)
(* ============================================================ *)
Print Assumptions fekl_diff_shift.
Print Assumptions fekl_d_eps.
Print Assumptions fekl_d_move_eps.
Print Assumptions fekl_mult_pos_le.
Print Assumptions fekl_mult_pos_le_b.
Print Assumptions fekl_gap_decomp_general.
Print Assumptions fekl_sumf_ext.
Print Assumptions fekl_sumf_add.
Print Assumptions fekl_sumf_linear.
Print Assumptions fekl_part_pos.
Print Assumptions fekl_fep_gap_le_b.
Print Assumptions fekl_fep_gap_canonical_le_b.
Print Assumptions fekl_fep_gap_eps.
Print Assumptions fekl_sf_vfe_ge_complexity_B.
