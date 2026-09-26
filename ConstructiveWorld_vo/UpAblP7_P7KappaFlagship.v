(* ============================================================ UpAblP7_P7KappaFlagship —— 使命行：κ∈(0,1) 前提包与 1<hi 的实例装配（四件）
(* 数学使命：本件形式化 BoundedSoftmax 上下界定理所需的两个前提在抽象接口层的  *) (*   构造与实例装配：其一，κ:=1−δ*∈(0,1) 前提包在 lo:=二分之一抽象形下的       *)
(*   完整构造（0<δ*<1，含严格加倍引理 uapk7_lt_x_plus_x 与非严格化桥          *) (*   uapk7_le_neq_to_lt）；其二，该前提包与 1<hi（p7d_hi_gt_one）的合取实例    *)
(*   uapk7_flagship_hi_kappa（温度/利差/指数族九参数全显）。                   *) (* 零承认件句式：全件 Theorem 级真 Qed；零公理、零承认、零参数声明、零猜想、    *)
(*   零弃证（禁词中文化）；零经典逻辑引设；语句面全 Set 层（合取用 S01 And=prod、*) (*   析取用 Or=sum，零 Prop 泄露）；公理面零新增。                             *)
(* 主要结果（前缀 uapk7_）：                                                  *) (*   uapk7_le_neq_to_lt : Or (lt a b) (Id a b) -> Not (Id a b) -> lt a b。     *)
(*   uapk7_lt_x_plus_x : lt zero x -> lt x (x+x)。                            *) (*   uapk7_delta_star_bounded_half : lt zero (half·half) ∧ lt (half·half) one，*)
(*     其中 half:=inv_pos (plus one one) two_pos。                            *) (*   uapk7_flagship_hi_kappa : κ∈(0,1) 前提包 ∧ lt one hi。                    *)
(* 来源：源文件 Paper7Ablation.v、LoHiSqueeze.v、P7BoundedSoftmaxDeep.v、       *) (*   UpAblP7_Paper7Ablation.v（uabp7_kappa_in01_package 前提包源件）、         *)
(*   UpAblP7_LoHiSqueeze.v（half 别名同构的姊妹件）；本件只使用其已证出口面，   *) (*   原树零改。                                                                *)
(* 依赖清单：CW_ConstructiveWorld_219、S01_BaseRing（half_twice/two_pos/       *) (*   inv_pos_pos/le_plus_nonneg_r/plus_cancel_l/lt_le_iff/lt_dec 等序与正性面）、*)
(*   Paper7Ablation、LoHiSqueeze、P7BoundedSoftmaxDeep（p7d_hi_gt_one）、       *) (*   UpAblP7_Paper7Ablation、UpAblP7_LoHiSqueeze；载体供给节另引                *)
(*   UpReqConcFin2（cf2_temp_pos/cf2_Delta_pos）与 UpAblD1_expf_pack            *) (*   （real_expf_realizable 的逐位拆包引用形，uabd1x_expf 系）。                *)
(* 证明要点：件a 由 Or 消去：lt 支直取，eq 支以 Not (Id a b) 矛盾消去。        *) (*   件b-0 以 DecidableOrder 三分情形构造：lt 支直取；eq 支经 plus_cancel_l     *)
(*   消去首项得 0=x，与 0<x 矛盾；gt 支与 le_plus_nonneg_r 的 x≤x+x 合成       *)
(*   x+x<x+x 自反矛盾。                                                        *)
(*   件b 左支由 inv_pos_pos 与 mult_positive；右支经加倍还原链（half_twice：    *)
(*   1/4+1/4=1/2、1/2+1/2=1）得 half2<half<one 严格链；Not (Id half2 one) 的    *)
(*   见证由 half2=one ⟹ half=1+1 ⟹ 4=1 ⟹ 2<1 与 1≤2 合成 2<2 矛盾给出；        *)
(*   末端 DO 三分情形收束：lt 支直取、eq 支经 uapk7_le_neq_to_lt、              *)
(*   gt 支反自反矛盾。                                                         *)
(*   三分情形（lt_dec）在本件承担全部分情形推理：各支以矛盾消去收束。          *)
(*   件c 两支合取：前提包以 @uabp7_kappa_in01_package 全显实例化；1<hi 以      *)
(*   p7d_hi_gt_one 同参实例化（hi:=expf(invT·Delta)）；Section 九参数           *)
(*   （temp/Delta/expf 五件）与别名 invT/lo/hi/δ* 与源模块对应节同构。            *)
(* 构造性注记：语句面全 Set 层；公理面零新增；全中文零承认件写法；              *)
(*   文尾 Print Assumptions 逐件全闭合。                                       *)
(* 编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。 *)
   ============================================================*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import Paper7Ablation.
Require Import LoHiSqueeze.
Require Import P7BoundedSoftmaxDeep.
Require Import UpAblP7_Paper7Ablation.
Require Import UpAblP7_LoHiSqueeze.
Require Import UpReqConcFin2.
Require Import UpAblD1_expf_pack.

(* ################ 段一：由 Or 见证与不等性得严格序的桥 ############## *)
(* 该桥只用基类前提（零 DO 依赖）：见证为 Or 型，消去即构造。               *)

Section Uapk7Bridge.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 件a：lt 支直取，eq 支与 Not (Id a b) 前提矛盾消去 *)
Theorem uapk7_le_neq_to_lt :
  forall a b : R, Or (lt a b) (Id a b) -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hwit Hne.
  destruct Hwit as [Hlt | Heq].
  - exact Hlt.
  - elim (Hne Heq).
Qed.

End Uapk7Bridge.

(* ################ 段二：δ*:=half·half 的双侧界（二分之一抽象形） ################# *)
(* Section 带 DO（件b-0 与件b 末端的三分情形均使用 lt_dec）。别名 half/half2    *)
(* 与 UpAblP7_LoHiSqueeze 的对应件同构（lo:=inv_pos (plus one one) two_pos）。 *)

Section Uapk7Half.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 件b-0：0<x ⟹ x<x+x。抽象接口无「加正仍严格」原语，                         *)
(* 本件以 DO 三分情形构造：eq 支 plus_cancel_l 消去首项得 0=x，与 0<x 矛盾；    *)
(* gt 支 x+x<x 与 le_plus_nonneg_r 的 x≤x+x 合成自反矛盾。 *)
Theorem uapk7_lt_x_plus_x :
  forall x : R, lt zero x -> lt x (plus x x).
Proof.
  intros x Hx.
  destruct (lt_dec x (plus x x)) as [Hlt | [Heq | Hgt]].
  - exact Hlt.
  - assert (Hxz : Id (plus x zero) (plus x x))
      by exact (id_trans (plus_zero x) Heq).
    assert (H0x : Id zero x) by exact (plus_cancel_l x zero x Hxz).
    elim (lt_irrefl zero (lt_id_r zero x zero (id_sym H0x) Hx)).
  - assert (Hlexx : le x (plus x x))
      by exact (le_plus_nonneg_r x x (lt_le_iff zero x (inl Hx))).
    elim (lt_irrefl (plus x x)
            (lt_le_trans (plus x x) x (plus x x) Hgt Hlexx)).
Qed.

(* 件b：0<δ*<1 @ lo:=1/2（加倍还原链与件a 桥合成） *)
Theorem uapk7_delta_star_bounded_half :
  And (lt zero half2) (lt half2 one).
Proof.
  assert (Hhp : lt zero half) by exact (inv_pos_pos (plus one one) two_pos).
  assert (Hh2p : lt zero half2) by exact (mult_positive half half Hhp Hhp).
  (* 加倍还原链（half_twice）：1/4+1/4=1/2、1/2+1/2=1、1=4·(1/4) *)
  assert (Hq : Id (plus half2 half2) half) by exact (half_twice half).
  assert (Hone : Id (plus half half) one)
    by exact (id_trans (id_cong (fun x => plus x x) (id_sym (mult_one half)))
                       (half_twice one)).
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2)))
    by exact (id_trans (id_sym Hone)
                       (id_sym (id_cong (fun x => plus x x) Hq))).
  split.
  - exact Hh2p.
  - (* 严格面：half2<half2+half2（件b-0）经 Hq 得 half2<half；half<half+half *)
    (* 经 Hone 得 half<one；两跳 lt_trans 构成 half2<one。 *)
    assert (Hlt1 : lt half2 (plus half2 half2)) by exact (uapk7_lt_x_plus_x half2 Hh2p).
    assert (Hlt2 : lt half2 half) by exact (lt_id_r half2 (plus half2 half2) half Hq Hlt1).
    assert (Hlt3 : lt half (plus half half)) by exact (uapk7_lt_x_plus_x half Hhp).
    assert (Hlt4 : lt half one) by exact (lt_id_r half (plus half half) one Hone Hlt3).
    assert (Hchain : lt half2 one) by exact (lt_trans half2 half one Hlt2 Hlt4).
    (* Not (Id half2 one)：由 half2=one 推 half=1+1、4=1，进而 2<1，与 1≤2 合成 2<2 矛盾 *)
    assert (Hne : Not (Id half2 one)).
    { intro Heq.
      assert (H2 : Id half (plus one one))
        by exact (id_trans (id_sym Hq) (id_cong (fun w => plus w w) Heq)).
      assert (H41 : Id (plus (plus one one) (plus one one)) one)
        by exact (id_trans (id_cong (fun w => plus w w) (id_sym H2)) Hone).
      assert (H24 : lt (plus one one) (plus (plus one one) (plus one one)))
        by exact (uapk7_lt_x_plus_x (plus one one) two_pos).
      assert (H21 : lt (plus one one) one) by exact (lt_id_r (plus one one) (plus (plus one one) (plus one one)) one H41 H24).
      assert (Hle12 : le one (plus one one))
        by exact (le_plus_nonneg_r one one (lt_le_iff zero one (inl one_pos))).
      exact (lt_irrefl (plus one one)
               (lt_le_trans (plus one one) one (plus one one) H21 Hle12)). }
    (* 非严格面：1/4≤1/2≤1/4+1/4=1，经 le_id_r 与恒等式得 half2≤one *)
    assert (Hle0 : le zero half2) by exact (lt_le_iff zero half2 (inl Hh2p)).
    assert (Hle0' : le zero (plus half2 half2))
      by exact (lt_le_iff zero (plus half2 half2)
                  (inl (plus_positive half2 half2 Hh2p Hh2p))).
    assert (Hle : le half2 one)
      by exact (le_id_r half2 (plus (plus half2 half2) (plus half2 half2)) one
                  (id_sym Hone2)
                  (le_trans half2 (plus half2 half2)
                     (plus (plus half2 half2) (plus half2 half2))
                     (le_plus_nonneg_r half2 half2 Hle0)
                     (le_plus_nonneg_r (plus half2 half2) (plus half2 half2) Hle0'))).
    (* DO 三分情形收束：lt 支直取；eq 支经件a 与 Not (Id half2 one) 矛盾消去； *)
    (* gt 支 one<half2 与 le half2≤one 合成 one<one 矛盾。 *)
    destruct (lt_dec half2 one) as [Hlt | [Heq | Hgt]].
    + exact Hlt.
    + exact (uapk7_le_neq_to_lt half2 one (inr Heq) Hne).
    + elim (lt_irrefl one (lt_le_trans one half2 one Hgt Hle)).
Qed.

End Uapk7Half.

(* ################ 段三：κ∈(0,1) 前提包与 1<hi 的实例合取 ################ *)
(* Section 九参数与 UpAblP7_Paper7Ablation 的包节一致；                         *)
(* 别名 invT/lo/hi/δ* 与源模块对应节同构。 *)

Section Uapk7Flagship.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* 件c：κ∈(0,1) 前提包（@ 全显实例化 uabp7_kappa_in01_package）∧ 1<hi        *)
(*   （p7d_hi_gt_one 实例支：hi:=expf(invT·Delta)）。 *)
Theorem uapk7_flagship_hi_kappa :
  And (And (lt zero (minus one delta_star)) (lt (minus one delta_star) one))
      (lt one hi).
Proof.
  split.
  - exact (@uabp7_kappa_in01_package RI DO temp temp_pos Delta Delta_pos
             expf expf_pos expf_zero expf_plus expf_mono_lt).
  - exact (p7d_hi_gt_one temp temp_pos Delta Delta_pos expf expf_pos
             expf_zero expf_mono_lt).
Qed.

End Uapk7Flagship.

(* ################ 六前提位的载体供给节（逐位消解） ################
   原六假设位（temp_pos/Delta_pos/expf_pos/expf_zero/expf_plus/
   expf_mono_lt）为 RI 面抽象证书位；本节在典范 Real 载体 req 面
   逐位供给同构语句（字段映照：lt:=real_lt、req:=real_eq、
   zero:=real_zero、one:=real_one、plus:=real_plus、mult:=real_mult）。
   载体：温度=cf2_temp、利差=cf2_Delta（UpReqConcFin2），指数函数=
   uabd1x_expf（real_expf_realizable 的签名投影，其逐位拆包引用形
   uabd1x_expf_pos/zero/plus/mono_lt 见 UpAblD1_expf_pack）。
   kappa 前提包位由 uabp7_kappa_in01_package 在抽象接口层供给
   （uapk7_flagship_hi_kappa 全参显式使用，签名保持）；Id 面无具体
   载体实例，故载体供给在 req 面陈述。原抽象假设位声明与既有定理
   签名零改动。 *)
Section Uapk7CarrierSupply.

(* 位 temp_pos：载体温度正性（cf2_temp_pos 全参直引） *)
Theorem uapk7_temp_pos_supply : real_lt real_zero cf2_temp.
Proof. exact (cf2_temp_pos). Qed.

(* 位 Delta_pos：载体利差正性（cf2_Delta_pos 全参直引） *)
Theorem uapk7_Delta_pos_supply : real_lt real_zero cf2_Delta.
Proof. exact (cf2_Delta_pos). Qed.

(* 位 expf_pos：载体指数逐点正（uabd1x_expf_pos 直引） *)
Theorem uapk7_expf_pos_supply : forall x : Real, real_lt real_zero (uabd1x_expf x).
Proof. exact (uabd1x_expf_pos). Qed.

(* 位 expf_zero：载体指数零点幺值（uabd1x_expf_zero 直引） *)
Theorem uapk7_expf_zero_supply : real_eq (uabd1x_expf real_zero) real_one.
Proof. exact (uabd1x_expf_zero). Qed.

(* 位 expf_plus：载体指数和性（uabd1x_expf_plus 直引） *)
Theorem uapk7_expf_plus_supply : forall a b : Real,
  real_eq (uabd1x_expf (real_plus a b))
          (real_mult (uabd1x_expf a) (uabd1x_expf b)).
Proof. exact (uabd1x_expf_plus). Qed.

(* 位 expf_mono_lt：载体指数严格单调（uabd1x_expf_mono_lt 直引） *)
Theorem uapk7_expf_mono_lt_supply : forall a b : Real,
  real_lt a b -> real_lt (uabd1x_expf a) (uabd1x_expf b).
Proof. exact (uabd1x_expf_mono_lt). Qed.

End Uapk7CarrierSupply.

(* ---- 假设审计（对逐件 Print Assumptions） ---- *)
Print Assumptions uapk7_le_neq_to_lt.
Print Assumptions uapk7_lt_x_plus_x.
Print Assumptions uapk7_delta_star_bounded_half.
Print Assumptions uapk7_flagship_hi_kappa.
Print Assumptions uapk7_temp_pos_supply.
Print Assumptions uapk7_Delta_pos_supply.
Print Assumptions uapk7_expf_pos_supply.
Print Assumptions uapk7_expf_zero_supply.
Print Assumptions uapk7_expf_plus_supply.
Print Assumptions uapk7_expf_mono_lt_supply.
