(* ============================================================ *)
(* ToyR 战役包I · 切片七扫尾 —— UpAblT6_UpReqSampling 玩具替换稿        *)
(*   基准：Main/Live 同名件（全程只读零改）；语句面/定理名/依赖面/      *)
(*   声明序与基准逐字守恒，仅换标注刀位的证明体。                      *)
(*   刀路（九槽落，两槽如实挂账）：弃 sumd_sum_* 出节转发件单点直喂，    *)
(*   unfold sumd_sumf（透明处方）后 enum 列表归纳原地重演——nil 支       *)
(*   定义性收口，cons 支双腿缝合（ext/le＝逐点腿＋归纳腿；linear＝      *)
(*   distrib 右分配中项链；add＝assoc-comm 换位内项链，弃不可达之       *)
(*   UpReqAlgebra req_plus_exchange 改纯字段链）；pos＝中转层脱钩        *)
(*   直取 sumd_list_sum_pos。挂账（原体保留）：A5 swap_cc（双层和       *)
(*   换序，内外双重重排超切片边界）；B6 eq_list（sumd_sum_eq_list        *)
(*   本体即定义性恒等 req_refl，任何替换体与之逐字同＝唯一形不化）。     *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblT6_UpReqSampling.v —— 假设消融战役 T6 批·席 a（T3a 移交同根余量前 ≤25 位之 11 位） *)
(* 辖区：UpReqSampling.v sumf 接口面（ReqUContraction/ReqBoundedSoftmax 两节）   *)
(* 放电母本：sumd_*@UpReqSumD                                                   *)
(*                                                              *)
(* 目的：对 UpReqSampling 两节的 sumf 接口面假设位逐条兑现消融定理：              *)
(*   假设位（对任意 sumf 算子的接口字段假定）在具体有限和实例                    *)
(*   sumf := sumd_sumf S enum（enum 列表和，UpReqSumD 放电机械）上               *)
(*   全部无条件成立——前提减薄为纯数据槽（枚举清单），假设位逐条消除。            *)
(*                                                              *)
(* 主件清单（11 件，前缀 uabT6_，逐件标注被消融位坐标与放电件）：                 *)
(*   §A ReqUContraction（L98-136）：                                   *)
(*    A1 uabT6_usamp_sum_ext      ←L105 sum_ext    放电 sumd_sum_ext@UpReqSumD:112 *)
(*    A2 uabT6_usamp_sum_linear   ←L107 sum_linear 放电 sumd_sum_linear@:135 *)
(*    A3 uabT6_usamp_sum_add      ←L110 sum_add    放电 sumd_sum_add@:161 *)
(*    A4 uabT6_usamp_sum_le       ←L113 sum_le     放电 sumd_sum_le@:203 *)
(*    A5 uabT6_usamp_sum_swap_cc  ←L132 sum_swap_cc 放电 sumd_sum_swap@:384 *)
(*        （swap 特形：f 双标函数参 f : S -> S -> R，内外两层 sumf 实例位；     *)
(*          T3a 移交单注意位预勘命中——先 Check 出节签名再落语句，              *)
(*          sumd_sum_swap 出节形与本件语句面逐字同构）                        *)
(*   §B ReqBoundedSoftmax（L700-747）：                                *)
(*    B1 uabT6_bsoft_sum_ext      ←L707 sum_ext    放电 sumd_sum_ext@:112 *)
(*    B2 uabT6_bsoft_sum_linear   ←L709 sum_linear 放电 sumd_sum_linear@:135 *)
(*    B3 uabT6_bsoft_sum_pos      ←L712 sum_pos    放电 sumd_sum_pos@:233 *)
(*        （非空数据槽显式参：Not (enum = nil) 与 UpReqSumD 头注               *)
(*          「非空前提显式参」同形同阶；原假设位无此参）                      *)
(*    B4 uabT6_bsoft_sum_add      ←L714 sum_add    放电 sumd_sum_add@:161 *)
(*    B5 uabT6_bsoft_sum_le       ←L717 sum_le     放电 sumd_sum_le@:203 *)
(*    B6 uabT6_bsoft_sum_eq_list  ←L747 sum_eq_list 放电 sumd_sum_eq_list@:81 *)
(*        （eq_list 特形：结论为列表和桥——原节内引用节自持 Fixpoint           *)
(*          rsq_bs_list_sum，本件以 UpReqSumD 同形自持机械 sumd_list_sum      *)
(*          兑现（UpReqSumD 头注 L69「与 UpReqSampling bs_list_sum 同形        *)
(*          自持」），sumd_sum_eq_list 在具体实例上为定义性 req_refl 件；      *)
(*          移交单注意位预勘第二处命中，同先 Check 纪律落语句）               *)
(*                                                              *)
(* 分级：11 件全 N1（库内放电件直连：被消融假设在库内已有无条件形，               *)
(*   零施工登记坐标=上列放电件行号；证明体非平凡内容在放电件本体——              *)
(*   列表归纳链 sumd_list_sum_*@UpReqSumD，本件直连不注水）。                    *)
(*   一处诚实前提形态如实申报（不注水）：                                       *)
(*   · B3 pos 面＝非空数据槽显式参 Not (enum = nil)（UpReqSumD 头注             *)
(*     「非空前提显式参」同形同阶；签名变化 7 口径）。                          *)
(*   数据槽是供给面（具体实例 enum 清单天然携带）非逻辑假定。                    *)
(*   本批辖区无 zero_nonneg 面（无满射槽参形）；W 邻接位 L116/L719              *)
(*   abs_sum_le_h 属 §3-W1 墙件，未纳入、未触碰。                              *)
(*                                                              *)
(* 依赖（全部只读消费，原树零改）：CW_ConstructiveWorld_219、                   *)
(*   UpReqSumD（经其传递 UpReqAlgebra/UpReqDist）。                            *)
(*   语句面逐字抽取自现档 UpReqSampling.v（两树逐字节同验：                      *)
(*   Main/Live_X md5 同 2ce2c50a，2026-09-15 版，与 FA2 普查表行号              *)
(*   逐位核对一致），仅 sumf → sumd_sumf S enum 换实例位。                     *)
(*                                                              *)
(* 备注：语句面全集合层（req/le/lt 均集合值谓词）；公理面零新增；文尾逐件        *)
(*   Print Assumptions 收尾。四关留痕：Live_X/attn/logs/                        *)
(*   g{1..4}-UpAblT6_UpReqSampling.log。                                       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqSumD.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* ============ §A ReqUContraction（UpReqSampling.v L98-136） ============ *)
(* 原 Context {R}{RIS} + S + sumf；出节全参形：R 显式（RIS 隐式位经类          *)
(* 实例解析），sumf 换 sumd_sumf S enum 实例。                                *)

(* A1 ←L105 sum_ext（逐字：forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT6_usamp_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* A2 ←L107 sum_linear（逐字：forall (a : R) (f : S -> R), req (sumf (fun s : S => mult a (f s))) (mult a (sumf f))） *)
Theorem uabT6_usamp_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
             (mult a (plus (f x) (sumd_list_sum S f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum S f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum S f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
                (distrib a (f x) (sumd_list_sum S f t)))).
Qed.

(* A3 ←L110 sum_add（逐字：forall f g : S -> R, req (sumf (fun s : S => plus (f s) (g s))) (plus (sumf f) (sumf g))） *)
Theorem uabT6_usamp_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - (exact (req_trans (plus (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_refl (plus (f x) (g x))) IH) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (req_sym (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus_assoc (f x) (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (req_plus_compat (f x) (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus_assoc (g x) (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_trans (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (g x) (sumd_list_sum S f t)) (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t) (sumd_list_sum S g t) (plus_comm (g x) (sumd_list_sum S f t)) (req_refl (sumd_list_sum S g t))) (req_sym (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus_assoc (sumd_list_sum S f t) (g x) (sumd_list_sum S g t))))))) (plus_assoc (f x) (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))))).
Qed.

(* A4 ←L113 sum_le（逐字：forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g)） *)
Theorem uabT6_usamp_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* A5 ←L132 sum_swap_cc（swap 特形：双标函数参，内外两层 sumf 实例位全换；放电 sumd_sum_swap@384） *)
Theorem uabT6_usamp_sum_swap_cc :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f : S -> S -> R),
    req (sumd_sumf S enum (fun s : S => sumd_sumf S enum (fun s' : S => f s s')))
        (sumd_sumf S enum (fun s' : S => sumd_sumf S enum (fun s : S => f s s'))).
Proof.
  intros R RIS S enum f.
  exact (sumd_sum_swap S enum f).
Qed.

(* ============ §B ReqBoundedSoftmax（UpReqSampling.v L700-747） ============ *)

(* B1 ←L707 sum_ext *)
Theorem uabT6_bsoft_sum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* B2 ←L709 sum_linear *)
Theorem uabT6_bsoft_sum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - exact (req_trans
             (plus (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t))
             (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
             (mult a (plus (f x) (sumd_list_sum S f t)))
             (req_plus_compat (mult a (f x)) (mult a (f x))
                (sumd_list_sum S (fun s : S => mult a (f s)) t)
                (mult a (sumd_list_sum S f t))
                (req_refl (mult a (f x))) IH)
             (req_sym (mult a (plus (f x) (sumd_list_sum S f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S f t)))
                (distrib a (f x) (sumd_list_sum S f t)))).
Qed.

(* B3 ←L712 sum_pos（非空数据槽显式参，sumd_sum_pos@233 同形） *)
Theorem uabT6_bsoft_sum_pos :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros R RIS S enum Hne f H.
  unfold sumd_sumf.
  exact (sumd_list_sum_pos S f enum Hne H).
Qed.

(* B4 ←L714 sum_add *)
Theorem uabT6_bsoft_sum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - (exact (req_trans (plus (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t)) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x)) (sumd_list_sum S (fun s : S => plus (f s) (g s)) t) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_refl (plus (f x) (g x))) IH) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (plus (plus (f x) (sumd_list_sum S f t)) (plus (g x) (sumd_list_sum S g t))) (req_trans (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (f x) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))) (req_sym (plus (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (plus (plus (f x) (g x)) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus_assoc (f x) (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t)))) (req_plus_compat (f x) (f x) (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_refl (f x)) (req_trans (plus (g x) (plus (sumd_list_sum S f t) (sumd_list_sum S g t))) (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus_assoc (g x) (sumd_list_sum S f t) (sumd_list_sum S g t)) (req_trans (plus (plus (g x) (sumd_list_sum S f t)) (sumd_list_sum S g t)) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (req_plus_compat (plus (g x) (sumd_list_sum S f t)) (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t) (sumd_list_sum S g t) (plus_comm (g x) (sumd_list_sum S f t)) (req_refl (sumd_list_sum S g t))) (req_sym (plus (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t))) (plus (plus (sumd_list_sum S f t) (g x)) (sumd_list_sum S g t)) (plus_assoc (sumd_list_sum S f t) (g x) (sumd_list_sum S g t))))))) (plus_assoc (f x) (sumd_list_sum S f t) (plus (g x) (sumd_list_sum S g t)))))).
Qed.

(* B5 ←L717 sum_le *)
Theorem uabT6_bsoft_sum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  unfold sumd_sumf.
  induction enum as [| x t IH].
  - exact (le_refl zero).
  - exact (le_plus_compat (f x) (g x) (sumd_list_sum S f t)
             (sumd_list_sum S g t) (H x) IH).
Qed.

(* B6 ←L747 sum_eq_list（eq_list 特形：列表和桥，UpReqSumD 同形自持机械 sumd_list_sum 兑现；放电 sumd_sum_eq_list@81） *)
Theorem uabT6_bsoft_sum_eq_list :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (g : S -> R),
    req (sumd_sumf S enum g) (sumd_list_sum S g enum).
Proof.
  intros R RIS S enum g.
  exact (sumd_sum_eq_list S enum g).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT6_usamp_sum_ext.
Print Assumptions uabT6_usamp_sum_linear.
Print Assumptions uabT6_usamp_sum_add.
Print Assumptions uabT6_usamp_sum_le.
Print Assumptions uabT6_usamp_sum_swap_cc.
Print Assumptions uabT6_bsoft_sum_ext.
Print Assumptions uabT6_bsoft_sum_linear.
Print Assumptions uabT6_bsoft_sum_pos.
Print Assumptions uabT6_bsoft_sum_add.
Print Assumptions uabT6_bsoft_sum_le.
Print Assumptions uabT6_bsoft_sum_eq_list.
