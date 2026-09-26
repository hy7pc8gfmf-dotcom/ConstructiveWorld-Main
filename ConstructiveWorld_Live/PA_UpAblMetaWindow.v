(* ============================================================
   使命：本件数学使命叙述见下方原头注首段（既有件注记型头注整编候后波）。
   依赖：见原头注 Require 面与依赖段。
   对标：见原头注来源/对标行。
   构造性：纯构造性、零承认件（详见原头注红线自审段）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)
(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   mwi_degenerate_collapse_uniform（原 L160，1 句玩具证）               *)
(*   mwi_Kunif_rows_eq（原 L156，2 句玩具证）                             *)
(*   mwi_Kunif_row（原 L152，2 句玩具证）                                 *)
(*   mwi_abs_zero（原 L57，1 句玩具证）                                   *)
(*   mwi_req_minus_self（原 L50，3 句玩具证）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblMetaWindow.v —— M4 件：World3 非退化核世界的双侧混合窗定理                  *)
(*                                                              *)
(* 【主件】mtw_window_two_sided：双侧合取窗定理（S01 基座 Set 层合取承载）。         *)
(*   退化侧（退化世界）：凡核行全同的行随机核，点质量对一步即退化为行分布——               *)
(*     一步演化后两态分布逐点等于首行，TV == 0，混合窗退化为零。                    *)
(*   存在侧（非退化世界）：World3（行互异+精确衰减）供体两个合取肢——                     *)
(*     mtw_tv_exact_iter（TV(n) == (1/2)^n·TV₀ 精确幂律）与                        *)
(*     mtw_no_mixing_below（budget < (1/2)^n·TV₀ ⟹ budget < TV(n) 预算下界），      *)
(*   合取即「混合窗恰存在于非退化世界；退化世界以 TV(1)=0 显式退化」。               *)
(*                                                              *)
(* 【供体依存账（只读，零改）】UpAblMetaWorld3（N4 件）：mtw_step/mtw_titer/         *)
(*   mtw_tv/mtw_mu0/mtw_nu0/mtw_half/mtw_sumf/req_r_pow 机器面 +                   *)
(*   mtw_tv_exact_iter/mtw_no_mixing_below/mtw_hh_one 三肢。                        *)
(*   退化侧不依存 cf2 链（UpReqConcFin2/UpAblMetaLow）——其闭包携带 stdlib 经典       *)
(*   公理继承面；本件退化情形以泛型条件定理自证（比单世界实例更强：凡退化核皆退化）。      *)
(*                                                              *)
(* 【红线自审】零承认件；零经典逻辑；零新假设（前提位全显式定理参数）；                 *)
(*   语句面全 Set 值（req/lt/le/Not 均基座 Set 层别名），无紫层泄露；                  *)
(*   全件 Defined 收束可提取；基座代数桥（左零乘/自差零/零绝对值）本件自建。           *)
(* 编译配方：9.1 直调轨，unset COQLIB/ROCQLIB，-Q . ""，cpu_guard CoreN 2。         *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqSampling.
Require Import UpAblMetaWorld3.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* §1 退化侧机器：泛型核一步演化 + 基座代数桥                                      *)
(* ============================================================ *)

(* 泛型一步演化器：与供体 mtw_step 同构，核 K 提升为显式参数 *)
Definition mwi_step (K : bool -> bool -> Real) (mu : bool -> Real) (s' : bool) : Real :=
  plus (mult (mu true) (K true s')) (mult (mu false) (K false s')).

(* 左零乘：0·a == 0（基座 mult_zero 仅右零形，comm 桥） *)
Lemma mwi_mult_zero_l : forall a : Real, req (mult zero a) zero.
Proof.
  intro a.
  apply (req_trans (mult zero a) (mult a zero) zero).
  - exact (mult_comm zero a).
  - exact (mult_zero a).
Defined.

(* 自差为零：a − a == 0 *)
Lemma mwi_req_minus_self : forall a : Real, req (req_minus a a) zero.
Proof.
  intro a.
  unfold req_minus.
  exact (plus_opp a).
Defined.

(* 零的绝对值：|0| == 0 *)
Lemma mwi_abs_zero : req (abs zero) zero.
Proof. exact abs_zero. Defined.

(* ============================================================ *)
(* §2 退化面定理：核行全同 ⟹ 一步退化（TV == 0，混合窗退化侧）                      *)
(*   注：行随机前提为世界资格前提；退化本体只需行全同（两行同为首行）。                *)
(* ============================================================ *)

Theorem mwi_collapse_row_equal :
  forall K : bool -> bool -> Real,
    (forall s : bool, req (plus (K s true) (K s false)) one) ->
    (forall s s' : bool, req (K s s') (K true s')) ->
    req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero.
Proof.
  intros K Hrow Heq.
  (* 质量对在核 K 下一步演化逐点等于首行：mu0 侧 = 1·K(t,·) + 0·K(f,·) *)
  assert (Ht : forall s' : bool, req (mwi_step K mtw_mu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_mu0 s')
                     (plus (K true s') zero)
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_mu0 true) (K true s')) (K true s')
               (mult (mtw_mu0 false) (K false s')) zero
               (req_mult_one_l (K true s'))
               (mwi_mult_zero_l (K false s'))).
    - exact (plus_zero (K true s')). }
  (* nu0 侧 = 0·K(t,·) + 1·K(f,·) = K(f,·) = K(t,·)（行全同） *)
  assert (Hf : forall s' : bool, req (mwi_step K mtw_nu0 s') (K true s')).
  { intro s'.
    apply (req_trans (mwi_step K mtw_nu0 s')
                     (plus zero (K false s'))
                     (K true s')).
    - exact (req_plus_compat
               (mult (mtw_nu0 true) (K true s')) zero
               (mult (mtw_nu0 false) (K false s')) (K false s')
               (mwi_mult_zero_l (K true s'))
               (req_mult_one_l (K false s'))).
    - exact (req_trans (plus zero (K false s')) (K false s') (K true s')
               (req_plus_zero_l (K false s'))
               (Heq false s')). }
  (* 逐点差为零 ⟹ 逐点绝对值为零 *)
  assert (Hz : forall s' : bool,
           req (abs (req_minus (mwi_step K mtw_mu0 s')
                               (mwi_step K mtw_nu0 s'))) zero).
  { intro s'.
    apply (req_trans
             (abs (req_minus (mwi_step K mtw_mu0 s')
                             (mwi_step K mtw_nu0 s')))
             (abs zero) zero).
    - exact (req_abs_compat
               (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
               zero
               (req_trans
                  (req_minus (mwi_step K mtw_mu0 s') (mwi_step K mtw_nu0 s'))
                  (req_minus (K true s') (K true s'))
                  zero
                  (req_plus_compat
                     (mwi_step K mtw_mu0 s') (K true s')
                     (opp (mwi_step K mtw_nu0 s')) (opp (K true s'))
                     (Ht s')
                     (req_opp_compat (mwi_step K mtw_nu0 s') (K true s')
                               (Hf s')))
                  (mwi_req_minus_self (K true s')))).
    - exact mwi_abs_zero. }
  (* TV = (1/2)·(0+0) = 0 *)
  apply (req_trans (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0))
                   (mult mtw_half zero) zero).
  - exact (req_mult_compat mtw_half mtw_half
             (mtw_sumf (fun s : bool =>
                   abs (req_minus (mwi_step K mtw_mu0 s)
                                  (mwi_step K mtw_nu0 s))))
             zero
             (req_refl mtw_half)
             (req_trans
                (mtw_sumf (fun s : bool =>
                      abs (req_minus (mwi_step K mtw_mu0 s)
                                     (mwi_step K mtw_nu0 s))))
                (plus zero zero) zero
                (req_plus_compat
                   (abs (req_minus (mwi_step K mtw_mu0 true)
                                   (mwi_step K mtw_nu0 true))) zero
                   (abs (req_minus (mwi_step K mtw_mu0 false)
                                   (mwi_step K mtw_nu0 false))) zero
                   (Hz true) (Hz false))
                (req_plus_zero_l zero))).
  - exact (mult_zero mtw_half).
Defined.

(* ============================================================ *)
(* §3 退化世界显式实例：均匀核（每行 (1/2,1/2)，行全同）TV(1) == 0                  *)
(* ============================================================ *)

Definition mwi_Kunif (s s' : bool) : Real := mtw_half.

Lemma mwi_Kunif_row : forall s : bool,
  req (plus (mwi_Kunif s true) (mwi_Kunif s false)) one.
Proof. intro s. exact mtw_hh_one. Defined.

Lemma mwi_Kunif_rows_eq : forall s s' : bool,
  req (mwi_Kunif s s') (mwi_Kunif true s').
Proof. intros s s'. exact (req_refl mtw_half). Defined.

Theorem mwi_degenerate_collapse_uniform :
  req (mtw_tv (mwi_step mwi_Kunif mtw_mu0) (mwi_step mwi_Kunif mtw_nu0)) zero.
Proof.
  exact (mwi_collapse_row_equal mwi_Kunif mwi_Kunif_row mwi_Kunif_rows_eq).
Defined.

(* ============================================================ *)
(* §4 主件：双侧混合窗定理（S01 基座 Set 层合取承载）                               *)
(*   左肢=退化侧（退化世界窗退化）；右肢=存在侧（非退化世界窗真实存在：               *)
(*   精确幂律 + 预算下界两个合取肢合取）。                                              *)
(* ============================================================ *)

Theorem mtw_window_two_sided :
  And
    (* 退化侧：核行全同的行随机核 ⟹ 一步退化 TV == 0 *)
    (forall K : bool -> bool -> Real,
       (forall s : bool, req (plus (K s true) (K s false)) one) ->
       (forall s s' : bool, req (K s s') (K true s')) ->
       req (mtw_tv (mwi_step K mtw_mu0) (mwi_step K mtw_nu0)) zero)
    (* 存在侧：非退化世界（World3）精确幂律 + 混合窗预算下界 *)
    (And
       (forall n : nat,
          req (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0))
              (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)))
       (forall (n : nat) (B : Real),
          lt B (mult (req_r_pow mtw_half n) (mtw_tv mtw_mu0 mtw_nu0)) ->
          lt B (mtw_tv (mtw_titer n mtw_mu0) (mtw_titer n mtw_nu0)))).
Proof.
  split.
  - exact mwi_collapse_row_equal.
  - split.
    + exact mtw_tv_exact_iter.
    + exact mtw_no_mixing_below.
Defined.

(* ============================================================ *)
(* 四关自检：全件 Closed（零新假设）                                              *)
(* ============================================================ *)

Print Assumptions mwi_step.
Print Assumptions mwi_mult_zero_l.
Print Assumptions mwi_req_minus_self.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_collapse_row_equal.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mtw_window_two_sided.

(* PA 追印段（ 核验副本件） *)
Print Assumptions mwi_degenerate_collapse_uniform.
Print Assumptions mwi_Kunif_rows_eq.
Print Assumptions mwi_Kunif_row.
Print Assumptions mwi_abs_zero.
Print Assumptions mwi_req_minus_self.
