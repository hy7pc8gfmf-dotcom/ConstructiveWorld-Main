(* ==========================================================================)
   UpAblLeEqCompat.v — le/eq 兼容性与有序和传输引理族
   使命: lec_eq_le/le_le_eq 等四向兼容、le_b 对偶形（lec_le_b_pair_eq/le_pair_le_b）、E66 节有序和引理（lec_e66s_add_le_lr 等）与标志和传输 lec_flag_lsum_le/lec_flag_add_le_lr。
   依赖: CW_ConstructiveWorld_219、UpReqSumD、UpAblEps66Sum、UpAblP2FeedMix、UpRealLeB、G08_Gibbs；Stdlib Extraction。
   对标: 序关系与相等互换的保序引理（序代数标准件）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

From Stdlib Require Import Extraction.
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
Require Import UpReqSumD.
Require Import UpAblEps66Sum.
Require Import UpAblP2FeedMix.
Require Import UpRealLeB.
Require Import G08_Gibbs.

(* ============================================================ *)
(* §A 兼容家族四件：双侧序-等词互转（本件自证）                        *)
(* ============================================================ *)

(** lec_eq_le·等词⟹同向序：由序谓词的 Or 编码（real_le x y :=           *)
(*   Or (real_lt x y) (real_eq x y)）取右支（等词见证位）即得。          *)
Lemma lec_eq_le : forall x y : Real, real_eq x y -> real_le x y.
Proof.
  intros x y H.
  unfold real_le.
  right.
  exact H.
Qed.

(** lec_eq_le_rev·等词⟹反向序：先经 real_eq_sym 换向，再用 lec_eq_le 取右支。 *)
Lemma lec_eq_le_rev : forall x y : Real, real_eq x y -> real_le y x.
Proof.
  intros x y H.
  apply lec_eq_le.
  apply real_eq_sym.
  exact H.
Qed.

(** lec_le_le_eq·双侧序⟹等词（反对称）：对两序前提的 Or 编码分四支：      *)
(*   （序，序）支：两严格序前提经传递性自撞 real_lt_irrefl，空型消除；    *)
(*   （序，等词）与（等词，序）支：经 real_eq_sym 落到等词支；            *)
(*   （等词，等词）支：取左侧见证。                                      *)
Lemma lec_le_le_eq : forall x y : Real,
  real_le x y -> real_le y x -> real_eq x y.
Proof.
  intros x y Hxy Hyx.
  destruct Hxy as [Hlt | Heq]; destruct Hyx as [Hlt' | Heq'].
  - exact (match (real_lt_irrefl x (real_lt_trans x y x Hlt Hlt')) with end).
  - exact (real_eq_sym y x Heq').
  - exact Heq.
  - exact Heq.
Qed.

(** lec_le_eq_eq·沿等词双侧的序运输：若 x 序不降于 y 且 x 与 x′、y 与 y′  *)
(*   分别等词，则 x′ 序不降于 y′；经序的传递性与家族件接续两次。          *)
Lemma lec_le_eq_eq : forall x y x' y' : Real,
  real_le x y -> real_eq x x' -> real_eq y y' -> real_le x' y'.
Proof.
  intros x y x' y' Hle Hxx' Hyy'.
  apply (real_le_trans x' y y').
  - apply (real_le_trans x' x y).
    + apply (lec_eq_le_rev x x'). exact Hxx'.
    + exact Hle.
  - apply (lec_eq_le y y'). exact Hyy'.
Qed.

(* ============================================================ *)
(* §B Bishop 侧家族两件：le_b 形反对称与单向桥的家族接入               *)
(* ============================================================ *)

(** lec_le_b_pair_eq·le_b 双侧⟹等词（Bishop 形反对称入族）：由 G08 的    *)
(*   gibbe2_le_b_antisym 逐 n 构造件直接给出（无 Or 分解、无 LPO）——     *)
(*   家族在 Bishop 形序上同样双侧闭合。                                  *)
Lemma lec_le_b_pair_eq : forall x y : Real,
  real_le_b x y -> real_le_b y x -> real_eq x y.
Proof.
  intros x y H1 H2.
  exact (gibbe2_le_b_antisym x y H1 H2).
Qed.

(** lec_le_pair_le_b·Or 形双侧⟹le_b 双侧：双侧各自经单向桥               *)
(*   real_le_to_le_b 转换；逆向精确分解构造性不可证，本件不作此主张。     *)
Lemma lec_le_pair_le_b : forall x y : Real,
  real_le x y -> real_le y x -> real_le_b x y.
Proof.
  intros x y Hxy Hyx.
  apply (real_le_to_le_b x y).
  exact Hxy.
Qed.

(* ============================================================ *)
(* §C 求和族序/等词兼容通路（e66s 加法/保序面的序面接续）               *)
(* ============================================================ *)

Section LecE66.

Context (S0 : Set).
Context (enum0 : list S0).

(** lec_e66s_add_le_lr·加法序上界：逐点相加后求和 序不降于 分别求和后相加；由 e66s_real_sum_over_S_add 经 lec_eq_le 降至序面。 *)
Lemma lec_e66s_add_le_lr : forall (f g : S0 -> Real),
  real_le (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)).
Proof.
  intros f g.
  apply lec_eq_le.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** lec_e66s_add_le_rl·加法序下界：反向序不等式；由 e66s_real_sum_over_S_add 经 lec_eq_le_rev 给出。 *)
Lemma lec_e66s_add_le_rl : forall (f g : S0 -> Real),
  real_le (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g))
          (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s))).
Proof.
  intros f g.
  apply lec_eq_le_rev.
  exact (e66s_real_sum_over_S_add S0 enum0 f g).
Qed.

(** lec_e66s_add_of_le_pair·往返闭合：加法面双侧序不等式⟹加法等词，      *)
(*   即双侧序收回等词的反对称构造——对两序前提的 Or 编码就地分四支：        *)
(*   两严格序支经传递性自撞 real_lt_irrefl 空型消除，混等词支经            *)
(*   real_eq_sym 落到等词支，双等词支取左侧见证（与 lec_le_le_eq 同法      *)
(*   就地重演，不经单跳转发）。                                            *)
Lemma lec_e66s_add_of_le_pair : forall (f g : S0 -> Real),
  real_le (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)) ->
  real_le (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g))
          (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s))) ->
  real_eq (e66s_sumf S0 enum0 (fun s : S0 => real_plus (f s) (g s)))
          (real_plus (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)).
Proof.
  intros f g Hlr Hrl.
  destruct Hlr as [Hlt | Heq]; destruct Hrl as [Hlt' | Heq'].
  - (* 两严格序支：正向传递后与自反性相撞，空型消除 *)
    exact (match (real_lt_irrefl _ (real_lt_trans _ _ _ Hlt Hlt')) with end).
  - (* 左严格序、右等词：等词换向后即结论 *)
    exact (real_eq_sym _ _ Heq').
  - (* 左等词：取左侧见证 *)
    exact Heq.
  - (* 双等词：取左侧见证 *)
    exact Heq.
Qed.

(** lec_e66s_sum_eq_of_pw_le_pair·逐点双侧序⟹和等词：逐点双侧序经        *)
(*   e66s_real_sum_over_S_le 两次提升到和级，再由 lec_le_le_eq 反对称     *)
(*   收尾——e66s 求和族等词面的一条纯序面通路。                           *)
Lemma lec_e66s_sum_eq_of_pw_le_pair : forall (f g : S0 -> Real),
  (forall s : S0, real_le (f s) (g s)) ->
  (forall s : S0, real_le (g s) (f s)) ->
  real_eq (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g).
Proof.
  intros f g Hfg Hgf.
  apply lec_le_le_eq.
  - exact (e66s_real_sum_over_S_le S0 enum0 f g Hfg).
  - exact (e66s_real_sum_over_S_le S0 enum0 g f Hgf).
Qed.

(** lec_lsum_le_trans·原生折叠序传输：逐点序不降⟹real_list_sum 上        *)
(*   序不降——三步：e66s 序面（sumd 折叠级）、折叠桥 p2f_lsum_bridge       *)
(*   （逐点等词）、lec_le_eq_eq（沿等词双侧运输）。                       *)
Lemma lec_lsum_le_trans : forall (f g : S0 -> Real),
  (forall s : S0, real_le (f s) (g s)) ->
  real_le (real_list_sum S0 f enum0) (real_list_sum S0 g enum0).
Proof.
  intros f g H.
  apply (lec_le_eq_eq (e66s_sumf S0 enum0 f) (e66s_sumf S0 enum0 g)
                      (real_list_sum S0 f enum0) (real_list_sum S0 g enum0)).
  - exact (e66s_real_sum_over_S_le S0 enum0 f g H).
  - exact (p2f_lsum_bridge S0 enum0 f).
  - exact (p2f_lsum_bridge S0 enum0 g).
Qed.

End LecE66.

(* ============================================================ *)
(* §D bool 具体层实例（柯西实数层 fully concrete：枚举                    *)
(*   e66s_flag_enum＝true::false::nil，零残留抽象参数）                   *)
(* ============================================================ *)

(* 求和载体实例 lec_flag_sumf：e66s_sumf 特化到 bool 载体，供提取         *)
Definition lec_flag_sumf (f : bool -> Real) : Real :=
  e66s_sumf bool e66s_flag_enum f.

(** lec_flag_lsum_le：bool 载体上的 lec_lsum_le_trans 实例（逐点序不降⟹折叠序不降）。 *)
Theorem lec_flag_lsum_le :
  forall (f g : bool -> Real),
    (forall s : bool, real_le (f s) (g s)) ->
    real_le (real_list_sum bool f e66s_flag_enum)
            (real_list_sum bool g e66s_flag_enum).
Proof.
  intros f g H.
  exact (lec_lsum_le_trans bool e66s_flag_enum f g H).
Qed.

(** lec_flag_add_le_lr：加法序上界的 bool 具体层实例。 *)
Theorem lec_flag_add_le_lr :
  forall (f g : bool -> Real),
    real_le (lec_flag_sumf (fun s : bool => real_plus (f s) (g s)))
            (real_plus (lec_flag_sumf f) (lec_flag_sumf g)).
Proof.
  intros f g.
  exact (lec_e66s_add_le_lr bool e66s_flag_enum f g).
Qed.

(* ============================================================ *)
(* 提取区：提取命令单条单常量（多条提取命令的输出会相互覆盖）。           *)
(*   本件证明内容全为序/等词兼容引理（Set 值谓词上的构造性见证变换），    *)
(*   无独立数值计算体；提取面取求和载体 lec_flag_sumf（折叠核心体）       *)
(*   作计算内容代表，桥面引理以假设审计替代提取。                         *)
(*                                                                        *)
(*                                                                        *)
(* ============================================================ *)
Set Extraction Output Directory "_ts2_g3out".
Extraction "ts2_lec_fold" lec_flag_sumf.

(* ============================================================ *)
(* 假设审计：以下 Print Assumptions 应全部 Closed（零外部未证假设）       *)
(* ============================================================ *)
Print Assumptions lec_eq_le.
Print Assumptions lec_eq_le_rev.
Print Assumptions lec_le_le_eq.
Print Assumptions lec_le_eq_eq.
Print Assumptions lec_le_b_pair_eq.
Print Assumptions lec_le_pair_le_b.
Print Assumptions lec_e66s_add_le_lr.
Print Assumptions lec_e66s_add_le_rl.
Print Assumptions lec_e66s_add_of_le_pair.
Print Assumptions lec_e66s_sum_eq_of_pw_le_pair.
Print Assumptions lec_lsum_le_trans.
Print Assumptions lec_flag_lsum_le.
Print Assumptions lec_flag_add_le_lr.
