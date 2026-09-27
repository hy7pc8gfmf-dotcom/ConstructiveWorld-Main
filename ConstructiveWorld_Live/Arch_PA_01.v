(* ==========================================================================)
   Arch_PA_01.v -- 命题族集注与实例化承载
   使命：本件形式化以下命题族：uabT1_fw_ssum_ext、uabT1_fw_ssum_add、uabT1_fw_ssum_linear、uabT1_fw_ssum_le、uabT1_fw_ssum_pos、uabd1s4_two、uabd1s4_two_pos、uabd1s4_half、uabd1s4_half_pos。
   依赖：件内 Require 声明面所列库件。
   构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载，零 Prop 泄露。
   编译配方：Rocq 9.1 直调 coqc -native-compiler no -q -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

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
From Stdlib Require Import List.
Require Import AttnDoeblin.
Require Import fa53_compat_abs.
Require Import AbsLeId.
Require Import UpReqFEPAttn.
Require Import UpReqRealFEP.
From Stdlib Require Import Extraction.
Require Import UpReqAlgebra.
Require Import UpReqDist.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.

(* ================= §1 uabT1_fw_ssum_ext 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* G1 ←  ssum_ext（逐字：forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g)） *)
Theorem uabT1_fw_ssum_ext :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, req (f s) (g s)) -> req (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_ext S enum f g H).
Qed.

(* G2 ←L81 ssum_add *)
Theorem uabT1_fw_ssum_add :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    req (sumd_sumf S enum (fun s : S => plus (f s) (g s)))
        (plus (sumd_sumf S enum f) (sumd_sumf S enum g)).
Proof.
  intros R RIS S enum f g.
  exact (sumd_sum_add S enum f g).
Qed.

(* G3 ←L84 ssum_linear *)
Theorem uabT1_fw_ssum_linear :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (a : R) (f : S -> R),
    req (sumd_sumf S enum (fun s : S => mult a (f s))) (mult a (sumd_sumf S enum f)).
Proof.
  intros R RIS S enum a f.
  exact (sumd_sum_linear S enum a f).
Qed.

(* G4 ←L87 ssum_le *)
Theorem uabT1_fw_ssum_le :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S)
    (f g : S -> R),
    (forall s : S, le (f s) (g s)) -> le (sumd_sumf S enum f) (sumd_sumf S enum g).
Proof.
  intros R RIS S enum f g H.
  exact (sumd_sum_le S enum f g H).
Qed.

(* G5 ←L89 ssum_pos（非空数据槽显式参，sumd_sum_pos@233 同形） *)
Theorem uabT1_fw_ssum_pos :
  forall (R : Set) {RIS : RealInterfaceEnhancedSetoid R} (S : Set) (enum : list S),
    Not (enum = nil) ->
    forall f : S -> R,
      (forall s : S, lt zero (f s)) -> lt zero (sumd_sumf S enum f).
Proof.
  intros R RIS S enum Hne f H.
  exact (sumd_sum_pos S enum f Hne H).
Qed.

(* ============ PA 收尾段（逐件 Closed 判读） ============ *)
Print Assumptions uabT1_fw_ssum_ext.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_pos.

Print Assumptions uabT1_fw_ssum_pos.
Print Assumptions uabT1_fw_ssum_le.
Print Assumptions uabT1_fw_ssum_linear.
Print Assumptions uabT1_fw_ssum_add.
Print Assumptions uabT1_fw_ssum_ext.
(* ================= §2 uabd1s4_two 族 ================= *)
(* ============ 供给基础模块：两点均匀半函数（Real 载体版 fa57 两点器） ============ *)

Definition uabd1s4_two : Real := real_plus real_one real_one.

Lemma uabd1s4_two_pos : real_lt real_zero uabd1s4_two.
Proof.
  exact real_two_pos.
Qed.

Definition uabd1s4_half : Real := real_inv_pos uabd1s4_two uabd1s4_two_pos.

Lemma uabd1s4_half_pos : real_lt real_zero uabd1s4_half.
Proof.
  exact (real_inv_pos_pos uabd1s4_two uabd1s4_two_pos).
Qed.

(* 归一链核心肢：半+半 == 壹（fa57_half_plus_half 的 Real 载体副本） *)
Lemma uabd1s4_half_plus_half : real_eq (real_plus uabd1s4_half uabd1s4_half) real_one.
Proof.
  exact (real_eq_trans           (real_plus uabd1s4_half uabd1s4_half)           (real_mult uabd1s4_half uabd1s4_two)           real_one           (real_eq_trans              (real_plus uabd1s4_half uabd1s4_half)              (real_plus (real_mult uabd1s4_half real_one)                         (real_mult uabd1s4_half real_one))              (real_mult uabd1s4_half uabd1s4_two)              (RealSetoid.real_eq_plus_compat uabd1s4_half uabd1s4_half                                   (real_mult uabd1s4_half real_one)                                   (real_mult uabd1s4_half real_one)                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half))                                   (real_eq_sym (real_mult uabd1s4_half real_one) uabd1s4_half (real_mult_one uabd1s4_half)))              (real_eq_sym                 (real_mult uabd1s4_half uabd1s4_two)                 (real_plus (real_mult uabd1s4_half real_one)                            (real_mult uabd1s4_half real_one))                 (real_distrib uabd1s4_half real_one real_one)))           (real_eq_trans              (real_mult uabd1s4_half uabd1s4_two)              (real_mult uabd1s4_two uabd1s4_half)              real_one              (real_mult_comm uabd1s4_half uabd1s4_two)              (real_inv_pos_correct uabd1s4_two uabd1s4_two_pos))).
Qed.

(* Hpitn 供给肢：k:=1、pit:=半函数 时的两态归一（列表和按 cons 折叠 δ/iota 展开） *)
Lemma uabd1s4_half_sum_two :
  real_eq (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2)) real_one.
Proof.
  exact (real_eq_trans           (real_list_sum nat (fun _ : nat => uabd1s4_half) (List.seq 0 2))           (real_plus uabd1s4_half uabd1s4_half)           real_one           (RealSetoid.real_eq_plus_compat uabd1s4_half (real_plus uabd1s4_half real_zero)                                uabd1s4_half uabd1s4_half                                (real_eq_refl uabd1s4_half)                                (real_plus_zero uabd1s4_half))           uabd1s4_half_plus_half).
Qed.


Inductive uabd1s4_ske_pack12 : Set :=
| uabd1s4_ske_pack12_intro :
    forall k : nat,
      forall beta : Real,
        real_lt real_zero beta ->
        forall r : nat -> Real,
          forall eta : Real,
            real_lt real_zero eta ->
            real_le eta real_one ->
            forall pit : nat -> Real,
              (forall i : nat, real_lt real_zero (pit i)) ->
              real_eq (real_list_sum nat pit (List.seq 0 (Datatypes.S k))) real_one ->
              forall piref : nat -> Real,
                (forall i : nat, real_lt real_zero (piref i)) ->
                uabd1s4_ske_pack12.

(* ============ 依赖模块：两点均匀实例一次喂定 12 槽 ============ *)

Theorem uabd1s4_ske_pack12_supplied : uabd1s4_ske_pack12.
Proof.
  exact (uabd1s4_ske_pack12_intro 1%nat           real_one real_lt_zero_one           (fun _ : nat => real_zero)           real_one real_lt_zero_one (real_le_refl real_one)           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)           uabd1s4_half_sum_two           (fun _ : nat => uabd1s4_half)           (fun _ : nat => uabd1s4_half_pos)).
Qed.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions uabd1s4_two_pos.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_ske_pack12_supplied.

(* PA 追印段（ 核验副本件） *)
Print Assumptions uabd1s4_ske_pack12_supplied.
Print Assumptions uabd1s4_half_sum_two.
Print Assumptions uabd1s4_half_plus_half.
Print Assumptions uabd1s4_half_pos.
Print Assumptions uabd1s4_two_pos.
(* ================= §3 idt_list_sum 族 ================= *)
Import ListNotations.
Import RealInterfaceEnhancedMod.

(* Section：载体上下文与四槽同款（Context {RI}{SS} 裸名句法 =       *)
(* 宿主文件自身已证句法，S13/S15 RowView 同款）                     *)
Section IdSlotTranslate.

Context {RI : RealInterfaceEnhanced}.
Context {SS : StateSpace RI}.
Local Existing Instance RI_base.

(* ============ 桥 1：RI 载体列表折叠机 + 定义性实例化消解实例 ============ *)
(* Enhanced 载体副本（字面同构翻译）；裸 zero/plus = @zero RI /     *)
(* @plus RI（宿主真机同接口）。                                     *)

Fixpoint idt_list_sum (f : S -> R) (l : list S) : R :=
  match l with
  | nil => @S01_BaseRing.zero RI
  | x :: t => @S01_BaseRing.plus RI (f x) (idt_list_sum f t)
  end.

(* sum_over_S 接口参数的定义性实例化消解实例（sumd_sumf 同位副本） *)
Definition idt_sumf (enum : list S) (f : S -> R) : R :=
  idt_list_sum f enum.

(* 桥 1 本体：Id 形钥匙桥——id_refl 定义性坍缩（零归纳零 rewrite；   *)
(* 与 CWE5 定理2 之 Id 载体同构件）。                               *)
Lemma idt_sum_eq_list :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (idt_list_sum g enum).
Proof.
  intros enum g.
  exact id_refl.
Qed.

(* ============ 桥 2：宿主出节真机一致桥（接口翻译件机侧） =========== *)
(* 出节机在 cons 具体形上 delta/zeta/iota 化简与在写机同构，         *)
(* id_cong2 逐步同余；nil 具体形 id_refl（转换墙免疫：不押中性       *)
(* 变元 conversion）。两宿主真机各一件：                             *)

Lemma idt_bs_list_sum_attn_agree :
  forall (f : S -> R) (l : list S),
    Id (idt_list_sum f l) (AttnDoeblin.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

Lemma idt_bs_list_sum_s13_agree :
  forall (f : S -> R) (l : list S),
    Id (idt_list_sum f l) (S13_NLiveAudit.bs_list_sum f l).
Proof.
  intros f l. induction l as [| x t IH].
  - exact id_refl.
  - exact (id_cong2 (@S01_BaseRing.plus RI) id_refl IH).
Qed.

(* ============ 四宿主核验定理（每槽一个） =========== *)
(* 语句 = 槽语句（sum_over_S := idt_sumf 实例化消解实例）对宿主出节真机；  *)
(* enum 由槽节 Variable 位升格为显式全称（更强诚实形）。喂法 =       *)
(* 桥 2 特化（idt_sumf 经 delta/beta 坍缩为 idt_list_sum，桥 1 同    *)
(* 式）。四定理即四槽 sum_eq_list 之可实现 witnesses，四依存位       *)

Theorem idt_slot_attdoeblin :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

Theorem idt_slot_g01 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (AttnDoeblin.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_attn_agree g enum).
Qed.

Theorem idt_slot_s13 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

Theorem idt_slot_s15 :
  forall (enum : list S) (g : S -> R),
    Id (idt_sumf enum g) (S13_NLiveAudit.bs_list_sum g enum).
Proof.
  intros enum g.
  exact (idt_bs_list_sum_s13_agree g enum).
Qed.

(* ============ G4 证据：七件全 Closed ============ *)
Print Assumptions idt_sum_eq_list.
Print Assumptions idt_bs_list_sum_attn_agree.
Print Assumptions idt_bs_list_sum_s13_agree.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_s15.

End IdSlotTranslate.

Print Assumptions idt_slot_s15.
Print Assumptions idt_slot_s13.
Print Assumptions idt_slot_g01.
Print Assumptions idt_slot_attdoeblin.
Print Assumptions idt_sum_eq_list.
(* ================= §4 uabd2_ali_abs_ge_zero_id_pai 族 ================= *)
(* 与 AbsLeId L43-54 同款语境（RI_base 实例解析投影裸名）；出节后  *)
(* RI0/DO0 消为显式头参（全参形，节后 Check 实证）。               *)
Section UabD2PairWorld.

Context {RI0 : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO0 : DecidableOrder RI0}.

Theorem uabd2_ali_abs_ge_zero_id_pair :
  forall a : R, le zero a -> Id (abs a) a.
Proof.
  intros a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI0 DO0 a Ha).
Qed.

End UabD2PairWorld.

(* 出节形实证（FA3 纪律6：节参消失不对称 Check 实证） *)
Check uabd2_ali_abs_ge_zero_id_pair.

Theorem uabd2_ali_abs_ge_zero_id_explicit :
  forall (RI1 : RealInterfaceEnhanced) (DO1 : DecidableOrder RI1)
         (a : @S01_BaseRing.R RI1),
    @S01_BaseRing.le RI1 (@S01_BaseRing.zero RI1) a ->
    @S01_BaseRing.Id (@S01_BaseRing.R RI1) (@S01_BaseRing.abs RI1 a) a.
Proof.
  intros RI1 DO1 a Ha.
  exact (@fa53_abs_ge_zero_id_dec RI1 DO1 a Ha).
Qed.

(* ============ ① RI 槽：具体 Real 载体直接匹配（N1，双形） =========== *)
(* 具体层 Require 置于抽象节后（AbsLeId L86 遮蔽注记同款）。       *)

(* real 面：槽语句字段映照载体形=N1 源文件 ali_real_abs_ge_zero_id   *)
Theorem uabd2_ri_real_abs_ge_zero_id :
  forall a : Real, real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* S07_RealSetoidExpLog.RealInterfaceEnhancedMod 模块（Locate 实证， *)
(*  节7 前缀同款）；le/zero/abs/req 四字段展开与 real_* 面       *)
(* delta/iota 可转换同体，同源文件闭合。                              *)
Theorem uabd2_ri_reqface_abs_ge_zero_id :
  forall a : Real,
    @RealInterfaceEnhancedMod.le Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.zero Real RealInterfaceEnhancedMod.RealEnhancedReal) a ->
    @RealInterfaceEnhancedMod.req Real RealInterfaceEnhancedMod.RealEnhancedReal
      (@RealInterfaceEnhancedMod.abs Real RealInterfaceEnhancedMod.RealEnhancedReal a) a.
Proof.
  exact ali_real_abs_ge_zero_id.
Qed.

(* ============ ③ DO 槽具体层：可构造面（字段5，T 档） ============ *)
(* 透明展开一行闭合，T 档显式登记（防注水口径，不计非平凡战果）。   *)
Theorem uabd2_do_ltle_iffdec_real :
  forall a b : Real,
    S01_BaseRing.Or (real_lt a b) (real_eq a b) -> real_le a b.
Proof.
  intros a b H.
  exact H.
Qed.

(* ---- 字段1-4 墙登记见文件头注（三分/非退化判定族，不发全实例件） ---- *)

(* ============ PA 自审段（G2 前置：逐件 Closed 判读） ============ *)
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_do_ltle_iffdec_real.

Print Assumptions uabd2_do_ltle_iffdec_real.
Print Assumptions uabd2_ri_reqface_abs_ge_zero_id.
Print Assumptions uabd2_ri_real_abs_ge_zero_id.
Print Assumptions uabd2_ali_abs_ge_zero_id_explicit.
Print Assumptions uabd2_ali_abs_ge_zero_id_pair.
(* ================= §5 uabd1s3_fep_st_Z 族 ================= *)
Import RealInterfaceEnhancedMod.

(* ---- 载体件：boltzmann 非正规和 Z 实例（sumd 引擎） ---- *)
Definition uabd1s3_fep_st_Z (S0 : Set) (enum0 : list S0)
  (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D) : Real :=
  sumd_sumf S0 enum0
    (fun s : S0 => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s))).

Lemma uabd1s3_fep_st_Z_pos :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D),
    real_lt real_zero (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos).
Proof.
  intros S0 enum0 Hne base_loss D D_pos.
  exact (sumd_sum_pos S0 enum0          (fun s : S0 => real_exp_neg (real_mult (real_inv_pos D D_pos) (base_loss s)))          Hne          (fun s : S0 => real_exp_neg_pos (real_mult (real_inv_pos D D_pos) (base_loss s)))).
Qed.

(* ---- 载体件：Boltzmann 分布 π 实例（real_boltzmann_dist_r 装配） ---- *)
Definition uabd1s3_fep_st_dist (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) (s : S0) : Real :=
  real_boltzmann_dist_r S0 base_loss D D_pos
    (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)
    (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos) s.

(* ---- 载体件：独立提议核 k(s,s'):=π(s')（与首参无关，fa56b 同构） ---- *)
Definition uabd1s3_fep_st_kernel (S0 : Set) (enum0 : list S0)
  (Hne : Not (enum0 = nil)) (base_loss : S0 -> Real) (D : Real)
  (D_pos : real_lt real_zero D) : S0 -> S0 -> Real :=
  fun _ s' => uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s'.

(* ---- 槽1 L82 real_partition_condition（源文件 req_fep_partition_condition *)
Theorem uabd1s3_fep_st_real_partition_condition :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (z0 : S0 -> Real) (T0 : Real) (HT0 : real_lt real_zero T0),
    real_eq (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_opp (real_mult (real_inv_pos T0 HT0) (z0 s)))))
            (sumd_sumf S0 enum0
              (fun s : S0 => real_exp_neg
                              (real_mult (real_inv_pos T0 HT0) (real_opp (z0 s))))).
Proof.
  intros S0 enum0 Hne z0 T0 HT0.
  exact (req_fep_partition_condition S0 (sumd_sumf S0 enum0)          (sumd_sum_ext S0 enum0) z0 T0 HT0).
Qed.

(* ---- 槽2 L95 real_transition_nonneg（real_boltzmann_dist_r_pos 严格形   *)
Theorem uabd1s3_fep_st_real_transition_nonneg :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_le real_zero (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s').
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  apply real_lt_le_iff.
  left.
  exact (real_boltzmann_dist_r_pos S0 base_loss D D_pos          (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)          (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos) s').
Qed.

(* ---- 槽3 L97 real_transition_normalization（rfep_boltzmann_normalized_real *)
(*    直接代入；partition 前提由 Z 定义件 real_eq_refl 承载） ---- *)
Theorem uabd1s3_fep_st_real_transition_normalization :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s : S0),
    real_eq (sumd_sumf S0 enum0
              (fun s' : S0 => uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            real_one.
Proof.
  intros S0 enum0 Hne base_loss D D_pos s.
  exact (rfep_boltzmann_normalized_real S0 (sumd_sumf S0 enum0)          (sumd_sum_ext S0 enum0) (sumd_sum_linear S0 enum0)          base_loss D D_pos          (uabd1s3_fep_st_Z S0 enum0 base_loss D D_pos)          (uabd1s3_fep_st_Z_pos S0 enum0 Hne base_loss D D_pos)          (real_eq_refl _)).
Qed.

(* ---- 槽4 L99 real_detailed_balance（fa56b 独立提议核副本，mult_comm 闭合） ---- *)
Theorem uabd1s3_fep_st_real_detailed_balance :
  forall (S0 : Set) (enum0 : list S0) (Hne : Not (enum0 = nil))
         (base_loss : S0 -> Real) (D : Real) (D_pos : real_lt real_zero D)
         (s s' : S0),
    real_eq (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s s'))
            (real_mult (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')
                       (uabd1s3_fep_st_kernel S0 enum0 Hne base_loss D D_pos s' s)).
Proof.
  intros S0 enum0 Hne base_loss D D_pos s s'.
  exact (real_mult_comm (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s)                        (uabd1s3_fep_st_dist S0 enum0 Hne base_loss D D_pos s')).
Qed.

Set Extraction Output Directory "_tuabd1s3_g3out".
Extraction "tuabd1s3_G3_fep_st_Z.ml" uabd1s3_fep_st_Z.

Print Assumptions uabd1s3_fep_st_Z_pos.
Print Assumptions uabd1s3_fep_st_real_partition_condition.
Print Assumptions uabd1s3_fep_st_real_transition_nonneg.
Print Assumptions uabd1s3_fep_st_real_transition_normalization.
Print Assumptions uabd1s3_fep_st_real_detailed_balance.

Print Assumptions uabd1s3_fep_st_real_detailed_balance.
Print Assumptions uabd1s3_fep_st_real_transition_normalization.
Print Assumptions uabd1s3_fep_st_real_transition_nonneg.
Print Assumptions uabd1s3_fep_st_real_partition_condition.
Print Assumptions uabd1s3_fep_st_Z_pos.
(* ================= §6 tmw_req_energy_exp_temp_mono 族 ================= *)
Import RealInterfaceEnhancedMod.

(* Section TmwMonoW2：宿主 Section FirewallReq 见证面与                 *)
(*   UpReqTempEntropy Section ReqTempEntropy 消解面之并集。             *)
(*   见证每型一个，宿主位/消解位同喂。                                  *)
Section TmwMonoW2.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.

(* ---- 求和面（宿主 ssum_* 与消解面 fsum_* 同型合并） ---- *)
Hypothesis tmw_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis tmw_sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis tmw_sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).
Hypothesis tmw_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Hypothesis tmw_sum_le :
  forall f g : S -> R, (forall s : S, le (f s) (g s)) -> le (sumf f) (sumf g).
Hypothesis tmw_sum_zero_nonneg :
  forall f : S -> R,
    (forall s : S, le zero (f s)) -> req (sumf f) zero ->
    forall s : S, req (f s) zero.

Variable base_loss : S -> R.

Hypothesis tmw_dist_log_inv_one_inv :
  forall (x : R) (Hx : lt zero x) (Hi : lt zero (inv_pos x Hx)),
    req (log (inv_pos x Hx) Hi) (opp (log x Hx)).
Hypothesis tmw_dist_log_exp_neg :
  forall u : R, req (log (exp_neg u) (exp_neg_pos u)) (opp u).
Hypothesis tmw_dist_log_le_linear :
  forall (x : R) (Hx : lt zero x), le (log x Hx) (req_minus x one).
Hypothesis tmw_dist_log_eq_linear :
  forall (x : R) (Hx : lt zero x),
    req (log x Hx) (req_minus x one) -> req x one.

(* ---- Z_temp 接口（宿主 req_Z_temp_spec 同位） ---- *)
Variable Z_temp : R -> R.
Hypothesis tmw_Z_temp_spec : forall (t : R) (Ht : lt zero t),
  req (Z_temp t) (sumf (fun s => exp_neg (mult (inv_pos t Ht) (base_loss s)))).

Theorem tmw_req_energy_exp_temp_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hbd).
Qed.

Theorem tmw_req_energy_exp_temp_strict_mono_cond :
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (inv_pos t1 Ht1) (inv_pos t2 Ht2)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros t1 t2 Ht1 Ht2 Hlt Hkl Hbd.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl Hbd).
Qed.

Theorem tmw_req_energy_exp_temp_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t1 Ht1)
     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss
                            Z_temp tmw_Z_temp_spec t2 Ht2).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (UpReqTempEntropy.req_energy_exp_temp_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(*   断言目标，依存位形自身）。                                         *)
Theorem tmw_req_energy_exp_temp_strict_mono_full :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  lt zero (req_relative_entropy S sumf
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt R RIS S sumf tmw_sum_pos base_loss
                                   Z_temp tmw_Z_temp_spec t1 Ht1)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t2 Ht2)
             (@UpFirewallReq.fw_bt_pos R RIS S sumf tmw_sum_pos base_loss
                                       Z_temp tmw_Z_temp_spec t1 Ht1)) ->
  lt zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt Hkl.
  exact (UpReqTempEntropy.req_energy_exp_temp_strict_mono           S sumf tmw_sum_ext tmw_sum_add tmw_sum_linear tmw_sum_pos           tmw_sum_le           base_loss           tmw_dist_log_inv_one_inv tmw_dist_log_exp_neg           tmw_dist_log_le_linear           Z_temp tmw_Z_temp_spec t1 t2 Ht1 Ht2 Hlt Hkl           (Hlmn (inv_pos t2 Ht2) (inv_pos t1 Ht1)                 (UpReqTempEntropy.req_inv_pos_lt_contra t1 t2 Ht1 Ht2 Hlt))).
Qed.

(*   req_le_minus_nonneg (fw_et t1)(fw_et t2)(槽W2a 位 ← 全强度桥)。    *)
Theorem tmw_le_minus_nonneg_fw_et :
  (forall a b : R, lt a b -> lt zero (req_minus b a)) ->
  forall (t1 t2 : R) (Ht1 : lt zero t1) (Ht2 : lt zero t2),
  lt t1 t2 ->
  le zero (req_minus (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t2 Ht2)
                     (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos
                                              base_loss Z_temp
                                              tmw_Z_temp_spec t1 Ht1)).
Proof.
  intros Hlmn t1 t2 Ht1 Ht2 Hlt.
  exact (req_le_minus_nonneg           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t1 Ht1)           (@UpFirewallReq.fw_et R RIS S sumf tmw_sum_pos base_loss                                 Z_temp tmw_Z_temp_spec t2 Ht2)           (tmw_req_energy_exp_temp_mono_full Hlmn t1 t2 Ht1 Ht2 Hlt)).
Qed.

End TmwMonoW2.

(* Print Assumptions 假设审计（五件全量）。                             *)
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_le_minus_nonneg_fw_et.

Print Assumptions tmw_le_minus_nonneg_fw_et.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_full.
Print Assumptions tmw_req_energy_exp_temp_mono_full.
Print Assumptions tmw_req_energy_exp_temp_strict_mono_cond.
Print Assumptions tmw_req_energy_exp_temp_mono_cond.
