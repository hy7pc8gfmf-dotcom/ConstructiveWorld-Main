(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpAblD1S5_UpReqEntropyMonoSplit.v —— FA-D1S5 数据供给大封装第二梯 件②           *)
(*                                                              *)
(* 辖区：UpReqEntropyMonoSplit.v Section EmsEntropyMonoSplit 净新 12 槽             *)
(*   （Live_X 副本与 ConstructiveWorld_vo 正册 md5 同代                            *)
(*    911646f880b85cf77cc890c3c7563e8c，零代际漂移）                              *)
(*   槽行号锚（源版本实测）：S:90｜real_sum_over_S:91｜ext:95｜le:97｜              *)
(*     linear:99｜add:102｜T_star:105｜T_star_pos:106｜energy:107｜                *)
(*     Hpinned:137-140｜Hkl_right:146-152｜Hkl_left:153-159                       *)
(*     UpAblD1S3_sum_pos_UpReqEntropyMonoSplit.v，fa57_sum_carrier_realizes        *)
(*     源版本速记件（bt/et/kl）传递引用该槽，包按载体完备性携带之（不另立              *)
(*     实例化消解定理、不计位），供给腿＝单点实例 Hf tt。                                 *)
(*                                                              *)
(* 形态：D1S4 封装记录型先例照抄；含 forall S : Type 字段——按 D1S4 偏差2/           *)
(*   坑卡① 提升为 Type 排序（Set 排序实测编译拒绝先例），G3 提取在 S 应用位          *)
(*   预期出现 Obj.magic 擦除族，按 AA3/E888 口径登记。                            *)
(* 源版本速记件 ems_bt/ems_bt_pos/ems_et/ems_kl_peak（源版本 L112-131 Section          *)
(*   Let，源版本自述 discharge 时内联）以显式参形实名同构（δ 展开同体，件头登记）。      *)
(*                                                              *)
(* 实例供给：S:=unit（单点态空间）｜求和载体:=fun f => f tt｜sumpos:=Hf tt｜         *)
(*   T_star:=real_one｜energy:=零函数。                                            *)
(*   单点载体下：ext/le 供给腿＝使用位直取（H tt）；linear/add＝两侧归一逐项         *)
(*   重合（real_eq_refl 一行）；Hpinned＝两侧各自 mult_zero 一步归零；              *)
(*   Hkl_right/Hkl_left＝kl 单点归零链（bt 归一 inv_pos_correct→log_one→           *)
(*   plus/opp 群律）＋real_lt_compat 序迁移——机械供给级。                           *)
(*                                                              *)
(* 分级（禁注水如实申报）：12 净新槽全部 T·接口/数据/证书供给级合并申报。             *)
(*                                                              *)
(* 依赖：CW_ConstructiveWorld_219（S02 环律/S03 逆元器/S07 Setoid 桥/S08 log 器）     *)
(*   ＋UpReqTempDefs＋UpReqEntropyDeficitTemp（温度族/KL 定义件——源版本自身依赖面，     *)
(*   只读使用，非槽源版本）；零 Require 槽源版本（防 P3S1 坑1 混代际）。              *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblD1S5_*.{log,exit}                      *)
(* ============================================================ *)

From Stdlib Require Import List.
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
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.

(* ============ 供给常量（单点实例） ============ *)

Definition uabd1s5_ems_sum : (unit -> Real) -> Real :=
  fun f : unit -> Real => f tt.

Definition uabd1s5_ems_sumpos
  : forall f : unit -> Real,
      (forall s : unit, real_lt real_zero (f s)) ->
      real_lt real_zero (uabd1s5_ems_sum f) :=
  fun (f : unit -> Real)
      (Hf : forall s : unit, real_lt real_zero (f s)) => Hf tt.

Definition uabd1s5_ems_energy : unit -> Real := fun _ : unit => real_zero.

(* ============ 源版本速记件显式参形同构（δ 展开同体；对照源版本 L112-131） ============ *)

Definition uabd1s5_ems_bt (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t) (s : S) : Real :=
  real_boltzmann_dist_temp S sumf SUP t Ht energy s.

Definition uabd1s5_ems_btpos (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t)
  : forall s : S, real_lt real_zero (uabd1s5_ems_bt S sumf SUP energy t Ht s) :=
  real_boltzmann_dist_temp_pos S sumf SUP t Ht energy.

Definition uabd1s5_ems_et (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_energy_exp_temp S sumf SUP t Ht energy.

Definition uabd1s5_ems_kl (S : Type)
  (sumf : (S -> Real) -> Real)
  (SUP : forall f : S -> Real,
           (forall s : S, real_lt real_zero (f s)) ->
           real_lt real_zero (sumf f))
  (energy : S -> Real) (t : Real) (Ht : real_lt real_zero t)
  (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S sumf SUP t Ht energy
    (uabd1s5_ems_bt S sumf SUP energy u Hu)
    (uabd1s5_ems_btpos S sumf SUP energy u Hu).

(* ============ 机械供给腿（一步直接给出/短 trans 链） ============ *)

Lemma uabd1s5_ems_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Qed.

Lemma uabd1s5_ems_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_plus_comm real_zero x) (real_plus_zero x)).
Qed.

(* 单点载体下 Boltzmann 分布逐点归一：p_t(tt) == 1
   （Z δ/ι 收敛到因子自身，comm 后 inv_pos_correct 一步） *)
Lemma uabd1s5_ems_bt_one : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq
    (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos uabd1s5_ems_energy
       t Ht tt)
    real_one.
Proof.
  intros t Ht.
  exact (real_eq_trans
           (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy t Ht tt)
           (real_mult
              (real_boltzmann_factor_temp unit t Ht uabd1s5_ems_energy tt)
              (real_inv_pos
                 (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
                 (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    t Ht uabd1s5_ems_energy)))
           real_one
           (real_mult_comm
              (real_inv_pos
                 (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
                 (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    t Ht uabd1s5_ems_energy))
              (real_boltzmann_factor_temp unit t Ht uabd1s5_ems_energy tt))
           (real_inv_pos_correct
              (real_Z_temp unit uabd1s5_ems_sum t Ht uabd1s5_ems_energy)
              (real_Z_temp_pos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 t Ht uabd1s5_ems_energy))).
Qed.

(* 单点载体下峰温 KL 逐点归零：kl(t,u) == 0
   （bt_one → log_wd/log_one 双腿 → plus/opp 群律 → mult_one） *)
Lemma uabd1s5_ems_kl_zero :
  forall (t u : Real) (Ht : real_lt real_zero t) (Hu : real_lt real_zero u),
    real_eq
      (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos uabd1s5_ems_energy
         t Ht u Hu)
      real_zero.
Proof.
  intros t u Ht Hu.
  assert (Hlu : real_eq
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt))
             real_zero).
  { exact (real_eq_trans
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_one
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_lt_zero_one
                (uabd1s5_ems_bt_one u Hu))
             (real_log_one real_lt_zero_one)). }
  assert (Hlt2 : real_eq
              (real_log
                 (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy t Ht tt)
                 (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy t Ht tt))
              real_zero).
  { exact (real_eq_trans
             (real_log
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt))
             (real_log real_one real_lt_zero_one)
             real_zero
             (real_log_wd
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                real_one
                (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy t Ht tt)
                real_lt_zero_one
                (uabd1s5_ems_bt_one t Ht))
             (real_log_one real_lt_zero_one)). }
  apply (real_eq_trans
           (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy t Ht u Hu)
           (real_mult
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu tt)
              (real_plus
                 (real_log
                    (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy u Hu tt)
                    (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy u Hu tt))
                 (real_opp
                    (real_log
                       (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy t Ht tt)
                       (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy t Ht tt)))))
           real_zero).
  - exact (real_eq_refl
             (real_mult
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))))).
  - exact (real_eq_trans
             (real_mult
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))))
             (real_mult real_one
                (real_plus real_zero (real_opp real_zero)))
             real_zero
             (RealSetoid.real_eq_mult_compat_adapt
                (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                   uabd1s5_ems_energy u Hu tt)
                real_one
                (real_plus
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt))))
                (real_plus real_zero (real_opp real_zero))
                (uabd1s5_ems_bt_one u Hu)
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_log
                      (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt)
                      (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                         uabd1s5_ems_energy u Hu tt))
                   real_zero
                   (real_opp
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)))
                   (real_opp real_zero)
                   Hlu
                   (RealSetoid.real_eq_opp_compat
                      (real_log
                         (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt)
                         (uabd1s5_ems_btpos unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                            uabd1s5_ems_energy t Ht tt))
                      real_zero
                      Hlt2)))
             (real_eq_trans
                (real_mult real_one (real_plus real_zero (real_opp real_zero)))
                (real_mult real_one real_zero)
                real_zero
                (RealSetoid.real_eq_mult_compat_adapt
                   real_one real_one
                   (real_plus real_zero (real_opp real_zero))
                   real_zero
                   (real_eq_refl real_one)
                   (real_plus_opp real_zero))
                (uabd1s5_ems_mult_one_l real_zero))).
Qed.

(* Hpinned 供给腿：单点载体下两侧各自 mult_zero 一步归零 *)
Lemma uabd1s5_ems_Hpinned_leg :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (uabd1s5_ems_sum
         (fun s : unit =>
            real_mult
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu s)
              (uabd1s5_ems_energy s)))
      (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
         uabd1s5_ems_energy real_one real_lt_zero_one).
Proof.
  intros u Hu.
  exact (real_eq_trans
           (uabd1s5_ems_sum
              (fun s : unit =>
                 real_mult
                   (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                      uabd1s5_ems_energy u Hu s)
                   (uabd1s5_ems_energy s)))
           real_zero
           (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
              uabd1s5_ems_energy real_one real_lt_zero_one)
           (real_mult_zero
              (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy u Hu tt))
           (real_eq_sym
              (uabd1s5_ems_et unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one)
              real_zero
              (real_mult_zero
                 (uabd1s5_ems_bt unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one tt)))).
Qed.

(* Hkl_right/Hkl_left 供给腿：kl 归零 → 表达式归一为 eps → real_lt_compat 序迁移 *)
Lemma uabd1s5_ems_Hkl_right_leg :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le real_one u ->
    real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus
              (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
              (real_opp
                 (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus
                    (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                    (real_opp
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                       (real_opp
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                          real_zero
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu))
                          (real_opp real_zero)
                          (uabd1s5_ems_kl_zero real_one v real_lt_zero_one Hv)
                          (RealSetoid.real_eq_opp_compat
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                             real_zero
                             (uabd1s5_ems_kl_zero real_one u real_lt_zero_one Hu)))
                       (real_eq_refl eps))
                    (uabd1s5_ems_plus_zero_l eps)))
              Heps)).
Qed.

Lemma uabd1s5_ems_Hkl_left_leg :
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v ->
    real_le v real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_plus
              (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                 uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
              (real_opp
                 (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                    uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
           eps).
Proof.
  intros u v Hu Hv _ _ eps Heps.
  exact (inl
           (RealSetoid.real_lt_compat
              real_zero real_zero
              eps
              (real_plus
                 (real_plus
                    (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                       uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                    (real_opp
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                 eps)
              (real_eq_refl real_zero)
              (real_eq_sym
                 (real_plus
                    (real_plus
                       (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                          uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                       (real_opp
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                    eps)
                 eps
                 (real_eq_trans
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                       eps)
                    (real_plus real_zero eps)
                    eps
                    (RealSetoid.real_eq_plus_compat_adapt
                       (real_plus
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)))
                       real_zero
                       eps eps
                       (RealSetoid.real_eq_plus_compat_adapt
                          (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                             uabd1s5_ems_energy real_one real_lt_zero_one u Hu)
                          real_zero
                          (real_opp
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv))
                          (real_opp real_zero)
                          (uabd1s5_ems_kl_zero real_one u real_lt_zero_one Hu)
                          (RealSetoid.real_eq_opp_compat
                             (uabd1s5_ems_kl unit uabd1s5_ems_sum uabd1s5_ems_sumpos
                                uabd1s5_ems_energy real_one real_lt_zero_one v Hv)
                             real_zero
                             (uabd1s5_ems_kl_zero real_one v real_lt_zero_one Hv)))
                       (real_eq_refl eps))
                    (uabd1s5_ems_plus_zero_l eps)))
              Heps)).
Qed.

(* ============ 封装记录型：12 净新槽＋1 载体完备位逐字入包（对照源版本 L90-159） ============ *)

Inductive uabd1s5_ems_pack13 : Type :=
| uabd1s5_ems_pack13_intro :
    forall S : Type,
      forall real_sum_over_S : (S -> Real) -> Real,
        forall real_sum_pos_preserved :
          forall f : S -> Real,
            (forall s : S, real_lt real_zero (f s)) ->
            real_lt real_zero (real_sum_over_S f),
        (forall f g : S -> Real,
            (forall s : S, real_eq (f s) (g s)) ->
            real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall f g : S -> Real,
            (forall s : S, real_le (f s) (g s)) ->
            real_le (real_sum_over_S f) (real_sum_over_S g)) ->
        (forall (a : Real) (f : S -> Real),
            real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
                    (real_mult a (real_sum_over_S f))) ->
        (forall f g : S -> Real,
            real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
                    (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
        forall T_star : Real,
          forall T_star_pos : real_lt real_zero T_star,
          forall energy : S -> Real,
            (forall (u : Real) (Hu : real_lt real_zero u),
                real_eq
                  (real_sum_over_S
                     (fun s : S =>
                        real_mult
                          (uabd1s5_ems_bt S real_sum_over_S
                             real_sum_pos_preserved energy u Hu s)
                          (energy s)))
                  (uabd1s5_ems_et S real_sum_over_S
                     real_sum_pos_preserved energy T_star T_star_pos)) ->
            (forall (u v : Real) (Hu : real_lt real_zero u)
                    (Hv : real_lt real_zero v),
                real_le T_star u ->
                real_le u v ->
                forall eps : Real,
                  real_lt real_zero eps ->
                  real_le real_zero
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl S real_sum_over_S
                             real_sum_pos_preserved energy T_star T_star_pos v Hv)
                          (real_opp
                             (uabd1s5_ems_kl S real_sum_over_S
                                real_sum_pos_preserved energy T_star T_star_pos
                                u Hu)))
                       eps)) ->
            (forall (u v : Real) (Hu : real_lt real_zero u)
                    (Hv : real_lt real_zero v),
                real_le u v ->
                real_le v T_star ->
                forall eps : Real,
                  real_lt real_zero eps ->
                  real_le real_zero
                    (real_plus
                       (real_plus
                          (uabd1s5_ems_kl S real_sum_over_S
                             real_sum_pos_preserved energy T_star T_star_pos u Hu)
                          (real_opp
                             (uabd1s5_ems_kl S real_sum_over_S
                                real_sum_pos_preserved energy T_star T_star_pos
                                v Hv)))
                       eps)) ->
            uabd1s5_ems_pack13.

(* ============ 前置引理：单点实例一次喂定 13 位（12 净新＋1 载体完备） ============ *)

Theorem uabd1s5_ems_pack13_supplied : uabd1s5_ems_pack13.
Proof.
  exact (uabd1s5_ems_pack13_intro
           unit
           uabd1s5_ems_sum
           uabd1s5_ems_sumpos
           (fun (f g : unit -> Real)
                (H : forall s : unit, real_eq (f s) (g s)) => H tt)
           (fun (f g : unit -> Real)
                (H : forall s : unit, real_le (f s) (g s)) => H tt)
           (fun (a : Real) (f : unit -> Real) =>
              real_eq_refl (real_mult a (f tt)))
           (fun (f g : unit -> Real) =>
              real_eq_refl (real_plus (f tt) (g tt)))
           real_one
           real_lt_zero_one
           uabd1s5_ems_energy
           uabd1s5_ems_Hpinned_leg
           uabd1s5_ems_Hkl_right_leg
           uabd1s5_ems_Hkl_left_leg).
Qed.

(* ============ 假设面闭合申报 ============ *)

Print Assumptions uabd1s5_ems_pack13_supplied.
