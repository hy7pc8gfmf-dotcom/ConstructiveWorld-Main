(* ============================================================ *)
(* UpAblD1S5_UpReqDoeblinEntropy.v —— FA-D1S5 数据供给大打包第二梯 件①            *)
(* 席位：FA-D1S5（普查批 D1-⑦ 第二梯 ≤40 位·按模块聚合）｜独立伴生件·原树零改        *)
(*                                                              *)
(* 辖区：UpReqDoeblinEntropy.v Section DoeblinEntropyList 全 18 个 N 位             *)
(*   （Live_X 副本与 ConstructiveWorld_vo 正册 md5 同代                            *)
(*    873fa3238ca63a5fcce0bbec3260aa20，零代际漂移）                              *)
(*   槽位行号锚（母本实测）：states:827｜Hnil:828｜T:829｜Ht:830｜energy:831｜      *)
(*     om:834｜Hom:835｜Hom1:836｜w:837｜Hwp:838｜Hwn:839｜Hew:840-848｜           *)
(*     epss0:909｜p:929｜Hpp:930｜Heb:935-937｜r2:938｜Hsq:940-943                *)
(*   另 4 个 T·零消费位（Hepss:910/Hpn:931/Hep:932/Hr2:939）按普查 §④ 剪除申报，    *)
(*     零施工、不入包、不计位。                                                    *)
(* 主锚注记：本模块数据位为 Doeblin 一步核 δ 参数化节参（普查 D1-⑦ 批注记），         *)
(*   主锚 real_step_kl_eta_bound_eps@UpStepKL.v:682 属首梯辖区，本批零触碰。        *)
(*                                                              *)
(* 形态：D1S4 打包记录型先例照抄（UpAblD1S4_UpReqStepKLEtaInst 同款，               *)
(*   Inductive 单构造子逐槽语句入包）。本模块无 Type 字段，包落 Set 排序             *)
(*   （G3 提取 magic=0 干净，D1S4 偏差2 对照）。                                   *)
(* 母本节内定义件 doe_sumf/doe_sumpos/doe_pb/doe_Hpb/doe_omd/doe_K/doe_h            *)
(*   （母本 L851-884）以显式参形实名镜像（参形=槽位显式参形，δ 展开同体，            *)
(*   P1S1 sfc_two δ 展开同款），件头登记。                                         *)
(*                                                              *)
(* 实例供给：states:=单点 [nil]（cons nil nil）｜T:=real_one｜energy:=零函数｜       *)
(*   om:=real_one｜w:=壹函数｜p:=壹函数｜epss0:=real_one｜r2:=real_zero。           *)
(*   单点载体下全部求和按 cons 折叠 δ/ι 展开：Σ_g ≡ g(nil)+0。                      *)
(*   供给腿全部为一步直配/两步 trans 链（mult_one/mult_zero/plus_zero/plus_opp      *)
(*   族），机械位平凡性实测兑现。                                                  *)
(*                                                              *)
(* 分级（禁注水如实申报）：18 槽全部 T·数据供给级合并申报（Hsq 供给腿为              *)
(*   四步 trans 链 h==0 → 平方和归零 → le-inr 直配，如实登记仍属机械供给）。          *)
(*                                                              *)
(* 依赖：CW_ConstructiveWorld_219（S02 序与环律/S03 逆元器/S07 Setoid 桥/            *)
(*   S08 列表和与 log 器）＋UpReqTempDefs（温度族定义件——母本自身依赖面，只读        *)
(*   消费，非槽位母本）；零 Require 槽位母本（防 P3S1 坑1 混代际）。                 *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblD1S5_*.{log,exit}                      *)
(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.

(* ============ 供给常量（单点实例） ============ *)

Definition uabd1s5_doe_states : list (list Real) := cons nil nil.

Definition uabd1s5_doe_Hnil : uabd1s5_doe_states <> nil.
Proof.
  intro Hc. discriminate Hc.
Qed.

Definition uabd1s5_doe_T : Real := real_one.

Definition uabd1s5_doe_Ht : real_lt real_zero uabd1s5_doe_T := real_lt_zero_one.

Definition uabd1s5_doe_energy : list Real -> Real := fun _ : list Real => real_zero.

Definition uabd1s5_doe_om : Real := real_one.

Definition uabd1s5_doe_w : list Real -> Real := fun _ : list Real => real_one.

Definition uabd1s5_doe_epss0 : Real := real_one.

Definition uabd1s5_doe_p : list Real -> Real := fun _ : list Real => real_one.

Definition uabd1s5_doe_r2 : Real := real_zero.

(* ============ 母本节内定义件显式参形镜像（δ 展开同体） ============ *)
(* doe_sumf (母本 L851-852)：sumf g := real_list_sum (list Real) g states          *)

Definition uabd1s5_doe_sumf (states : list (list Real))
  : (list Real -> Real) -> Real :=
  fun g : list Real -> Real => real_list_sum (list Real) g states.

(* doe_sumpos (母本 L853-859) *)

Definition uabd1s5_doe_sumpos (states : list (list Real)) (Hnil : states <> nil)
  : forall f : list Real -> Real,
      (forall s : list Real, real_lt real_zero (f s)) ->
      real_lt real_zero (uabd1s5_doe_sumf states f) :=
  fun (f : list Real -> Real)
      (Hf : forall s : list Real, real_lt real_zero (f s)) =>
    real_list_sum_pos (list Real) f states Hf Hnil.

(* doe_pb (母本 L875-876)：real_boltzmann_dist_temp 载体化 *)

Definition uabd1s5_doe_pb (states : list (list Real)) (Hnil : states <> nil)
  (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
  (s : list Real) : Real :=
  real_boltzmann_dist_temp (list Real)
    (uabd1s5_doe_sumf states) (uabd1s5_doe_sumpos states Hnil) T Ht energy s.

(* doe_Hpb (母本 L877-878) *)

Definition uabd1s5_doe_Hpb (states : list (list Real)) (Hnil : states <> nil)
  (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
  : forall s : list Real, real_lt real_zero (uabd1s5_doe_pb states Hnil T Ht energy s) :=
  real_boltzmann_dist_temp_pos (list Real)
    (uabd1s5_doe_sumf states) (uabd1s5_doe_sumpos states Hnil) T Ht energy.

(* doe_omd (母本 L879)：omd := 1 − om *)

Definition uabd1s5_doe_omd (om : Real) : Real := real_minus_r real_one om.

(* doe_K (母本 L880-882)：K s := om·pb s + omd·w s *)

Definition uabd1s5_doe_K (states : list (list Real)) (Hnil : states <> nil)
  (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
  (om : Real) (w : list Real -> Real) (s : list Real) : Real :=
  real_plus (real_mult om (uabd1s5_doe_pb states Hnil T Ht energy s))
            (real_mult (uabd1s5_doe_omd om) (w s)).

(* doe_h (母本 L883-884)：h s := K s − pb s *)

Definition uabd1s5_doe_h (states : list (list Real)) (Hnil : states <> nil)
  (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
  (om : Real) (w : list Real -> Real) (s : list Real) : Real :=
  real_minus_r (uabd1s5_doe_K states Hnil T Ht energy om w s)
               (uabd1s5_doe_pb states Hnil T Ht energy s).

(* ============ 机械供给腿（一步直配/短 trans 链） ============ *)

Lemma uabd1s5_doe_mult_one_l : forall x : Real,
  real_eq (real_mult real_one x) x.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_one x) (real_mult_one x)).
Qed.

Lemma uabd1s5_doe_mult_zero_l : forall x : Real,
  real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x. exact (real_eq_trans _ _ _ (real_mult_comm real_zero x) (real_mult_zero x)).
Qed.

Lemma uabd1s5_doe_omd_one_zero : real_eq (uabd1s5_doe_omd real_one) real_zero.
Proof.
  exact (real_plus_opp real_one).
Qed.

Lemma uabd1s5_doe_omd_mult_zero : forall x : Real,
  real_eq (real_mult (uabd1s5_doe_omd real_one) x) real_zero.
Proof.
  intro x.
  exact (real_eq_trans
           (real_mult (uabd1s5_doe_omd real_one) x)
           (real_mult real_zero x)
           real_zero
           (RealSetoid.real_eq_mult_compat_adapt
              (uabd1s5_doe_omd real_one) real_zero x x
              uabd1s5_doe_omd_one_zero (real_eq_refl x))
           (uabd1s5_doe_mult_zero_l x)).
Qed.

Lemma uabd1s5_doe_K_eq_pb :
  forall (states : list (list Real)) (Hnil : states <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
         (w : list Real -> Real) (s : list Real),
    real_eq (uabd1s5_doe_K states Hnil T Ht energy real_one w s)
            (uabd1s5_doe_pb states Hnil T Ht energy s).
Proof.
  intros states Hnil T Ht energy w s.
  apply (real_eq_trans
           (real_plus
              (real_mult real_one (uabd1s5_doe_pb states Hnil T Ht energy s))
              (real_mult (uabd1s5_doe_omd real_one) (w s)))
           (real_plus (uabd1s5_doe_pb states Hnil T Ht energy s) real_zero)
           (uabd1s5_doe_pb states Hnil T Ht energy s)).
  - exact (RealSetoid.real_eq_plus_compat_adapt
             (real_mult real_one (uabd1s5_doe_pb states Hnil T Ht energy s))
             (uabd1s5_doe_pb states Hnil T Ht energy s)
             (real_mult (uabd1s5_doe_omd real_one) (w s))
             real_zero
             (uabd1s5_doe_mult_one_l (uabd1s5_doe_pb states Hnil T Ht energy s))
             (uabd1s5_doe_omd_mult_zero (w s))).
  - exact (real_plus_zero (uabd1s5_doe_pb states Hnil T Ht energy s)).
Qed.

Lemma uabd1s5_doe_h_zero :
  forall (states : list (list Real)) (Hnil : states <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : list Real -> Real)
         (w : list Real -> Real) (s : list Real),
    real_eq (uabd1s5_doe_h states Hnil T Ht energy real_one w s) real_zero.
Proof.
  intros states Hnil T Ht energy w s.
  apply (real_eq_trans
           (uabd1s5_doe_h states Hnil T Ht energy real_one w s)
           (real_plus
              (uabd1s5_doe_pb states Hnil T Ht energy s)
              (real_opp (uabd1s5_doe_pb states Hnil T Ht energy s)))
           real_zero).
  - exact (RealSetoid.real_eq_plus_compat_adapt
             (uabd1s5_doe_K states Hnil T Ht energy real_one w s)
             (uabd1s5_doe_pb states Hnil T Ht energy s)
             (real_opp (uabd1s5_doe_pb states Hnil T Ht energy s))
             (real_opp (uabd1s5_doe_pb states Hnil T Ht energy s))
             (uabd1s5_doe_K_eq_pb states Hnil T Ht energy w s)
             (real_eq_refl (real_opp (uabd1s5_doe_pb states Hnil T Ht energy s)))).
  - exact (real_plus_opp (uabd1s5_doe_pb states Hnil T Ht energy s)).
Qed.

(* Hsq 供给腿：平方和归零（h==0 逐点 → 平方归零 → 乘积归零 → 单点和归零）
   实例供给级陈述（states 钉单点常量——real_list_sum 折叠需构造元收敛） *)
Lemma uabd1s5_doe_sumsq_zero :
  real_eq
    (uabd1s5_doe_sumf uabd1s5_doe_states
       (fun s : list Real =>
          real_mult
            (real_mult
               (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                  uabd1s5_doe_om uabd1s5_doe_w s)
               (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                  uabd1s5_doe_om uabd1s5_doe_w s))
            (real_inv_pos
               (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s)
               (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s))))
    real_zero.
Proof.
  apply (real_eq_trans
           (uabd1s5_doe_sumf uabd1s5_doe_states
              (fun s : list Real =>
                 real_mult
                   (real_mult
                      (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                         uabd1s5_doe_om uabd1s5_doe_w s)
                      (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                         uabd1s5_doe_om uabd1s5_doe_w s))
                   (real_inv_pos
                      (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s)
                      (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s))))
           (real_mult
              (real_mult
                 (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                    uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                    uabd1s5_doe_om uabd1s5_doe_w nil)
                 (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                    uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                    uabd1s5_doe_om uabd1s5_doe_w nil))
              (real_inv_pos
                 (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                    uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                 (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                    uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)))
           real_zero).
  - exact (real_plus_zero
             (real_mult
                (real_mult
                   (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                      uabd1s5_doe_om uabd1s5_doe_w nil)
                   (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                      uabd1s5_doe_om uabd1s5_doe_w nil))
                (real_inv_pos
                   (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                   (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)))).
  - apply (real_eq_trans
             (real_mult
                (real_mult
                   (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                      uabd1s5_doe_om uabd1s5_doe_w nil)
                   (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                      uabd1s5_doe_om uabd1s5_doe_w nil))
                (real_inv_pos
                   (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                   (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)))
             (real_mult real_zero
                (real_inv_pos
                   (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                   (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                      uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)))
             real_zero).
    + exact (RealSetoid.real_eq_mult_compat_adapt
               (real_mult
                  (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                     uabd1s5_doe_om uabd1s5_doe_w nil)
                  (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                     uabd1s5_doe_om uabd1s5_doe_w nil))
               real_zero
               (real_inv_pos
                  (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                  (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil))
               (real_inv_pos
                  (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                  (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil))
               (real_eq_trans
                  (real_mult
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil)
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil))
                  (real_mult real_zero
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil))
                  real_zero
                  (RealSetoid.real_eq_mult_compat_adapt
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil)
                     real_zero
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil)
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil)
                     (uabd1s5_doe_h_zero uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_w nil)
                     (real_eq_refl
                        (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                           uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                           uabd1s5_doe_om uabd1s5_doe_w nil)))
                  (uabd1s5_doe_mult_zero_l
                     (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                        uabd1s5_doe_om uabd1s5_doe_w nil)))
               (real_eq_refl
                  (real_inv_pos
                     (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                     (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                        uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)))).
    + exact (uabd1s5_doe_mult_zero_l
               (real_inv_pos
                  (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                  (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                     uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil))).
Qed.

(* Hwn 供给腿：单点和 Σ壹 = 壹（cons 折叠 δ/ι 展开） *)
Lemma uabd1s5_doe_Hwn_leg :
  real_eq (real_list_sum (list Real) uabd1s5_doe_w uabd1s5_doe_states) real_one.
Proof.
  exact (real_eq_trans
           (real_list_sum (list Real) uabd1s5_doe_w uabd1s5_doe_states)
           (uabd1s5_doe_w nil)
           real_one
           (real_plus_zero (uabd1s5_doe_w nil))
           (real_eq_refl real_one)).
Qed.

(* Hew 供给腿：Σ(壹·零) == 能量期望（两侧各自两步归零） *)
Lemma uabd1s5_doe_Hew_leg :
  real_eq
    (real_list_sum (list Real)
       (fun s : list Real => real_mult (uabd1s5_doe_w s) (uabd1s5_doe_energy s))
       uabd1s5_doe_states)
    (real_energy_exp_temp (list Real)
       (uabd1s5_doe_sumf uabd1s5_doe_states)
       (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
       uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy).
Proof.
  apply (real_eq_trans
           (real_list_sum (list Real)
              (fun s : list Real => real_mult (uabd1s5_doe_w s) (uabd1s5_doe_energy s))
              uabd1s5_doe_states)
           real_zero
           (real_energy_exp_temp (list Real)
              (uabd1s5_doe_sumf uabd1s5_doe_states)
              (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
              uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy)).
  - exact (real_eq_trans
             (real_list_sum (list Real)
                (fun s : list Real => real_mult (uabd1s5_doe_w s) (uabd1s5_doe_energy s))
                uabd1s5_doe_states)
             (real_plus real_zero real_zero)
             real_zero
             (RealSetoid.real_eq_plus_compat_adapt
                (real_mult (uabd1s5_doe_w nil) (uabd1s5_doe_energy nil))
                real_zero
                real_zero real_zero
                (real_eq_trans
                   (real_mult (uabd1s5_doe_w nil) (uabd1s5_doe_energy nil))
                   (real_mult (uabd1s5_doe_energy nil) (uabd1s5_doe_w nil))
                   real_zero
                   (real_mult_comm (uabd1s5_doe_w nil) (uabd1s5_doe_energy nil))
                   (real_mult_one (uabd1s5_doe_energy nil)))
                (real_eq_refl real_zero))
             (real_plus_zero real_zero)).
  - exact (real_eq_sym
             (real_energy_exp_temp (list Real)
                (uabd1s5_doe_sumf uabd1s5_doe_states)
                (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
                uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy)
             real_zero
             (real_eq_trans
                (real_energy_exp_temp (list Real)
                   (uabd1s5_doe_sumf uabd1s5_doe_states)
                   (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
                   uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy)
                (real_plus real_zero real_zero)
                real_zero
                (RealSetoid.real_eq_plus_compat_adapt
                   (real_mult
                      (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil)
                      (uabd1s5_doe_energy nil))
                   real_zero
                   real_zero real_zero
                   (real_mult_zero
                      (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                         uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy nil))
                   (real_eq_refl real_zero))
                (real_plus_zero real_zero))).
Qed.

(* Heb 供给腿：两侧 δ/ι 展开逐字同体（同一载体 SC/SP/T/Ht/energy），reflexivity 一行 *)
Lemma uabd1s5_doe_Heb_leg :
  real_eq
    (real_list_sum (list Real)
       (fun s : list Real =>
          real_mult
            (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
               uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s)
            (uabd1s5_doe_energy s))
       uabd1s5_doe_states)
    (real_energy_exp_temp (list Real)
       (uabd1s5_doe_sumf uabd1s5_doe_states)
       (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
       uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy).
Proof.
  exact (real_eq_refl
           (real_energy_exp_temp (list Real)
              (uabd1s5_doe_sumf uabd1s5_doe_states)
              (uabd1s5_doe_sumpos uabd1s5_doe_states uabd1s5_doe_Hnil)
              uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy)).
Qed.

(* Hsq 供给腿：平方和 ≡ 零 ⟹ inr 直配（real_le = Or lt eq 的 eq 支） *)
Lemma uabd1s5_doe_Hsq_leg :
  real_le
    (uabd1s5_doe_sumf uabd1s5_doe_states
       (fun s : list Real =>
          real_mult
            (real_mult
               (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                  uabd1s5_doe_om uabd1s5_doe_w s)
               (uabd1s5_doe_h uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy
                  uabd1s5_doe_om uabd1s5_doe_w s))
            (real_inv_pos
               (uabd1s5_doe_pb uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s)
               (uabd1s5_doe_Hpb uabd1s5_doe_states uabd1s5_doe_Hnil
                  uabd1s5_doe_T uabd1s5_doe_Ht uabd1s5_doe_energy s))))
    uabd1s5_doe_r2.
Proof.
  exact (inr uabd1s5_doe_sumsq_zero).
Qed.

(* ============ 打包记录型：18 槽语句逐字入包（对照母本 L827-943） ============ *)

Inductive uabd1s5_doe_pack18 : Set :=
| uabd1s5_doe_pack18_intro :
    forall states : list (list Real),
      forall Hnil : states <> nil,
        forall T : Real,
          forall Ht : real_lt real_zero T,
            forall energy : list Real -> Real,
              forall om : Real,
                forall Hom : real_lt real_zero om,
                  forall Hom1 : real_le om real_one,
                    forall w : list Real -> Real,
                      forall Hwp : forall s : list Real, real_lt real_zero (w s),
                        forall Hwn : real_eq (real_list_sum (list Real) w states) real_one,
                          forall Hew :
                            real_eq
                              (real_list_sum (list Real)
                                 (fun s : list Real => real_mult (w s) (energy s)) states)
                              (real_energy_exp_temp (list Real)
                                 (fun g : list Real -> Real =>
                                    real_list_sum (list Real) g states)
                                 (fun (f : list Real -> Real)
                                      (Hf : forall s : list Real,
                                              real_lt real_zero (f s)) =>
                                    real_list_sum_pos (list Real) f states Hf Hnil)
                                 T Ht energy),
                          forall epss0 : Real,
                            forall p : list Real -> Real,
                              forall Hpp : forall s : list Real, real_lt real_zero (p s),
                                forall Heb :
                                  real_eq
                                    (real_list_sum (list Real)
                                       (fun s : list Real =>
                                          real_mult
                                            (real_boltzmann_dist_temp (list Real)
                                               (fun g : list Real -> Real =>
                                                  real_list_sum (list Real) g states)
                                               (fun (f : list Real -> Real)
                                                    (Hf : forall s : list Real,
                                                            real_lt real_zero (f s)) =>
                                                 real_list_sum_pos (list Real) f states Hf Hnil)
                                               T Ht energy s)
                                            (energy s))
                                       states)
                                    (real_energy_exp_temp (list Real)
                                       (fun g : list Real -> Real =>
                                          real_list_sum (list Real) g states)
                                       (fun (f : list Real -> Real)
                                            (Hf : forall s : list Real,
                                                    real_lt real_zero (f s)) =>
                                         real_list_sum_pos (list Real) f states Hf Hnil)
                                       T Ht energy),
                                forall r2 : Real,
                                  forall Hsq :
                                    real_le
                                      (real_list_sum (list Real)
                                         (fun s : list Real =>
                                            real_mult
                                              (real_mult
                                                 (real_minus_r
                                                    (real_plus
                                                       (real_mult om
                                                          (real_boltzmann_dist_temp (list Real)
                                                             (fun g : list Real -> Real =>
                                                                real_list_sum (list Real) g states)
                                                             (fun (f : list Real -> Real)
                                                                  (Hf : forall s : list Real,
                                                                          real_lt real_zero (f s)) =>
                                                               real_list_sum_pos (list Real) f states Hf Hnil)
                                                             T Ht energy s))
                                                       (real_mult (real_minus_r real_one om) (w s)))
                                                    (real_boltzmann_dist_temp (list Real)
                                                       (fun g : list Real -> Real =>
                                                          real_list_sum (list Real) g states)
                                                       (fun (f : list Real -> Real)
                                                            (Hf : forall s : list Real,
                                                                    real_lt real_zero (f s)) =>
                                                         real_list_sum_pos (list Real) f states Hf Hnil)
                                                       T Ht energy s))
                                                 (real_minus_r
                                                    (real_plus
                                                       (real_mult om
                                                          (real_boltzmann_dist_temp (list Real)
                                                             (fun g : list Real -> Real =>
                                                                real_list_sum (list Real) g states)
                                                             (fun (f : list Real -> Real)
                                                                  (Hf : forall s : list Real,
                                                                          real_lt real_zero (f s)) =>
                                                               real_list_sum_pos (list Real) f states Hf Hnil)
                                                             T Ht energy s))
                                                       (real_mult (real_minus_r real_one om) (w s)))
                                                    (real_boltzmann_dist_temp (list Real)
                                                       (fun g : list Real -> Real =>
                                                          real_list_sum (list Real) g states)
                                                       (fun (f : list Real -> Real)
                                                            (Hf : forall s : list Real,
                                                                    real_lt real_zero (f s)) =>
                                                         real_list_sum_pos (list Real) f states Hf Hnil)
                                                       T Ht energy s)))
                                              (real_inv_pos
                                                 (real_boltzmann_dist_temp (list Real)
                                                    (fun g : list Real -> Real =>
                                                       real_list_sum (list Real) g states)
                                                    (fun (f : list Real -> Real)
                                                         (Hf : forall s : list Real,
                                                                 real_lt real_zero (f s)) =>
                                                      real_list_sum_pos (list Real) f states Hf Hnil)
                                                    T Ht energy s)
                                                 (real_boltzmann_dist_temp_pos (list Real)
                                                    (fun g : list Real -> Real =>
                                                       real_list_sum (list Real) g states)
                                                    (fun (f : list Real -> Real)
                                                         (Hf : forall s : list Real,
                                                                 real_lt real_zero (f s)) =>
                                                      real_list_sum_pos (list Real) f states Hf Hnil)
                                                    T Ht energy s)))
                                         states)
                                      r2,
                                    uabd1s5_doe_pack18.

(* ============ 供给件：单点实例一次喂定 18 槽 ============ *)

Theorem uabd1s5_doe_pack18_supplied : uabd1s5_doe_pack18.
Proof.
  exact (uabd1s5_doe_pack18_intro
           uabd1s5_doe_states
           uabd1s5_doe_Hnil
           uabd1s5_doe_T
           uabd1s5_doe_Ht
           uabd1s5_doe_energy
           uabd1s5_doe_om
           real_lt_zero_one
           (inr (real_eq_refl real_one))
           uabd1s5_doe_w
           (fun _ : list Real => real_lt_zero_one)
           uabd1s5_doe_Hwn_leg
           uabd1s5_doe_Hew_leg
           uabd1s5_doe_epss0
           uabd1s5_doe_p
           (fun _ : list Real => real_lt_zero_one)
           uabd1s5_doe_Heb_leg
           uabd1s5_doe_r2
           uabd1s5_doe_Hsq_leg).
Qed.

(* ============ 假设面收口申报 ============ *)

Print Assumptions uabd1s5_doe_pack18_supplied.
