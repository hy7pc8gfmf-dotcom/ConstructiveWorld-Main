(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_A.v —— 战役 PA6-03 甲腿（T213）           *)
(*   EntropyMonoSplitInst 前三枚证明件逐枚消融（按依赖序 #4/#5/#6）     *)
(*                                                              *)
(* 母本：消融50/EntropyMonoSplitInst.v（论文6:644 引用件；权威消费态   *)
(*   /tmp/czn14_union_full/EntropyMonoSplitInst.vo，出节常量 8 枚）。  *)
(*   11 声明勘表：3 Let（emsi_bt/emsi_bt_pos/emsi_kl，速记无封口）      *)
(*   + 3 Lemma（三桥件）+ 1 Corollary（镜像孪生）+ 4 Theorem（装载）。  *)
(*   本件消融前三枚含 Qed 封口的证明件：                                *)
(*     #4 emsi_energy_pin_self（:97 能量钉自钉小桥）                    *)
(*     #5 emsi_le_diff_ge_zero（:117 差分非负序桥）                     *)
(*     #6 emsi_le_plus_eps（:136 eps 松弛提升桥）                       *)
(*   Let 三枚无独立证明体不设消融（出节内联消失）；#7–#11 留乙腿。      *)
(*                                                              *)
(* 消融纪律（禁转发冒充）：全部五枚定理证项零引用母本件名                 *)
(*   （emsi_* / inst_* 六枚全不出现），逐枚注明消融形态：                *)
(*     消融一（对 #4）上游直击 + 峰温装配对偶：剥母本 emsi_bt 换名层，    *)
(*       直接对上游注册面 UpReqTempDefs.real_boltzmann_dist_temp /       *)
(*       real_energy_exp_temp 定义面 real_eq_refl 重立；腿二给母本       *)
(*       inst_pinned_at_peak 的 sym 对偶新形（母本未证方向）。           *)
(*     消融二（对 #5）独立链：改走 RealSetoid.real_eq_le（eq 升格桥）    *)
(*       造 0 ≤ a+(−a) 再 real_le_trans 复合——与母本「compat 双边       *)
(*       同加 + id_l 换左」结构异链。                                   *)
(*     消融三（对 #6）实例装配：泛形直击重立 + eps:=real_one 具体装配    *)
(*       新形（real_one_pos 供位）+ #5∘#6 组合桥（消费本件消融件，       *)
(*       验证桥链撤母本后仍自洽复合）。                                  *)
(*                                                              *)
(* 纪律：全件真证收口零悬置；raw Real 层零 req2 混引；原树只读；        *)
(*   编译产物只落 /tmp/pa7_work；尾嵌 Print Assumptions 五连自检。       *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.

(* ============================================================ *)
(* 消融一（对母本 #4 emsi_energy_pin_self）——上游直击腿：               *)
(*   母本语句经 emsi_bt 换名包裹；本枚剥掉换名层，对上游注册面             *)
(*   real_boltzmann_dist_temp / real_energy_exp_temp 出节形直击。        *)
(*   证项零母本：左端 lambda 与 real_energy_exp_temp 定义面定义性        *)
(*   合一，real_eq_refl 一发真装（母本同理但本件独立复立）。             *)
(* ============================================================ *)
Theorem uap63_pin_self_updirect :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (energy : S -> Real) (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                (energy s)))
      (real_energy_exp_temp S rsu rsp u Hu energy).
Proof.
  intros S rsu rsp energy u Hu.
  exact (real_eq_refl
           (rsu (fun s : S =>
                   real_mult
                     (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                     (energy s)))).
Qed.

(* ============================================================ *)
(* 消融一腿二（峰温装配对偶）：母本 inst_pinned_at_peak 证               *)
(*   Σ(p_{t*}·e) == E_{t*}；本枚给 sym 对偶新形 E_{t*} == Σ(p_{t*}·e)    *)
(*   （母本全件未证方向），零供位零母本，上游定义面直击。                 *)
(* ============================================================ *)
Theorem uap63_pin_at_peak_sym_assembly :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (energy : S -> Real) (T : Real) (HT : real_lt real_zero T),
    real_eq
      (real_energy_exp_temp S rsu rsp T HT energy)
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp T HT energy s)
                (energy s))).
Proof.
  intros S rsu rsp energy T HT.
  exact (real_eq_refl
           (real_energy_exp_temp S rsu rsp T HT energy)).
Qed.

(* ============================================================ *)
(* 消融二（对母本 #5 emsi_le_diff_ge_zero）——独立链：                   *)
(*   母本链 = real_le_plus_compat 双边同加 −a + id_l 换左端；            *)
(*   本枚异链 = real_eq_le（eq 升格 le 桥）先立 0 ≤ a+(−a)（换向         *)
(*   real_plus_opp），再 real_le_trans 复合 compat 形——链根不同。        *)
(* ============================================================ *)
Theorem uap63_diff_ge_zero_indep :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  apply (real_le_trans real_zero
           (real_plus a (real_opp a))
           (real_plus b (real_opp a))).
  exact (RealSetoid.real_eq_le real_zero
           (real_plus a (real_opp a))
           (real_eq_sym (real_plus a (real_opp a)) real_zero
              (real_plus_opp a))).
  exact (real_le_plus_compat a b (real_opp a) (real_opp a) Hab
           (real_le_refl (real_opp a))).
Qed.

(* ============================================================ *)
(* 消融三（对母本 #6 emsi_le_plus_eps）泛形直击腿：同构重立              *)
(*   （compat + id_l，与母本同构——泛形即母本全部门面，声明为同构复装，    *)
(*   非独立链；独立性与装配性由下两腿补足）。                            *)
(* ============================================================ *)
Theorem uap63_plus_eps_updirect :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus X eps)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero eps HX
           (real_le_from_lt_aux real_zero eps Heps)).
Qed.

(* ============================================================ *)
(* 消融三腿二（实例装配）：eps := real_one 具体装配新形                  *)
(*   （母本全件无 any 具体eps 装配实例；real_one_pos 供位真装）。         *)
(* ============================================================ *)
Theorem uap63_eps_one_assembly :
  forall X : Real,
    real_le real_zero X -> real_le real_zero (real_plus X real_one).
Proof.
  intros X HX.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus X real_one)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero real_one HX
           (real_le_from_lt_aux real_zero real_one real_lt_zero_one)).
Qed.

(* ============================================================ *)
(* 消融三腿三（#5∘#6 组合桥独立链）：撤母本两桥后链仍自洽复合——          *)
(*   消费本件消融二/消融三泛形两枚，real_le_trans 一跳复合，              *)
(*   证项零母本件名。                                                   *)
(* ============================================================ *)
Theorem uap63_diff_eps_combo_indep :
  forall a b eps : Real,
    real_le a b -> real_lt real_zero eps ->
    real_le real_zero
      (real_plus (real_plus b (real_opp a)) eps).
Proof.
  intros a b eps Hab Heps.
  exact (real_le_trans real_zero
           (real_plus real_zero eps)
           (real_plus (real_plus b (real_opp a)) eps)
           (uap63_plus_eps_updirect real_zero eps
              (real_le_refl real_zero) Heps)
           (real_le_plus_compat real_zero
              (real_plus b (real_opp a)) eps eps
              (uap63_diff_ge_zero_indep a b Hab)
              (real_le_refl eps))).
Qed.

(* ---- G1 内嵌自检段（五枚闭合判词） ---- *)
Print Assumptions uap63_pin_self_updirect.
Print Assumptions uap63_pin_at_peak_sym_assembly.
Print Assumptions uap63_diff_ge_zero_indep.
Print Assumptions uap63_plus_eps_updirect.
Print Assumptions uap63_eps_one_assembly.
Print Assumptions uap63_diff_eps_combo_indep.
