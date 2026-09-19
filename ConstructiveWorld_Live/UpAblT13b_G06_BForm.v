(* ============================================================ *)
(* UpAblT13b_G06_BForm.v —— 假设消融战役 T13b 承接席（批10 实和与残差权七位）   *)
(* 辖区：G06_BForm.v 七位（T13a 移交单 §6 批10 行点名，总账 §2.2 批⑩ 余量）：    *)
(*   位1 :32  real_sum_over_S_ext（RealPPOLeBFull 求和外延槽）                   *)
(*   位2 :34  real_sum_over_S_le（求和单调槽）                                   *)
(*   位3 :36  real_sum_over_S_add（求和可加槽）                                  *)
(*   位4 :40  real_sum_over_S_linear（求和线性槽）                               *)
(*   位5 :59  lebR_res_weight_pos（残差权聚合正位）                              *)
(*   位6 :464 uab_temp_sum_pos（UpReqMinPProjB 截断质量正位）                     *)
(*   位7 :470 uab_Z_full_pos（完整配分正位）                                     *)
(* 放电母本：位1-4 ←real_list_sum_ext/le/add/linear/pos@S08_RealMainlineDPO       *)
(*   （:295/:432/:340/:362；求和槽实和实例 real_list_sum 材料化放电）；           *)
(*   位5 ←rplb_res_weight_pos_uncond@G06_BForm:155（无条件放电件直喂）；          *)
(*   位6/7 ←real_list_sum_pos@S08:463 正和族（词表非空+逐项正前提显式参；         *)
(*   位6 另带保留判定全保留实例供形，分支归约后与位7 同链）。                     *)
(* 消融形（诚实登记）：实载体语句面自足（Real 层，零装配桥）；位6 具体实例        *)
(*   供形（保留判定全保留）加逐项正/非空前提显式参。                              *)
(* 分级：位1-5/位7 N1（库内放电件直喂）；位6 N3（实例供给+正和族直喂）。          *)
(* 依赖（只读消费，原树零改）：CW_ConstructiveWorld_219、S08_RealMainlineDPO、    *)
(*   UpAuditBridge、G06_BForm。                                                  *)
(* 四关留痕：Live_X/attn/logs/g{1..4}-UpAblT13b_*.log                           *)
(* ============================================================ *)
From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import S08_RealMainlineDPO.
Require Import UpAuditBridge.
Require Import G06_BForm.
From Stdlib Require Import List.

(* 位1 ←:32（求和外延槽：实和实例材料化） *)
Theorem uabT13b_g06_ros_ext :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (@real_list_sum_ext S f g l H).
Qed.

(* 位2 ←:34（求和单调槽） *)
Theorem uabT13b_g06_ros_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  exact (@real_list_sum_le S f g l H).
Qed.

(* 位3 ←:36（求和可加槽） *)
Theorem uabT13b_g06_ros_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  exact (@real_list_sum_add S f g l).
Qed.

(* 位4 ←:40（求和线性槽） *)
Theorem uabT13b_g06_ros_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  exact (@real_list_sum_linear S a f l).
Qed.

(* 位5 ←:59（残差权聚合正；词表非空前提显式参） *)
Theorem uabT13b_g06_lebR_weight_pos :
  forall (X : Set) (vocab : list X), Not (Id vocab nil) ->
    real_lt real_zero
      (lebR_res_weight X (fun f : X -> Real => real_list_sum X f vocab)
                        (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  intros X vocab Hne.
  exact (rplb_res_weight_pos_uncond X vocab Hne).
Qed.

(* 位6 ←:464（截断质量正；保留判定全保留实例供入+逐项正/非空前提显式参） *)
Theorem uabT13b_g06_uabtemp_sum_pos :
  forall (Token : Type) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> vocab <> nil ->
    forall prefix : list Token,
      real_lt real_zero
        (@uab_temp_sum Token vocab rtf
             (fun (_ : list Token) (_ : Token) => unit)
             (fun (_ : list Token) (_ : Token) => inl tt : Or unit (Not unit))
             prefix).
Proof.
  intros Token vocab rtf Hf Hne prefix.
  exact (real_list_sum_pos Token rtf vocab Hf Hne).
Qed.

(* 位7 ←:470（完整配分正；逐项正/非空前提显式参） *)
Theorem uabT13b_g06_Zfull_pos :
  forall (Token : Type) (vocab : list Token) (rtf : Token -> Real),
    (forall w : Token, real_lt real_zero (rtf w)) -> vocab <> nil ->
    real_lt real_zero (Z_full Token vocab rtf).
Proof.
  intros Token vocab rtf Hf Hne.
  exact (real_list_sum_pos Token rtf vocab Hf Hne).
Qed.

(* ---- 收尾段（逐件假设面打印） ---- *)
Print Assumptions uabT13b_g06_ros_ext.
Print Assumptions uabT13b_g06_ros_le.
Print Assumptions uabT13b_g06_ros_add.
Print Assumptions uabT13b_g06_ros_linear.
Print Assumptions uabT13b_g06_lebR_weight_pos.
Print Assumptions uabT13b_g06_uabtemp_sum_pos.
Print Assumptions uabT13b_g06_Zfull_pos.
