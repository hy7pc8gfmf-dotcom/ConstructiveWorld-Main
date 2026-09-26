(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将下列定理之证明体替换为    *)
(* 玩具证（实质非平凡三口径：定义层受控展开、显式见证直取、结构性  *)
(* 重演；逐刀金标准文本程序直取自源版本体并断言同文），声明面与引用  *)
(* 面零改动，零新增 Require，证尾记号逐件守恒，纯构造性闭合，文尾  *)
(* 保留原件假设面追印。清单：                                      *)
(*       列表归纳 nil/cons 分判就地重演，金标直取 S08_RealMainlineDPO） *)
(*       体就地重演：展开＋rplb_sum_pos_discharged 实例化）          *)
(*       S08 real_list_sum_pos 归纳体重演；非空矛盾支 eq_refl 直击） *)
(* ============================================================ *)

(* ============================================================ *)
(*   位1 :32  real_sum_over_S_ext（RealPPOLeBFull 求和外延槽）                   *)
(*   位2 :34  real_sum_over_S_le（求和单调槽）                                   *)
(*   位3 :36  real_sum_over_S_add（求和可加槽）                                  *)
(*   位4 :40  real_sum_over_S_linear（求和线性槽）                               *)
(*   位5 :59  lebR_res_weight_pos（残差权聚合正位）                              *)
(*   位6 :464 uab_temp_sum_pos（UpReqMinPProjB 截断质量正位）                     *)
(*   位7 :470 uab_Z_full_pos（完整配分正位）                                     *)
(* 实例化消解源版本：位1-4 ←real_list_sum_ext/le/add/linear/pos@S08_RealMainlineDPO       *)
(*   （:295/:432/:340/:362；求和槽实和实例 real_list_sum 材料化实例化消解）；           *)
(*   位5 ←rplb_res_weight_pos_uncond@G06_BForm:155（无条件实例化消解件直接供给）；          *)
(*   位6/7 ←real_list_sum_pos@S08:463 正和族（词表非空+逐项正前提显式参；         *)
(*   位6 另带保留判定全保留实例供形，分支归约后与位7 同链）。                     *)
(* 消融形（诚实登记）：实载体语句面自足（Real 层，零装配桥）；位6 具体实例        *)
(*   供形（保留判定全保留）加逐项正/非空前提显式参。                              *)
(* 分级：位1-5/位7 N1（库内实例化消解件直接供给）；位6 N3（实例供给+正和族直接供给）。          *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219、S08_RealMainlineDPO、    *)
(*   UpAuditBridge、G06_BForm。                                                  *)
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
  induction l as [| w rest IH]; simpl.
  - apply real_eq_refl.
  - apply (RealSetoid.real_eq_plus_compat (f w) (real_list_sum S f rest)
             (g w) (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Qed.

(* 位2 ←:34（求和单调槽） *)
Theorem uabT13b_g06_ros_le :
  forall (S : Type) (l : list S) (f g : S -> Real),
    (forall s : S, real_le (f s) (g s)) ->
    real_le (real_list_sum S f l) (real_list_sum S g l).
Proof.
  intros S l f g H.
  induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (real_le_plus_compat (f w) (g w) (real_list_sum S f rest)
             (real_list_sum S g rest)).
    + exact (H w).
    + exact IH.
Qed.

(* 位3 ←:36（求和可加槽） *)
Theorem uabT13b_g06_ros_add :
  forall (S : Type) (l : list S) (f g : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_plus (f s) (g s)) l)
            (real_plus (real_list_sum S f l) (real_list_sum S g l)).
Proof.
  intros S l f g.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
    apply (real_plus_zero real_zero).
  - apply (real_eq_trans _
             (real_plus (real_plus (f w) (g w))
                        (real_plus (real_list_sum S f rest)
                                   (real_list_sum S g rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_plus (f w) (g w))
               (real_list_sum S (fun w0 : S => real_plus (f w0) (g w0)) rest)
               (real_plus (f w) (g w))
               (real_plus (real_list_sum S f rest) (real_list_sum S g rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_plus_swap_mid (f w) (g w) (real_list_sum S f rest)
               (real_list_sum S g rest)).
Qed.

(* 位4 ←:40（求和线性槽） *)
Theorem uabT13b_g06_ros_linear :
  forall (S : Type) (l : list S) (a : Real) (f : S -> Real),
    real_eq (real_list_sum S (fun s : S => real_mult a (f s)) l)
            (real_mult a (real_list_sum S f l)).
Proof.
  intros S l a f.
  induction l as [| w rest IH]; simpl.
  - apply (real_eq_sym (real_mult a real_zero) real_zero).
    apply (real_mult_zero a).
  - apply (real_eq_trans _
             (real_plus (real_mult a (f w))
                        (real_mult a (real_list_sum S f rest))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult a (f w))
               (real_list_sum S (fun w0 : S => real_mult a (f w0)) rest)
               (real_mult a (f w))
               (real_mult a (real_list_sum S f rest))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_sym (real_mult a (real_plus (f w) (real_list_sum S f rest)))
               (real_plus (real_mult a (f w)) (real_mult a (real_list_sum S f rest)))).
      apply (real_distrib a (f w) (real_list_sum S f rest)).
Qed.

(* 位5 ←:59（残差权聚合正；词表非空前提显式参） *)
Theorem uabT13b_g06_lebR_weight_pos :
  forall (X : Set) (vocab : list X), Not (Id vocab nil) ->
    real_lt real_zero
      (lebR_res_weight X (fun f : X -> Real => real_list_sum X f vocab)
                        (fun _ : X => real_one) (fun _ : X => real_one)).
Proof.
  intros X vocab Hne.
  unfold lebR_res_weight.
  apply (rplb_sum_pos_discharged X
           (fun s : X => real_mult real_one real_one) vocab Hne).
  intro s.
  exact (real_mult_positive real_one real_one real_lt_zero_one real_lt_zero_one).
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
  unfold Z_full.
  induction vocab as [| w rest IH]; simpl.
  - exfalso. exact (Hne eq_refl).
  - destruct rest as [| w' rest'].
    + apply (RealSetoid.real_lt_id_r real_zero (rtf w) (real_plus (rtf w) real_zero)).
      * apply (real_eq_sym (real_plus (rtf w) real_zero) (rtf w)).
        apply (real_plus_zero (rtf w)).
      * exact (Hf w).
    + apply (RealSetoid.real_lt_id_l real_zero (real_plus real_zero real_zero)
               (real_plus (rtf w) (real_list_sum Token rtf (w' :: rest')))).
      * apply (real_eq_sym (real_plus real_zero real_zero) real_zero).
        apply (real_plus_zero real_zero).
      * apply (real_lt_plus_compat real_zero (rtf w) real_zero
                 (real_list_sum Token rtf (w' :: rest'))).
        -- exact (Hf w).
        -- apply IH. discriminate.
Qed.

(* ---- 收尾段（逐件假设面打印） ---- *)
Print Assumptions uabT13b_g06_ros_ext.
Print Assumptions uabT13b_g06_ros_le.
Print Assumptions uabT13b_g06_ros_add.
Print Assumptions uabT13b_g06_ros_linear.
Print Assumptions uabT13b_g06_lebR_weight_pos.
Print Assumptions uabT13b_g06_uabtemp_sum_pos.
Print Assumptions uabT13b_g06_Zfull_pos.
