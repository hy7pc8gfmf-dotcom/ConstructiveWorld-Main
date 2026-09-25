(* UpAblP7_LoHiBridge.v —— lo/hi 桥接引理组：二分之一抽象形        *) (*   half:=inv_pos (plus one one) two_pos 的有界性与序关系事实。   *)
(* 使命：本件形式化三条事实：① Or 编码 le＋neq⟹lt；② 抽象 le＋neq   *) (*   ⟹lt；③ half2:=half·half 满足 0<half2 且 half2<1。用位：        *)
(*   LoHiSqueeze.v 中 lo:=expf(invT·oppΔ) 经 invT:=inv_pos 别名使用、 *) (*   利差 Delta/Delta_pos 直连 lo/hi；本件在 lo:=half 的抽象形位给出  *)
(*   完整前提形 δ*∈(0,1)。                                         *)
(* 定理面（五件，全 Qed，前缀 uahlb_）：                            *)
(*   uahlb_le_neq_lt —— Or 编码 le＋neq⟹lt：Or 逐支分情形（lt 支     *)
(*       直取；eq 支与 neq 前提矛盾消去，Empty_set 归谬）；           *)
(*   uahlb_le_abs_neq_lt —— 抽象 le＋neq⟹lt：经 ord_le_dec 在        *)
(*       (b,a) 位分情形，le b a 支由 le_antisym 反设，非 le 支经       *)
(*       not_le_lt 直接推得；构造性，无经典逻辑；                     *)
(*   uahlb_half2_le_one —— le 传递链：le_plus_nonneg_r 与 half_twice  *)
(*       恒等形经 le_trans 合成 half2≤half≤one；                      *)
(*   uahlb_half2_neq_one —— half2≠1：加倍恒等式（half_twice、         *)
(*       mult_one、plus_assoc/plus_opp/plus_zero）归约至               *)
(*       (1+1+1)=0，与 0<(1+1+1)（plus_positive）对角矛盾 lt_irrefl；  *)
(*   uahlb_delta_star_bounded_half —— 合取 0<half2 且 half2<1：       *)
(*       eq_dec 分情形重建 Or 编码 le（Id 支直取、neq 支经             *)
(*       uahlb_le_abs_neq_lt 升为 lt），再由 uahlb_le_neq_lt 推得      *)
(*       half2<1；0<half2 支由 mult_positive 直接推得。                *)
(* 辅助定义：uahlb_ord_dec/uahlb_not_le_lt/uahlb_eq_dec —— 经 match   *)
(*   Build_DecidableOrder 逐字段投影 DecidableOrder 记录（字段         *)
(*   ord_le_dec/not_le_lt/eq_dec；lt_dec 与 Stdlib Compare_dec 同名    *)
(*   遮蔽，故以投影别名取用）。                                       *)
(* 依赖：Require Import S01_BaseRing；不装设 Paper7Ablation/          *)
(*   P7BoundedSoftmaxDeep/被使用各件本身——依赖面最小。                *)
(* 对标：stdlib Compare_dec（可判定序分情形）；mathlib                *)
(*   lt_of_le_of_ne（le＋neq⟹lt）的构造性 Set 层对应。                 *)
(* 构造性注记：语句面全 Set 层（合取 S01 And=prod、析取 Or=sum、       *)
(*   否定 Not=→Empty_set）；零承认；可提取。                          *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。         *)

Require Import S01_BaseRing.

(* ############ 段一：uahlb_le_neq_lt —— Or 编码 le＋neq⟹lt ############### *)
(* 约定：本库序 le 取 Or(lt,Id) 编码（S01_BaseRing 实数层；UpTVDoeblin 中     *)
(* tvd_abs_le_id 同此编码）。Or 编码 le 逐支分情形：lt 支直取；eq 支与 neq    *)
(* 前提矛盾消去（Empty_set 归谬，构造性，无经典逻辑）。                       *)

Section UahlbBridgeOr.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Theorem uahlb_le_neq_lt : forall a b : R,
  Or (lt a b) (Id a b) -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hle Hneq.
  destruct Hle as [Hlt | Heq].
  - exact Hlt.
  - destruct (Hneq Heq).
Qed.

End UahlbBridgeOr.

(* ############ 段二：uahlb_le_abs_neq_lt —— 抽象 le＋neq⟹lt ############## *)
(* 抽象 le 无逐支分解字段，经 DecidableOrder 的 ord_le_dec 在 (b,a) 位分情形：*)
(* le b a 支与 le a b 由 le_antisym 得 Id a b，与 neq 前提矛盾消去；非 le 支  *)
(* 经 not_le_lt 直接推得 lt a b。构造性分情形，无经典逻辑。                   *)

Section UahlbBridgeLe.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 投影别名定式：match Build_DecidableOrder 逐字段取用，防字段名遮蔽        *)
Definition uahlb_ord_dec : forall a b : R, Or (le a b) (Not (le a b)) :=
  match DO with
  | Build_DecidableOrder _ old _ _ _ _ => old
  end.

Definition uahlb_not_le_lt : forall a b : R, Not (le a b) -> lt b a :=
  match DO with
  | Build_DecidableOrder _ _ _ _ nll _ => nll
  end.

Theorem uahlb_le_abs_neq_lt : forall a b : R,
  le a b -> Not (Id a b) -> lt a b.
Proof.
  intros a b Hle Hneq.
  destruct (uahlb_ord_dec b a) as [Hle' | Hnle'].
  - destruct (Hneq (le_antisym a b Hle Hle')).
  - exact (uahlb_not_le_lt b a Hnle').
Qed.

End UahlbBridgeLe.

(* ############ 段三：uahlb_delta_star_bounded_half —— δ*∈(0,1) 全前提形 ### *)
(* half:=inv_pos (plus one one) two_pos（two_pos/inv_pos_pos 提供正性）；      *)
(* half2:=mult half half（δ*=lo² 定义位的抽象形）。先证 uahlb_half2_le_one     *)
(* 与 uahlb_half2_neq_one，再经 uahlb_eq_dec 等辅助件合成全件。               *)

Section UahlbHalfStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* eq_dec 投影别名（同 uahlb_ord_dec 的 match 投影定式） *)
Definition uahlb_eq_dec : forall a b : R, Or (Id a b) (Not (Id a b)) :=
  match DO with
  | Build_DecidableOrder _ _ _ ed _ _ => ed
  end.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 证明素材（半的加倍恒等式组）：                                             *)
(*   0<half（inv_pos_pos 于 two_pos）；0<half2（mult_positive）；              *)
(*   half2+half2=half（half_twice half）；half+half=1（mult_one 与            *)
(*   half_twice one）；1=(half2+half2)+(half2+half2)（恒等重排）。             *)
(*   下列 uahlb_half2_le_one 与 uahlb_half2_neq_one 直接使用这组恒等式。       *)

Lemma uahlb_half2_le_one : le half2 one.
Proof.
  assert (Lh : le zero half2).
  { exact (lt_le_iff zero half2
             (@inl (lt zero half2) (Id zero half2)
                (mult_positive half half
                   (inv_pos_pos (plus one one) two_pos)
                   (inv_pos_pos (plus one one) two_pos)))). }
  assert (L1 : le half2 (plus half2 half2)).
  { exact (le_plus_nonneg_r half2 half2 Lh). }
  assert (L2 : le half2 half).
  { exact (le_id_r half2 (plus half2 half2) half (half_twice half) L1). }
  assert (Lh2 : le zero half).
  { exact (lt_le_iff zero half
             (@inl (lt zero half) (Id zero half)
                (inv_pos_pos (plus one one) two_pos))). }
  assert (L3 : le half (plus half half)).
  { exact (le_plus_nonneg_r half half Lh2). }
  exact (le_trans half2 half one L2
           (le_id_r half (plus half half) one
              (id_trans (id_cong (fun x => plus x x)
                          (id_sym (mult_one half)))
                 (half_twice one))
              L3)).
Qed.

Lemma uahlb_half2_neq_one : Not (Id half2 one).
Proof.
  intro Hid.
  assert (Hone2 : Id one (plus (plus half2 half2) (plus half2 half2))).
  { exact (id_trans
             (id_sym (id_trans (id_cong (fun x => plus x x)
                          (id_sym (mult_one half)))
                        (half_twice one)))
             (id_sym (id_cong (fun x => plus x x) (half_twice half)))). }
  assert (Hfour : Id one (plus (plus one one) (plus one one))).
  { exact (id_trans Hone2
             (id_cong (fun x => plus (plus x x) (plus x x)) Hid)). }
  assert (Hstep3 : Id zero
             (plus (plus (plus one one) (plus one one)) (opp one))).
  { exact (id_trans (id_sym (plus_opp one))
             (id_cong (fun x => plus x (opp one)) Hfour)). }
  assert (Hinner : Id (plus (plus one one) (opp one)) one).
  { exact (id_trans (id_sym (plus_assoc one one (opp one)))
             (id_trans (id_cong (fun w => plus one w) (plus_opp one))
                (plus_zero one))). }
  assert (Hthree : Id zero (plus (plus one one) one)).
  { exact (id_trans Hstep3
             (id_trans
                (id_sym (plus_assoc (plus one one) (plus one one)
                          (opp one)))
                (id_cong (fun w => plus (plus one one) w) Hinner))). }
  exact (lt_irrefl zero
           (lt_id_r zero (plus (plus one one) one) zero (id_sym Hthree)
              (plus_positive (plus one one) one two_pos one_pos))).
Qed.

(* uahlb_delta_star_bounded_half：合取 0<half2 且 half2<1 的完整前提形。      *)
(* half2<1 支：eq_dec 分情形重建 Or 编码 le——Id 支直取（inr）；neq 支经       *)
(* uahlb_le_abs_neq_lt 升为 lt 直取（inl）；再由 uahlb_le_neq_lt 推得：lt 支   *)
(* 直取、Id 支与 uahlb_half2_neq_one 前提矛盾消去。0<half2 支：mult_positive。 *)
Theorem uahlb_delta_star_bounded_half :
  And (lt zero half2) (lt half2 one).
Proof.
  assert (Hneq : Not (Id half2 one)).
  { exact uahlb_half2_neq_one. }
  assert (Hle1 : le half2 one).
  { exact uahlb_half2_le_one. }
  assert (O : Or (lt half2 one) (Id half2 one)).
  { destruct (uahlb_eq_dec half2 one) as [Hid | Hneq'].
    - exact (@inr (lt half2 one) (Id half2 one) Hid).
    - exact (@inl (lt half2 one) (Id half2 one)
               (uahlb_le_abs_neq_lt half2 one Hle1 Hneq')). }
  split.
  - exact (mult_positive half half
             (inv_pos_pos (plus one one) two_pos)
             (inv_pos_pos (plus one one) two_pos)).
  - exact (uahlb_le_neq_lt half2 one O Hneq).
Qed.

End UahlbHalfStar.

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
Print Assumptions uahlb_le_neq_lt.
Print Assumptions uahlb_le_abs_neq_lt.
Print Assumptions uahlb_half2_le_one.
Print Assumptions uahlb_half2_neq_one.
Print Assumptions uahlb_delta_star_bounded_half.
