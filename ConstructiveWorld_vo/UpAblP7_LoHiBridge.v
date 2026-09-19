(* ============================================================ *)
(* UpAblP7_LoHiBridge.v —— 论文7 专项消融战役 PA7-14 席（LoHi 次波·乙腿）      *)
(*   供给桥 + δ* 全前件包姊妹镜像（与 PA7-13 姊妹席 T156 cross 合璧互补；       *)
(*   本席辖 bridge 面，cross-节合璧零碰）。                                   *)
(* 使命：LoHiSqueeze.v 两节温度对 temp/temp_pos 仅经 invT:=inv_pos 别名消费、  *)
(*   利差对 Delta/Delta_pos 直连 lo/hi——本件在 lo:=inv_pos (plus one one)     *)
(*   two_pos（二分之一抽象形）位供给两件：                                    *)
(*   件甲 le+neq⟹lt 供给桥（Or 编码逐支：lt 支直取、eq 支与 Neq 前提矛盾      *)
(*       消去；T84/FA3 口径，UpTVDoeblin tvd_abs_le_id:73 路线注记同源）；     *)
(*   件乙 δ*<1 姊妹镜像（件七同款加倍还原链 + eq_dec + 桥组，与 PA7-05 件七    *)
(*       互补成对——件七是单侧 0<1−δ*（κ∈(0,1) 前件包），本件做 δ*∈(0,1)      *)
(*       全前件包）。                                                        *)
(* 实读台账（2026-09-19 探针定谳）：                                          *)
(*   LoHiSqueeze.v:78 lo:=expf(invT·oppΔ) 别名面、:108-120 δ*:=lo² 定义位；    *)
(*   UpAblP7_LoHiSqueeze.v:213-258 件七左支链（half_twice S01:503 加倍还原     *)
(*   ＋plus_positive＋恒等洗牌五步 Gup/Gtotal）；                             *)
(*   S01:160 lt_le_iff（Or 编码→le）、S01:560 le_plus_nonneg_r（le 泵）、      *)
(*   S01:473 one_neq_zero（neq 归谬定式：正性项 transport 至对角 lt_irrefl）、  *)
(*   S01:329-335 DecidableOrder 五字段（ord_le_dec/lt_dec/eq_dec/not_le_lt/    *)
(*   lt_le_iff_dec；lt_dec 被 Stdlib Compare_dec 遮蔽——WeakTriangleClose:120  *)
(*   fa53 投影别名定式 match Build_DecidableOrder 逐字段取用）。               *)
(* 定理面（五件，全 Qed，前缀 uahlb_ 本件内防撞）：                           *)
(*   件甲 uahlb_le_neq_lt —— Or 编码 le＋neq⟹lt 供给桥（任务件 a）；           *)
(*   件乙 uahlb_le_abs_neq_lt —— 抽象 le＋neq⟹lt（ord_le_dec 逐支＋           *)
(*       le_antisym 反证＋not_le_lt 放电，构造性零经典）；                     *)
(*   件丙 uahlb_half2_le_one —— le 泵链（le_plus_nonneg_r×2＋half_twice       *)
(*       等形降位＋le_trans 合龙：half2≤half≤one）；                          *)
(*   件丁 uahlb_half2_neq_one —— δ*≠1 供给件（件七 Hone2 加倍还原链镜像＋     *)
(*       四−一=三洗牌＋plus_positive 归谬：三=零 与 0<三 对角撞 lt_irrefl）；   *)
(*   件戊 uahlb_delta_star_bounded_half —— δ*∈(0,1) 全前件包（eq_dec 逐支     *)
(*       重打包 Or 编码 le：Id 支直取、neq 支经件乙升 lt；再由件甲合龙 δ*<1；  *)
(*       左支 mult_positive 直放电 0<δ*）。                                   *)
(* 红线自审：语句面全 Set 层（合取用 S01 And=prod、析取用 S01 Or=sum、否定用   *)
(*   S01 Not=→Empty_set，零 Prop 泄露）；公理面零新增；Require 面仅            *)
(*   S01_BaseRing（不装设 Paper7Ablation/P7BoundedSoftmaxDeep/母件本身——      *)
(*   T149 摘要漂移墙防避，比母件消费更强的不依赖位）；原 vo_9.1/Live 正本     *)
(*   零改；既有 UpAblP7* 全零改（只读复用件七链形）；全中文零承认件写法。      *)
(* ============================================================ *)

Require Import S01_BaseRing.

(* ############ 段一：件甲——Or 编码 le＋neq⟹lt 供给桥 #################### *)
(* 口径：real_le=Or(lt,eq)（cauchy 实数层 real_le 编码；UpTVDoeblin           *)
(* tvd_abs_le_id:73 路线注记同源）。Or 编码 le 逐支施工：lt 支直取；eq 支与   *)
(* Neq 前提矛盾消去（Empty_set 归谬，构造性零经典）。                         *)

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

(* ############ 段二：件乙——抽象 le＋neq⟹lt（可判定序供给） ############### *)
(* 抽象 le 无逐支分解字段，经 DecidableOrder 的 ord_le_dec 在 (b,a) 位逐支：  *)
(* le b a 支与 le a b 合流 le_antisym 放电 Id，与 Neq 前提矛盾消去；非 le 支  *)
(* 经 not_le_lt 直放电 lt a b。构造性逐支施工，零经典逻辑。                   *)

Section UahlbBridgeLe.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* fa53 投影别名定式（WeakTriangleClose:120 同款 match 投影，防字段名遮蔽） *)
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

(* ############ 段三：δ* 全前件包姊妹镜像（lo:=二分之一抽象形） ############ *)
(* half:=inv_pos (plus one one) two_pos（two_pos/inv_pos_pos 供给，件七同位）； *)
(* half2:=mult half half（δ*=lo² 定义位镜像）。件丙 le 泵链、件丁 neq 链、     *)
(* 件戊合龙全件 eq_dec＋件乙＋件甲。                                          *)

Section UahlbHalfStar.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* eq_dec 投影别名（同 fa53 定式） *)
Definition uahlb_eq_dec : forall a b : R, Or (Id a b) (Not (Id a b)) :=
  match DO with
  | Build_DecidableOrder _ _ _ ed _ _ => ed
  end.

Let half := inv_pos (plus one one) two_pos.
Let half2 := mult half half.

(* 件七同款加倍还原链（UpAblP7_LoHiSqueeze.v:216-228 逐字镜像）： *)
(*   Hhp: 0<half（inv_pos_pos@two_pos）；Hh2p: 0<δ*（mult_positive）；        *)
(*   Hq: δ*+δ*=half（half_twice 加倍还原）；Hone: half+half=1（mult_one       *)
(*   降形＋half_twice one）；Hone2: 1=δ*+δ*+δ*+δ*（恒等洗牌）。               *)
(*   上列四件在件丁/件戊证明体内联复用（件七同款，本件零转发零母件装设）。 *)

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

(* 件戊：δ*∈(0,1) 全前件包（与件七 κ∈(0,1) 前件包互补成对）。 *)
(* δ*<1 支：eq_dec 逐支重打包 Or 编码 le——Id 支直取（inr）；neq 支经件乙     *)
(* （抽象 le＋neq⟹lt）升 lt 直取（inl）；再由件甲（Or 编码 le＋neq⟹lt）     *)
(* 合龙：lt 支直取、Id 支与件丁 neq 前提矛盾消去。0<δ* 支：mult_positive。   *)
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

(* ---- PA 收尾段（逐件 Closed 判读；G1/G4 审查留痕面） ---- *)
Print Assumptions uahlb_le_neq_lt.
Print Assumptions uahlb_le_abs_neq_lt.
Print Assumptions uahlb_half2_le_one.
Print Assumptions uahlb_half2_neq_one.
Print Assumptions uahlb_delta_star_bounded_half.
