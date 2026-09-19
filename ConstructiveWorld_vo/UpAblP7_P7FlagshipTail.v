(* ============================================================ *)
(* UpAblP7_P7FlagshipTail.v —— 论文7 专项消融战役 PA7-10 席乙腿件           *)
(*   （P7BoundedSoftmaxDeep 旗舰五件合龙实例化·乙腿：②③④⑤四件）            *)
(* 母本：P7BoundedSoftmaxDeep.v（席位P7C 深层消融件；本件只读消费其        *)
(*   上游出节面，原树零改）。甲腿席 PA7-09 件（UpAblP7_P7KappaFlagship     *)
(*   与其台账）本件不依赖、不装设、不触碰——乙腿独立成件，旗舰件①与其      *)
(*   供给桥归甲腿，合龙面留给主会话。                                      *)
(* 母本坐标（文件:行号 → 本件消费位）：                                    *)
(*   P7BoundedSoftmaxDeep.v:263 p7d_one_le_hi_sq      → 乙腿②（展幅）     *)
(*   P7BoundedSoftmaxDeep.v:107 p7d_swap_of_sum_eq_list → 乙腿③（交换）   *)
(*   P7BoundedSoftmaxDeep.v:224 p7d_nR_pos_gives_enum_nonempty →         *)
(*   P7BoundedSoftmaxDeep.v:213 p7d_enum_nonempty_gives_nR_pos →          *)
(*       乙腿④（双向件较易侧＝反向者：出节无求和实例位，单例互证）         *)
(*   P7BoundedSoftmaxDeep.v:312 p7d_factor_over_hi    → 乙腿⑤（因子-倒数） *)
(*   P7BoundedSoftmaxDeep.v:76  p7d_lsum_fubini_gen   → ③ 载体恒等面直击   *)
(*   AttnDoeblin.v:478 bs_list_sum／:545 bs_hi_pos／:118 nat_to_R_pos     *)
(* 分级申报：N1 库内放电件直连（母本出节件＋S01 类字段＋基座 nat_to_R_pos）； *)
(* N2 已证导出（②乙独立链：lo·hi==one 六步恒等链＋严格单调三步洗牌链，     *)
(*   不消费 bs_lo_hi_eq／bs_lo_lt_hi 两母件承重位）；N3 实例供给           *)
(*   （温度:=1、利差:=1 具体装配，one_pos＋inv_pos_pos 供给；单例载体      *)
(*   (szero::nil) 具体数据位）。                                           *)
(* 依赖清单：S01_BaseRing＋AttnDoeblin＋P7BoundedSoftmaxDeep＋Stdlib List  *)
(*   ——只读消费，原树零改；不装设甲腿件（避免在飞依赖）。                  *)
(* κ∈(0,1) 前件包口径：温度/利差数据对＋两正性证书＋指数字段四件           *)
(*   （正性/零点/加法/严格单调）＝乙腿②⑤共用九参包；②乙即该包的消费形    *)
(*   （hi:=expf(invT·Δ) 面，expf_plus／mono 链供给），展幅 1≤hi² 为        *)
(*   κ:=1−lo²∈(0,1) 下界的展幅对偶补件。                                   *)
(* sum_eq_list 数据位裁定（承 CYD7 IdSlotTranslate 头注定谳）：SumOver     *)
(*   八字段实例构造不可行（zero_nonneg 全称位须 enum 满射数据）；故③之    *)
(*   实例形走「载体恒等供给」双面：恒等载体面（bs_list_sum 折叠为载体，    *)
(*   恒等级）＋显式全称升格面（求和实例与规范化证书升格为全称位——更强     *)
(*   诚实形），不冒充实例构造。                                            *)
(* 定理面（九件，全 Qed，前缀 uaft_）：                                    *)
(*   ②甲 uaft_one_le_hi_sq_one ——实例装配 @ 温度:=1、利差:=1               *)
(*   ②乙 uaft_one_le_hi_sq_indep ——独立链复刻（恒等六步＋单调三步）        *)
(*   ③甲 uaft_swap_of_sum_eq_list_explicit ——显式全称升格（实例装配）      *)
(*   ③乙 uaft_swap_list_carrier_id ——恒等载体面（上游直击 fubini）         *)
(*   ③丙 uaft_swap_singleton_carrier ——单例载体具体位（定义性坍缩）        *)
(*   ④甲 uaft_singleton_nR_pos ——单例 nR>0 计算位（nat_to_R_pos 直击）     *)
(*   ④乙 uaft_singleton_nonempty_hand ——独立链（长度同余＋one_pos 链）     *)
(*   ④丙 uaft_singleton_nonempty_via_mother ——母件反向消费（双向互证）     *)
(*   ⑤甲 uaft_factor_over_hi_one ——实例装配 @ 温度:=1、利差:=1             *)
(* 红线自审：零 公理/承认件/参数/猜想/弃证；Set 层语句；全 Qed；文尾       *)
(*   逐件全 Closed；独立伴生件不并入原模块；前缀 uaft_ 本件内防撞；        *)
(*   全中文零承认件写法（头注与注释同口径）。                              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import P7BoundedSoftmaxDeep.
From Stdlib Require Import List.

(* ################ 段一：乙腿②⑤——展幅与因子-倒数（九参前件包节） ######## *)

Section UaftScale.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* ②甲 ←p7d_one_le_hi_sq @ 温度:=1、利差:=1（实例装配路：数据双槽取 one，  *)
(*   one_pos 供两处正性位，invT:=inv_pos one one_pos 具体形；指数族保持     *)
(*   抽象——全库无具体实数实例，T146 工法档口径） *)
Theorem uaft_one_le_hi_sq_one :
  forall (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos one one_pos) one))
               (expf (mult (inv_pos one one_pos) one))).
Proof.
  intros expf expf_pos expf_zero expf_plus expf_mono_lt.
  exact (p7d_one_le_hi_sq one one_pos one one_pos expf expf_pos
           expf_zero expf_plus expf_mono_lt).
Qed.

(* ②乙 ←p7d_one_le_hi_sq 同句独立链复刻：lo·hi==one 六步恒等链             *)
(*   （expf_plus→distrib 反向→加法交换→加逆→乘零→指数零点）＋lo<hi          *)
(*   严格单调三步洗牌（lt_mult_compat＋mult_comm 两次 lt_id_l 搭桥），      *)
(*   不消费母件承重位 bs_lo_hi_eq／bs_lo_lt_hi。 *)
Theorem uaft_one_le_hi_sq_indep :
  forall (temp : R) (temp_pos : lt zero temp) (Delta : R) (Delta_pos : lt zero Delta)
         (expf : R -> R) (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)))
         (expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b)),
  le one (mult (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) Delta))).
Proof.
  intros temp temp_pos Delta Delta_pos expf expf_pos expf_zero expf_plus expf_mono_lt.
  assert (Hlhi : Id (mult (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))) one).
  { exact (id_trans (id_sym (expf_plus (mult (inv_pos temp temp_pos) (opp Delta))
                                       (mult (inv_pos temp temp_pos) Delta)))
             (id_trans (id_cong expf (id_sym (distrib (inv_pos temp temp_pos)
                                                     (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_comm (opp Delta) Delta)))
             (id_trans (id_cong expf (id_cong (fun w : R => mult (inv_pos temp temp_pos) w)
                                    (plus_opp Delta)))
                       (id_trans (id_cong expf (mult_zero (inv_pos temp temp_pos)))
                                 expf_zero))))). }
  assert (Hopplt : lt (opp Delta) Delta).
  { exact (le_lt_trans (opp Delta) zero Delta
             (le_id_r (opp Delta) (opp zero) zero opp_zero_t13
                (opp_le_compat zero Delta (lt_le_iff zero Delta (inl Delta_pos))))
             Delta_pos). }
  assert (Hlohi : lt (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                     (expf (mult (inv_pos temp temp_pos) Delta))).
  { apply (expf_mono_lt (mult (inv_pos temp temp_pos) (opp Delta))
                        (mult (inv_pos temp temp_pos) Delta)).
    exact (lt_id_l (mult (inv_pos temp temp_pos) (opp Delta))
                   (mult (opp Delta) (inv_pos temp temp_pos))
                   (mult (inv_pos temp temp_pos) Delta)
                   (mult_comm (inv_pos temp temp_pos) (opp Delta))
                   (lt_id_r (mult (opp Delta) (inv_pos temp temp_pos))
                            (mult Delta (inv_pos temp temp_pos))
                            (mult (inv_pos temp temp_pos) Delta)
                            (mult_comm Delta (inv_pos temp temp_pos))
                            (lt_mult_compat (opp Delta) Delta
                               (inv_pos temp temp_pos)
                               (inv_pos_pos temp temp_pos) Hopplt))). }
  apply (le_trans _ (mult (expf (mult (inv_pos temp temp_pos) Delta))
                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))).
  - exact (le_id_l one (mult (expf (mult (inv_pos temp temp_pos) Delta))
                             (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (mult (expf (mult (inv_pos temp temp_pos) Delta))
                   (expf (mult (inv_pos temp temp_pos) (opp Delta))))
             (id_sym (id_trans (mult_comm (expf (mult (inv_pos temp temp_pos) Delta))
                                          (expf (mult (inv_pos temp temp_pos) (opp Delta))))
                               Hlhi))
             (le_refl (mult (expf (mult (inv_pos temp temp_pos) Delta))
                            (expf (mult (inv_pos temp temp_pos) (opp Delta)))))).
  - exact (le_mult_compat_r (expf (mult (inv_pos temp temp_pos) Delta))
               (expf (mult (inv_pos temp temp_pos) (opp Delta)))
               (expf (mult (inv_pos temp temp_pos) Delta))
               (lt_le_iff zero (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl (expf_pos (mult (inv_pos temp temp_pos) Delta))))
               (lt_le_iff (expf (mult (inv_pos temp temp_pos) (opp Delta)))
                          (expf (mult (inv_pos temp temp_pos) Delta))
                          (inl Hlohi))).
Qed.

(* ⑤甲 ←p7d_factor_over_hi @ 温度:=1、利差:=1（实例装配路：因子-倒数       *)
(*   恒等式 e^{a/T}·(e^{Δ/T})⁻¹ == e^{(a−Δ)/T} 之具体温度形；hi 正性位由   *)
(*   bs_hi_pos @ one/one 装配供给） *)
Theorem uaft_factor_over_hi_one :
  forall (a b : R) (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b))),
  Id (mult (expf (mult (inv_pos one one_pos) a))
           (inv_pos (expf (mult (inv_pos one one_pos) one))
                    (AttnDoeblin.bs_hi_pos one one_pos one expf expf_pos)))
     (expf (mult (inv_pos one one_pos) (plus a (opp one)))).
Proof.
  intros a b expf expf_pos expf_zero expf_plus.
  exact (p7d_factor_over_hi one one_pos one a b expf expf_pos expf_zero expf_plus).
Qed.

End UaftScale.

(* ################ 段二：乙腿④——双向件较易侧（反向）与单例互证 ########## *)
(* 节前导复刻母本段四（实读裁定：反向件出节无求和实例位——较易侧；正向件   *)
(*   须 sel 全称位，本件以单例计算位补其具体形）。                          *)

Section UaftTail.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* ④甲（单例 nR>0 计算位）：nat_to_R_pos 直击——length (s::nil) 归约面     *)
(*   S (length nil) 与 nat_to_R_pos 全称位定义性合一（计算供给）。 *)
Theorem uaft_singleton_nR_pos : forall s : S,
  lt zero (AttnDoeblin.nat_to_R (length (s :: nil))).
Proof.
  intro s.
  exact (AttnDoeblin.nat_to_R_pos (length (nil : list S))).
Qed.

(* ④乙（独立链）：Id (s::nil) nil 沿长度同余洗成 Id one zero，与 one_pos   *)
(*   冲突放电（lt_id_l 搭桥＋lt_irrefl 收口）——零母件消费。 *)
Theorem uaft_singleton_nonempty_hand : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intros s H.
  assert (Hone0 : Id one zero).
  { exact (id_trans (id_sym (plus_zero one))
             (id_cong (fun l : list S => AttnDoeblin.nat_to_R (length l)) H)). }
  exact (lt_irrefl one (lt_id_l one zero one Hone0 one_pos)).
Qed.

(* ④丙（母件反向消费）：p7d_nR_pos_gives_enum_nonempty @ 单例载体——       *)
(*   与④乙双向互证（同一命题两独立来路）。 *)
Theorem uaft_singleton_nonempty_via_mother : forall s : S, Not (Id (s :: nil) nil).
Proof.
  intro s.
  exact (p7d_nR_pos_gives_enum_nonempty (s :: nil)
           (AttnDoeblin.nat_to_R_pos (length (nil : list S)))).
Qed.

End UaftTail.

(* ################ 段三：乙腿③——sum_eq_list 数据位之载体恒等供给 ######## *)
(* 节前导复刻母本段二前导（CYD7 裁定：SumOver 八字段实例构造不可行；故      *)
(*   三面施工：显式全称升格／恒等载体／单例具体位）。                       *)

Section UaftCarrier.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {SS : StateSpace RI}.

(* ③甲（显式全称升格·实例装配）：母件 p7d_swap_of_sum_eq_list 出节形之    *)
(*   全称升格——求和实例与规范化证书由节 Variable 位升格为显式全称位        *)
(*   （更强诚实形），f 全称收尾。 *)
Theorem uaft_swap_of_sum_eq_list_explicit :
  forall (SO : SumOver RI SS) (enum : list S)
         (sum_eq_list : forall g : S -> R,
            Id (@sum_over_S RI SS SO g) (AttnDoeblin.bs_list_sum g enum))
         (f : S -> S -> R),
  Id (@sum_over_S RI SS SO (fun s : S => @sum_over_S RI SS SO (fun s' : S => f s s')))
     (@sum_over_S RI SS SO (fun s' : S => @sum_over_S RI SS SO (fun s : S => f s s'))).
Proof.
  intros SO enum sum_eq_list f.
  exact (p7d_swap_of_sum_eq_list enum sum_eq_list f).
Qed.

(* ③乙（恒等载体面·上游直击）：取 bs_list_sum 折叠为求和载体——交换恒等    *)
(*   即双重列表和 fubini（p7d_lsum_fubini_gen 直击），零求和实例位。 *)
Theorem uaft_swap_list_carrier_id :
  forall (enum : list S) (f : S -> S -> R),
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') enum) enum)
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') enum) enum).
Proof.
  intros enum f.
  exact (p7d_lsum_fubini_gen f enum enum).
Qed.

(* ③丙（单例载体具体位）：enum:=(szero::nil) 具体数据位——内外两折叠在     *)
(*   单例载体上定义性坍缩为同一正规形（恒等级，零引理消费）。 *)
Theorem uaft_swap_singleton_carrier :
  forall f : S -> S -> R,
  Id (AttnDoeblin.bs_list_sum
        (fun s : S => AttnDoeblin.bs_list_sum (fun s' : S => f s s') (szero :: nil))
        (szero :: nil))
     (AttnDoeblin.bs_list_sum
        (fun s' : S => AttnDoeblin.bs_list_sum (fun s : S => f s s') (szero :: nil))
        (szero :: nil)).
Proof.
  intro f.
  exact id_refl.
Qed.

End UaftCarrier.

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uaft_one_le_hi_sq_one.
Print Assumptions uaft_one_le_hi_sq_indep.
Print Assumptions uaft_factor_over_hi_one.
Print Assumptions uaft_singleton_nR_pos.
Print Assumptions uaft_singleton_nonempty_hand.
Print Assumptions uaft_singleton_nonempty_via_mother.
Print Assumptions uaft_swap_of_sum_eq_list_explicit.
Print Assumptions uaft_swap_list_carrier_id.
Print Assumptions uaft_swap_singleton_carrier.
