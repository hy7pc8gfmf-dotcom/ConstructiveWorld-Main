(* ===================================================================== *)
(* UpAblP6_StateSpace_inst.v —— PA6-34 席：SecondLawQuantified 残面②      *)
(*   「任意 StateSpace 非平凡实例」（PA6-23/T231 闭合留账另账）兑现件。    *)
(* --------------------------------------------------------------------- *)
(* 【使命】上游节参载体类 Class StateSpace (RI : RealInterface)            *)
(*   （S01_BaseRing.v:1158，21 字段：S/四运算/八代数律/smetric+四度量律/  *)
(*   clim/clim_unique/cauchy_complete_S）此前唯一满律实例=RealSelfSS      *)
(*   （R 自状态空间，S01:1222）；S06:3093 ListStateSpace 节仅散定义不满律。*)
(*   本席给出第二个满律非平凡实例：R×R 乘积载体（L1 度量、逐点线性结构、   *)
(*   双分量 lim 收敛），≥3 态（(0,0)/(1,0)/(0,1) 两两非 Id 真证），       *)
(*   21 字段全构造零缺口，另附一锚定理实例面（IdSlotTranslate 依存件）。   *)
(* 【有限载体不可能性（如实落账）】bool×bool/三态枚举等有穷载体满律在      *)
(*   数学上关闭：inv_pos 对正整数标量 fourR=1+1+1+1 给逆（fourR>0 由      *)
(*   one_pos+lt_plus_compat 真证），任意标量 a=fourR·(a·inv fourR)        *)
(*   （mult_assoc/comm/one+inv_pos_correct），故满足逐点平方律的载体上    *)
(*   标量作用四折叠合为零映射，smult_one 迫载体退化为单点——本席把该      *)
(*   塌缩面形式化为定理 uab34_finite_collapse（任意抽象 StateSpace 上）。 *)
(*   因而非平凡实例取无穷载体 R×R（≥3 态面由三钉定理钉死）。               *)
(* 【红线自审】出口面全 Set 层 Id/le/lt（Id=S01:61 ML 恒等型，id_sym/     *)
(*   id_trans/id_cong 链）；零缺口声明语句；全部定理类枚 Proof 配 Qed     *)
(*   闭合（无一例外）；Print Assumptions 5 处留痕；uab34_ 前缀全库防撞。   *)
(* 【供体（全 @ 全参调用，cw czn14 检验实测）】RI 场律/序律/度量/lim 系    *)
(*   =RealInterface 字段；one_pos/lt_plus_compat/le_plus_compat           *)
(*   =RealInterfaceEnhanced 字段（S01:216-222）；idt_sumf/idt_list_sum/   *)
(*   idt_sum_eq_list/idt_slot_g01=IdSlotTranslate 节件（Context {RI}{SS}  *)
(*   依存 StateSpace 的上游一锚）；AttnDoeblin.bs_list_sum（出节真机）。   *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import AttnDoeblin.
Require Import IdSlotTranslate.
From Stdlib Require Import List.

(* ============================================================ *)
(* §一 R×R 乘积载体：运算/度量/收敛定义面 + 21 字段律面            *)
(* ============================================================ *)
Section ProdRR.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let Rb := @RI_base RIE.              (* RealInterface 参数位 *)
Let RR := prod (@R Rb) (@R Rb).      (* 实数积对载体型（字面积型，投影 R 卡死项不可作积展开） *)

(* ---- 乘积运算/度量/收敛（全 @ 全参，逐点定义） ---- *)
Definition uab34_pzero : RR := (@zero Rb, @zero Rb).

Definition uab34_psplus (x y : RR) : RR :=
  (@plus Rb (fst x) (fst y), @plus Rb (snd x) (snd y)).

Definition uab34_psmult (a : @R Rb) (x : RR) : RR :=
  (@mult Rb a (fst x), @mult Rb a (snd x)).

Definition uab34_psopp (x : RR) : RR :=
  (@opp Rb (fst x), @opp Rb (snd x)).

Definition uab34_pmetric (x y : RR) : @R Rb :=
  @plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (snd x) (snd y)).

Definition uab34_pclim (u : nat -> RR) (l : RR) : Set :=
  prod (@lim Rb (fun n => fst (u n)) (fst l))
       (@lim Rb (fun n => snd (u n)) (snd l)).

(* ---- 恒等型组合工具：积对恒等 = 双分量恒等的 pair 组合 ---- *)
Definition uab34_pair_id {A B : Set} {a a' : A} {b b' : B}
  (p : Id a a') (q : Id b b') : Id (pair a b) (pair a' b') :=
  id_trans (id_cong (fun x : A => (x, b)) p)
           (id_cong (fun y : B => (a', y)) q).

(* ---- 底层自给：实数左分配律 (a+b)·c == a·c+b·c ---- *)
(*   （接口只给左因子 distrib a b c : a·(b+c)==a·b+a·c；                *)
(*     用 mult_comm 换位三步组装，S01:1210 先例同构）                    *)
Definition uab34_mult_distrib_l (a b c : @R Rb) :
  Id (@mult Rb (@plus Rb a b) c) (@plus Rb (@mult Rb a c) (@mult Rb b c)) :=
  id_trans (@mult_comm Rb (@plus Rb a b) c)
    (id_trans (@distrib Rb c a b)
      (id_trans (id_cong (fun t => @plus Rb t (@mult Rb c b)) (@mult_comm Rb c a))
                (id_cong (fun t => @plus Rb (@mult Rb a c) t) (@mult_comm Rb c b)))).

(* ---- 四项重组：(x+y)+(z+w) == (x+z)+(y+w)（度量三角 L1 装配用） ---- *)
Definition uab34_plus_swap (x y z w : @R Rb) :
  Id (@plus Rb (@plus Rb x y) (@plus Rb z w)) (@plus Rb (@plus Rb x z) (@plus Rb y w)) :=
  id_trans (id_sym (@plus_assoc Rb x y (@plus Rb z w)))
    (id_trans (id_cong (fun t => @plus Rb x t) (@plus_assoc Rb y z w))
      (id_trans (id_cong (fun t => @plus Rb x (@plus Rb t w)) (@plus_comm Rb y z))
        (id_trans (id_cong (fun t => @plus Rb x t) (id_sym (@plus_assoc Rb z y w)))
                  (@plus_assoc Rb x z (@plus Rb y w))))).

(* ---- 度量的分量控制肢：m(fx,fy) ≤ m1+m2 与 m(sx,sy) ≤ m1+m2 ---- *)
Definition uab34_metric_le_l (x y : RR) :
  @le Rb (@metric Rb (fst x) (fst y)) (uab34_pmetric x y) :=
  le_id_l (@metric Rb (fst x) (fst y))
          (@plus Rb (@metric Rb (fst x) (fst y)) (@zero Rb))
          (uab34_pmetric x y)
          (id_sym (@plus_zero Rb (@metric Rb (fst x) (fst y))))
          (le_plus_compat (@metric Rb (fst x) (fst y)) (@metric Rb (fst x) (fst y))
                          (@zero Rb) (@metric Rb (snd x) (snd y))
                          (@le_refl Rb (@metric Rb (fst x) (fst y)))
                          (@metric_pos Rb (snd x) (snd y))).

Definition uab34_metric_le_r (x y : RR) :
  @le Rb (@metric Rb (snd x) (snd y)) (uab34_pmetric x y) :=
  le_id_l (@metric Rb (snd x) (snd y))
          (@plus Rb (@zero Rb) (@metric Rb (snd x) (snd y)))
          (uab34_pmetric x y)
          (id_trans (id_sym (@plus_zero Rb (@metric Rb (snd x) (snd y))))
                    (@plus_comm Rb (@metric Rb (snd x) (snd y)) (@zero Rb)))
          (le_plus_compat (@zero Rb) (@metric Rb (fst x) (fst y))
                          (@metric Rb (snd x) (snd y)) (@metric Rb (snd x) (snd y))
                          (@metric_pos Rb (fst x) (fst y))
                          (@le_refl Rb (@metric Rb (snd x) (snd y)))).

(* ---- 八代数律（积对逐点，pair_id 组合） ---- *)
Lemma uab34_pplus_assoc : forall a b c : RR,
  Id (uab34_psplus a (uab34_psplus b c)) (uab34_psplus (uab34_psplus a b) c).
Proof.
  intros a b c.
  exact (uab34_pair_id (@plus_assoc Rb (fst a) (fst b) (fst c))
                       (@plus_assoc Rb (snd a) (snd b) (snd c))).
Qed.

Lemma uab34_pplus_comm : forall a b : RR,
  Id (uab34_psplus a b) (uab34_psplus b a).
Proof.
  intros a b.
  exact (uab34_pair_id (@plus_comm Rb (fst a) (fst b))
                       (@plus_comm Rb (snd a) (snd b))).
Qed.

Lemma uab34_pplus_zero : forall a : RR,
  Id (uab34_psplus a uab34_pzero) a.
Proof.
  intros [ax ay].
  exact (uab34_pair_id (@plus_zero Rb ax) (@plus_zero Rb ay)).
Qed.

Lemma uab34_pplus_opp : forall a : RR,
  Id (uab34_psplus a (uab34_psopp a)) uab34_pzero.
Proof.
  intros [ax ay].
  exact (uab34_pair_id (@plus_opp Rb ax) (@plus_opp Rb ay)).
Qed.

Lemma uab34_psmult_one : forall a : RR,
  Id (uab34_psmult (@one Rb) a) a.
Proof.
  intros [ax ay].
  exact (uab34_pair_id
           (id_trans (@mult_comm Rb (@one Rb) ax) (@mult_one Rb ax))
           (id_trans (@mult_comm Rb (@one Rb) ay) (@mult_one Rb ay))).
Qed.

Lemma uab34_psmult_assoc : forall a b : @R Rb, forall x : RR,
  Id (uab34_psmult a (uab34_psmult b x)) (uab34_psmult (@mult Rb a b) x).
Proof.
  intros a b [ax ay].
  exact (uab34_pair_id (@mult_assoc Rb a b ax) (@mult_assoc Rb a b ay)).
Qed.

Lemma uab34_psmult_distrib_r : forall a : @R Rb, forall x y : RR,
  Id (uab34_psmult a (uab34_psplus x y))
     (uab34_psplus (uab34_psmult a x) (uab34_psmult a y)).
Proof.
  intros a [ax ay]. intros [bx byy].
  exact (uab34_pair_id (@distrib Rb a ax bx) (@distrib Rb a ay byy)).
Qed.

Lemma uab34_psmult_distrib_l : forall a b : @R Rb, forall x : RR,
  Id (uab34_psmult (@plus Rb a b) x)
     (uab34_psplus (uab34_psmult a x) (uab34_psmult b x)).
Proof.
  intros a b [ax ay].
  exact (uab34_pair_id (uab34_mult_distrib_l a b ax) (uab34_mult_distrib_l a b ay)).
Qed.

(* ---- 四度量律 ---- *)
Lemma uab34_pmetric_sym : forall x y : RR,
  Id (uab34_pmetric x y) (uab34_pmetric y x).
Proof.
  intros x y.
  exact (id_trans
          (id_cong (fun t => @plus Rb t (@metric Rb (snd x) (snd y)))
                   (@metric_sym Rb (fst x) (fst y)))
          (id_cong (fun t => @plus Rb (@metric Rb (fst y) (fst x)) t)
                   (@metric_sym Rb (snd x) (snd y)))).
Qed.

Lemma uab34_pmetric_pos : forall x y : RR,
  @le Rb (@zero Rb) (uab34_pmetric x y).
Proof.
  intros x y.
  exact (le_id_l (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb)) (uab34_pmetric x y)
           (id_sym (@plus_zero Rb (@zero Rb)))
           (le_plus_compat (@zero Rb) (@metric Rb (fst x) (fst y))
                           (@zero Rb) (@metric Rb (snd x) (snd y))
                           (@metric_pos Rb (fst x) (fst y))
                           (@metric_pos Rb (snd x) (snd y)))).
Qed.

Lemma uab34_pmetric_zero : forall x y : RR,
  Id (uab34_pmetric x y) (@zero Rb) -> Id x y.
Proof.
  intros [ax ay].
  intros [bx byy] H.
  apply (uab34_pair_id
          (@metric_zero Rb ax bx
             (@le_antisym Rb (@metric Rb ax bx) (@zero Rb)
                (@le_id_r Rb (@metric Rb ax bx)
                            (uab34_pmetric (ax, ay) (bx, byy)) (@zero Rb)
                            H (uab34_metric_le_l (ax, ay) (bx, byy)))
                (@metric_pos Rb ax bx)))
          (@metric_zero Rb ay byy
             (@le_antisym Rb (@metric Rb ay byy) (@zero Rb)
                (@le_id_r Rb (@metric Rb ay byy)
                            (uab34_pmetric (ax, ay) (bx, byy)) (@zero Rb)
                            H (uab34_metric_le_r (ax, ay) (bx, byy)))
                (@metric_pos Rb ay byy)))).
Qed.

Lemma uab34_pmetric_triangle : forall x y z : RR,
  @le Rb (uab34_pmetric x z)
         (@plus Rb (uab34_pmetric x y) (uab34_pmetric y z)).
Proof.
  intros x y z.
  exact (le_id_r (uab34_pmetric x z)
           (@plus Rb (@plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z)))
                     (@plus Rb (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z))))
           (@plus Rb (uab34_pmetric x y) (uab34_pmetric y z))
           (uab34_plus_swap (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z))
                            (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z)))
           (le_plus_compat (@metric Rb (fst x) (fst z))
             (@plus Rb (@metric Rb (fst x) (fst y)) (@metric Rb (fst y) (fst z)))
             (@metric Rb (snd x) (snd z))
             (@plus Rb (@metric Rb (snd x) (snd y)) (@metric Rb (snd y) (snd z)))
             (@metric_triangle Rb (fst x) (fst y) (fst z))
             (@metric_triangle Rb (snd x) (snd y) (snd z)))).
Qed.

(* ---- 双收敛面：clim_unique 与柯西完备（双分量拆装） ---- *)
Lemma uab34_pclim_unique : forall (u : nat -> RR) (l1 l2 : RR),
  uab34_pclim u l1 -> uab34_pclim u l2 -> Id l1 l2.
Proof.
  intros u [a1 b1].
  intros [a2 b2].
  intros H1 H2.
  exact (uab34_pair_id
          (@lim_unique Rb (fun n => fst (u n)) a1 a2 (fst H1) (fst H2))
          (@lim_unique Rb (fun n => snd (u n)) b1 b2 (snd H1) (snd H2))).
Qed.

Lemma uab34_pcauchy_complete : forall (u : nat -> RR),
  (forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
     sigT (fun N : nat => forall m n : nat,
       NatLe N m -> NatLe N n ->
       @lt Rb (uab34_pmetric (u m) (u n)) eps)) ->
  sigT (fun l : RR => uab34_pclim u l).
Proof.
  intros u Hc.
  assert (Hf : forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      @lt Rb (@metric Rb (fst (u m)) (fst (u n))) eps)).
  { intros eps Heps. destruct (Hc eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    exact (le_lt_trans (@metric Rb (fst (u m)) (fst (u n)))
                       (uab34_pmetric (u m) (u n)) eps
            (uab34_metric_le_l (u m) (u n)) (HN m n Hm Hn)). }
  assert (Hs : forall eps : @R Rb, @lt Rb (@zero Rb) eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      @lt Rb (@metric Rb (snd (u m)) (snd (u n))) eps)).
  { intros eps Heps. destruct (Hc eps Heps) as [N HN].
    exists N. intros m n Hm Hn.
    exact (le_lt_trans (@metric Rb (snd (u m)) (snd (u n)))
                       (uab34_pmetric (u m) (u n)) eps
            (uab34_metric_le_r (u m) (u n)) (HN m n Hm Hn)). }
  destruct (@cauchy_complete Rb (fun n => fst (u n)) Hf) as [a1 p1].
  destruct (@cauchy_complete Rb (fun n => snd (u n)) Hs) as [b1 p2].
  exists (a1, b1). exact (p1, p2).
Qed.

(* ---- 实例本体：21 字段全构造（StateSpace 类第二满律实例） ---- *)
Instance uab34_prodRR : StateSpace Rb := {|
  S := RR;
  szero := uab34_pzero;
  splus := uab34_psplus;
  smult := uab34_psmult;
  sopp := uab34_psopp;
  splus_assoc := uab34_pplus_assoc;
  splus_comm := uab34_pplus_comm;
  splus_zero := uab34_pplus_zero;
  splus_opp := uab34_pplus_opp;
  smult_one := uab34_psmult_one;
  smult_assoc := uab34_psmult_assoc;
  smult_distrib_r := uab34_psmult_distrib_r;
  smult_distrib_l := uab34_psmult_distrib_l;
  smetric := uab34_pmetric;
  smetric_sym := uab34_pmetric_sym;
  smetric_pos := uab34_pmetric_pos;
  smetric_zero := uab34_pmetric_zero;
  smetric_triangle := uab34_pmetric_triangle;
  clim := uab34_pclim;
  clim_unique := uab34_pclim_unique;
  cauchy_complete_S := uab34_pcauchy_complete
|}.

(* ============================================================ *)
(* §二 非平凡性三钉：三态 (0,0)/(1,0)/(0,1) 两两非 Id             *)
(* ============================================================ *)
(*   路线：投影分解出 Id zero one，与 one_pos（lt zero one）+     *)
(*   lt_id_l 合成 lt one one，撞 lt_irrefl 反证。                 *)

(* ---- 积对分量提取（保族）：ML-Id 族带型索引，分量 Id 须留在分量族 ---- *)
Definition uab34_pair_inj_l {A B : Set} {x x' : A} {y y' : B}
  (p : Id (pair x y) (pair x' y')) : Id x x' := id_cong (@fst A B) p.

Definition uab34_pair_inj_r {A B : Set} {x x' : A} {y y' : B}
  (p : Id (pair x y) (pair x' y')) : Id y y' := id_cong (@snd A B) p.

Lemma uab34_three_state_ne_01 :
  Not (Id (@pair (@R Rb) (@R Rb) (@zero Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@one Rb) (@zero Rb))).
Proof.
  intros H.
  apply (@lt_irrefl Rb (@one Rb)).
  exact (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb)
           (id_sym (uab34_pair_inj_l H)) one_pos).
Qed.

Lemma uab34_three_state_ne_02 :
  Not (Id (@pair (@R Rb) (@R Rb) (@zero Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@zero Rb) (@one Rb))).
Proof.
  intros H. exact (@lt_irrefl Rb (@one Rb) (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb) (id_sym (uab34_pair_inj_r H)) one_pos)).
Qed.

Lemma uab34_three_state_ne_12 :
  Not (Id (@pair (@R Rb) (@R Rb) (@one Rb) (@zero Rb))
          (@pair (@R Rb) (@R Rb) (@zero Rb) (@one Rb))).
Proof.
  intros H. exact (@lt_irrefl Rb (@one Rb) (@lt_id_l Rb (@one Rb) (@zero Rb) (@one Rb) (uab34_pair_inj_l H) one_pos)).
Qed.

End ProdRR.

(* ============================================================ *)
(* §三 有限载体不可能性（形式化落账）：逐点平方律载体必退化单点    *)
(* ============================================================ *)
(*   对任意抽象 StateSpace（任意 RIE 参数位），若载体满足逐点平方律    *)
(*   x+x==0，则标量作用经 fourR=1+1+1+1 的正逆除法四折叠合，      *)
(*   smult_one 迫每个载体元素 Id szero——bool×bool/枚举类有限      *)
(*   载体满律路线由此定理数学关闭，非平凡实例必须取无穷载体。      *)

Section FiniteCollapse.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Let Rb := @RI_base RIE.
Let fourR : @R Rb :=
  @plus Rb (@plus Rb (@one Rb) (@one Rb)) (@plus Rb (@one Rb) (@one Rb)).

Variable SSc : StateSpace Rb.
Hypothesis Hexp2 : forall y : @S Rb SSc, Id (@splus Rb SSc y y) (@szero Rb SSc).

Lemma uab34_four_pos : @lt Rb (@zero Rb) fourR.
Proof.
  assert (Htw : @lt Rb (@zero Rb) (@plus Rb (@one Rb) (@one Rb))).
  { exact (@lt_id_l Rb (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb))
            (@plus Rb (@one Rb) (@one Rb))
            (id_sym (@plus_zero Rb (@zero Rb)))
            (@lt_plus_compat RIE (@zero Rb) (@one Rb) (@zero Rb) (@one Rb)
                              (@one_pos RIE) (@one_pos RIE))). }
  exact (@lt_id_l Rb (@zero Rb) (@plus Rb (@zero Rb) (@zero Rb)) fourR
          (id_sym (@plus_zero Rb (@zero Rb)))
          (@lt_plus_compat RIE (@zero Rb) (@plus Rb (@one Rb) (@one Rb))
                              (@zero Rb) (@plus Rb (@one Rb) (@one Rb))
                              Htw Htw)).
Qed.

(* 标量除法：fourR · (a·inv fourR) == a（对任意实标量 a） *)
Lemma uab34_scalar_div (a : @R Rb) :
  Id (@mult Rb fourR (@mult Rb a (@inv_pos Rb fourR uab34_four_pos))) a.
Proof.
  exact (id_trans (@mult_assoc Rb fourR a (@inv_pos Rb fourR uab34_four_pos))
    (id_trans (id_cong (fun t => @mult Rb t (@inv_pos Rb fourR uab34_four_pos))
                       (@mult_comm Rb fourR a))
      (id_trans (id_sym (@mult_assoc Rb a fourR (@inv_pos Rb fourR uab34_four_pos)))
        (id_trans (id_cong (fun t => @mult Rb a t)
                           (@inv_pos_correct Rb fourR uab34_four_pos))
                  (@mult_one Rb a))))).
Qed.

(* 作用塌缩：任意标量的作用把任意载体元素送至 szero *)
Lemma uab34_action_null :
  forall (a : @R Rb) (y : @S Rb SSc),
    Id (@smult Rb SSc a y) (@szero Rb SSc).
Proof.
  intros a y.
  set (i4 := @inv_pos Rb fourR uab34_four_pos).
  set (c := @mult Rb a i4).
  set (cy := @smult Rb SSc c y).
  set (twR := @plus Rb (@one Rb) (@one Rb)).
  (* H1：标量 a 换成 fourR·c（c := a·inv fourR） *)
  assert (H1 : Id (@smult Rb SSc a y) (@smult Rb SSc (@mult Rb fourR c) y)).
  { exact (id_cong (fun t => @smult Rb SSc t y)
                   (id_sym (uab34_scalar_div a))). }
  (* H2：mult fourR c == mult twR c + mult twR c（distrib，fourR≡twR+twR） *)
  assert (H2 : Id (@mult Rb fourR c)
                  (@plus Rb (@mult Rb twR c) (@mult Rb twR c))).
  { exact (@uab34_mult_distrib_l RIE twR twR c). }
  (* H3：单肢 smult (mult twR c) y == cy+cy（distrib+分配_l+左幺） *)
  assert (H3 : Id (@smult Rb SSc (@mult Rb twR c) y)
                  (@splus Rb SSc cy cy)).
  { exact (id_trans
             (id_cong (fun t => @smult Rb SSc t y)
                       (@uab34_mult_distrib_l RIE (@one Rb) (@one Rb) c))
             (id_trans (@smult_distrib_l Rb SSc (@mult Rb (@one Rb) c)
                                         (@mult Rb (@one Rb) c) y)
               (id_trans
                  (id_cong (fun t => @splus Rb SSc t
                                              (@smult Rb SSc (@mult Rb (@one Rb) c) y))
                           (id_cong (fun t => @smult Rb SSc t y)
                                    (id_trans (@mult_comm Rb (@one Rb) c)
                                              (@mult_one Rb c))))
                  (id_cong (fun t => @splus Rb SSc cy t)
                           (id_cong (fun t => @smult Rb SSc t y)
                                    (id_trans (@mult_comm Rb (@one Rb) c)
                                              (@mult_one Rb c))))))). }
  (* H4：smult (mult fourR c) y == (cy+cy)+(cy+cy)（H2 装配+分配_l+H3 双肢） *)
  assert (H4 : Id (@smult Rb SSc (@mult Rb fourR c) y)
                  (@splus Rb SSc (@splus Rb SSc cy cy) (@splus Rb SSc cy cy))).
  { exact (id_trans (id_cong (fun t => @smult Rb SSc t y) H2)
            (id_trans (@smult_distrib_l Rb SSc (@mult Rb twR c) (@mult Rb twR c) y)
              (id_trans
                 (id_cong (fun t => @splus Rb SSc t
                                              (@smult Rb SSc (@mult Rb twR c) y)) H3)
                 (id_cong (fun t => @splus Rb SSc (@splus Rb SSc cy cy) t)
                           H3)))). }
  (* H5：(cy+cy)+(cy+cy) == szero（逐点平方律双用+零幺） *)
  assert (H5 : Id (@splus Rb SSc (@splus Rb SSc cy cy) (@splus Rb SSc cy cy))
                  (@szero Rb SSc)).
  { exact (id_trans
             (id_cong (fun t => @splus Rb SSc t (@splus Rb SSc cy cy)) (Hexp2 cy))
             (id_trans
                (id_cong (fun t => @splus Rb SSc (@szero Rb SSc) t) (Hexp2 cy))
                (@splus_zero Rb SSc (@szero Rb SSc)))). }
  exact (id_trans H1 (id_trans H4 H5)).
Qed.

Theorem uab34_finite_collapse : forall y : @S Rb SSc, Id y (@szero Rb SSc).
Proof.
  intros y.
  exact (id_trans (id_sym (@smult_one Rb SSc y))
                  (uab34_action_null (@one Rb) y)).
Qed.

End FiniteCollapse.

(* ============================================================ *)
(* §四 一锚定理实例面：上游 StateSpace 依存件在本载体上的兑现      *)
(* ============================================================ *)
(*   IdSlotTranslate 节（Context {RI}{SS} 依存 StateSpace，无     *)
(*   SumOver 前提）之求和参数位翻译件/宿主核销定理在 R×R 载体上实例化。*)

Section Anchor.

Context {RIE : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

(* 参数位装配面：求和参数位（list 折叠机）与翻译机在本载体上恒等 *)
Theorem uab34_idt_sum_eq_list_prodRR :
  forall (enum : list (@S (@RI_base RIE) uab34_prodRR))
         (g : @S (@RI_base RIE) uab34_prodRR -> @R (@RI_base RIE)),
    Id (@IdSlotTranslate.idt_sumf RIE uab34_prodRR enum g)
       (@IdSlotTranslate.idt_list_sum RIE uab34_prodRR g enum).
Proof.
  intros enum g.
  exact (@IdSlotTranslate.idt_sum_eq_list RIE uab34_prodRR enum g).
Qed.

(* 一锚定理：idt_slot_g01（宿主 AttnDoeblin.bs_list_sum 真机核销）
   在本实例上的实例面——上游 StateSpace 依存定理首次在本载体实例化消解 *)
Theorem uab34_idt_slot_g01_prodRR :
  forall (enum : list (@S (@RI_base RIE) uab34_prodRR))
         (g : @S (@RI_base RIE) uab34_prodRR -> @R (@RI_base RIE)),
    Id (@IdSlotTranslate.idt_sumf RIE uab34_prodRR enum g)
       (@AttnDoeblin.bs_list_sum RIE uab34_prodRR g enum).
Proof.
  intros enum g.
  exact (@IdSlotTranslate.idt_slot_g01 RIE uab34_prodRR enum g).
Qed.

End Anchor.

(* ============================================================ *)
(* §五 G4 证据：五件全 Closed 留痕                                *)
(* ============================================================ *)
Print Assumptions uab34_three_state_ne_01.
Print Assumptions uab34_pclim_unique.
Print Assumptions uab34_finite_collapse.
Print Assumptions uab34_idt_sum_eq_list_prodRR.
Print Assumptions uab34_idt_slot_g01_prodRR.
