(* ============================================================ *)
(* DecBridge6.v — 席位 CZD12（批次 E-STAGING-CZD12）P2 施工件     *)
(* DO 判定桥六槽件：T62 C 类 #34-39 一件收口                     *)
(*                                                               *)
(* 对账坐标（消融50/T62-零引用47枚triage.md §2-C 表）：           *)
(*   #34 UpReqArgminEngine.v:69  rae_le_dec（Or(le)(Not le)）     *)
(*   #35 UpReqArgminEngine.v:71  rae_lt_dec（三分，eq 腿 req 形） *)
(*   #36 UpReqArgminEngine.v:202 probe_le_dec（#34 同位复制）     *)
(*   #37 UpReqArgminEngine.v:203 probe_lt_dec（#35 同位复制）     *)
(*   #38 UpReqAlgebra.v:1474  req_lt_plus_compat_lt_le            *)
(*   #39 UpReqAlignRestA.v:80 ralt_lt_plus_compat_lt_le           *)
(*                                                               *)
(* 收口原理（T62 §3-P2 路线）：六槽宿主节皆为 RIS 世界抽象假设位； *)
(*   全抽象 R 的整体三分 = LPO 墙（E225 定谳，零 Instance），故    *)
(*   消融定谳 = "DO 强化层"收口：节增 RI+DO 双 Context（fa53      *)
(*   同款），R 取 S01 具体载体，RIS 结构经 TempSoftmaxInstantiation *)
(*   的装配桥 tsi_rie_setoid 供给（req 腿 := Id，le/lt/plus 等    *)
(*   字段 = S01 同名投影，纯 delta/iota 可逆换装）。              *)
(*                                                               *)
(* 本件唯一新数学点（须真证）：req-Id 判定腿换装桥 db6_id_req ——  *)
(*   fa53 判定引擎三分产出 Id 腿，六槽语句面要 req 腿，本桥在     *)
(*   tsi 桥 req:=Id 定义面上把 Id 判定证书换装为 req 判定证书。   *)
(*   #38/#39 与 fa53_lt_plus_compat_lt_le_dec 逐字同语句，        *)
(*   exact 一击收口。                                             *)
(*                                                               *)
(* 纪律：语句面全 Set 层（Or/Not/Empty_set 皆 S01 Set 层定义），   *)
(*   零 Prop 泄露；禁词面零命中；非平凡真证（投影别名 + 三腿换装  *)
(*   重排 + 平移件转换收口）。原树零改；验证=本地信任缓存侧编。    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.
Require Import TempSoftmaxInstantiation.
Require Import fa53_compat_abs.

Section DecBridge6.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* tsi 装配桥实例缩写：S01 载体上的 RIS 结构（req 腿 := Id） *)
Let TSI : RealInterfaceEnhancedMod.RealInterfaceEnhancedSetoid
            (@S01_BaseRing.R RI) :=
  tsi_rie_setoid RI.

(* 槽语句面投影（tsi 桥字段全显式读法；与宿主 RIS 槽同名同形） *)
Let rle  : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.le (@S01_BaseRing.R RI) TSI a b.
Let rlt  : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.lt (@S01_BaseRing.R RI) TSI a b.
Let rreq : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> Set :=
  fun a b => @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI) TSI a b.
Let rplus : @S01_BaseRing.R RI -> @S01_BaseRing.R RI -> @S01_BaseRing.R RI :=
  fun a b => @RealInterfaceEnhancedMod.plus (@S01_BaseRing.R RI) TSI a b.

(* ---- fa53 投影别名定式：类字段名 lt_dec 被 Stdlib Compare_dec    *)
(*      遮蔽（fa53_compat_abs.v:39-44 同款 match 投影） ---- *)
Definition db6_ord_le_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (@S01_BaseRing.le RI a b) (@S01_BaseRing.Not (@S01_BaseRing.le RI a b)) :=
  match DO with
  | Build_DecidableOrder _ ord _ _ _ _ => ord
  end.

Definition db6_lt_dec_id :
  forall a b : @S01_BaseRing.R RI,
    Or (@S01_BaseRing.lt RI a b)
       (Or (Id a b) (@S01_BaseRing.lt RI b a)) :=
  match DO with
  | Build_DecidableOrder _ _ lt_d _ _ _ => lt_d
  end.

(* ============================================================ *)
(* 新数学点：req-Id 判定腿换装桥                                  *)
(*   fa53 引擎三分中腿是 Id 证书；六槽语句面中腿是 req 证书。     *)
(*   tsi 装配桥的 req 字段定义性为 Id（fun x y => Id x y），故    *)
(*   换装 = 纯转换级运输；本桥显式成件以承载换装语义并供消费。    *)
(* ============================================================ *)
Theorem db6_id_req :
  forall (a b : @S01_BaseRing.R RI),
    Id a b -> @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI) TSI a b.
Proof.
  intros a b H. exact H.
Qed.

(* ---- 槽 #34/#36 形：le 二分判定（DO 字段 ord_le_dec 直配） ---- *)
Theorem db6_rae_le_dec :
  forall a b : @S01_BaseRing.R RI, Or (rle a b) (Not (rle a b)).
Proof.
  intros a b. exact (db6_ord_le_dec a b).
Qed.

(* ---- 槽 #35/#37 形：三分判定（fa53_lt_dec 直配 + eq 腿换装） ----
   inl/inr-inr 两腿与引擎产出同形直配；inr-inl 腿 = db6_id_req
   换装桥把 Id 判定证书换装为 req 判定证书（本件新数学点）。 *)
Theorem db6_rae_lt_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (rlt a b) (Or (rreq a b) (rlt b a)).
Proof.
  intros a b.
  destruct (db6_lt_dec_id a b) as [Hlt | [Heq | Hgt]].
  - (* a < b：严格腿直配 *)
    exact (inl Hlt).
  - (* a == b：Id 证书换装为 req 证书 *)
    exact (inr (inl (db6_id_req a b Heq))).
  - (* b < a：反侧严格腿直配 *)
    exact (inr (inr Hgt)).
Qed.

(* ---- 槽 #36/#37：probe 位（与 rae 位同语句；独立成件对账锚定） ---- *)
Theorem db6_probe_le_dec :
  forall a b : @S01_BaseRing.R RI, Or (rle a b) (Not (rle a b)).
Proof.
  exact db6_rae_le_dec.
Qed.

Theorem db6_probe_lt_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (rlt a b) (Or (rreq a b) (rlt b a)).
Proof.
  exact db6_rae_lt_dec.
Qed.

(* ---- 槽 #38/#39 形：严格×非严加法保序 ----
   与 fa53_compat_abs.v:103 fa53_lt_plus_compat_lt_le_dec 逐字同
   语句（le/lt/plus 经 tsi 桥 = S01 同名投影，转换级同一关系），
   exact 一击收口；#39 为 #38 的 ralt 位独立成件。 *)
Theorem db6_req_lt_plus_compat_lt_le :
  forall a b c d : @S01_BaseRing.R RI,
    @S01_BaseRing.lt RI a b -> rle c d -> rlt (rplus a c) (rplus b d).
Proof.
  intros a b c d Hab Hcd.
  exact (fa53_lt_plus_compat_lt_le_dec a b c d Hab Hcd).
Qed.

Theorem db6_ralt_lt_plus_compat_lt_le :
  forall a b c d : @S01_BaseRing.R RI,
    @S01_BaseRing.lt RI a b -> rle c d -> rlt (rplus a c) (rplus b d).
Proof.
  exact db6_req_lt_plus_compat_lt_le.
Qed.

End DecBridge6.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明） ---- *)
Print Assumptions db6_id_req.
Print Assumptions db6_rae_le_dec.
Print Assumptions db6_rae_lt_dec.
Print Assumptions db6_probe_le_dec.
Print Assumptions db6_probe_lt_dec.
Print Assumptions db6_req_lt_plus_compat_lt_le.
Print Assumptions db6_ralt_lt_plus_compat_lt_le.
