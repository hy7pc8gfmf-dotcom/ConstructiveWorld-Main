(* ============================================================
   DecBridge6.v — fa53 判定引擎证书到六槽语句面的桥接件。
   使命：fa53 判定引擎三分产出 Id 分支，六槽语句面要 req 分支——
         本件在 tsi 桥 req:=Id 定义面上给出 Id 判定证书到 req
         判定证书的转换桥 db6_id_req（本件新数学点），并提供
         le 二分判定／三分判定／加法保序的对应位形件（#34-#39
         位形）。全抽象 R 的整体三分在纯构造性下不可得，
         故取 DO 强化层路径：节增 RI+DO 双 Context（fa53 同款），
         R 取 S01 具体实例，RIS 结构经 TempSoftmaxInstantiation
         的装配桥 tsi_rie_setoid 供给（req 分支 := Id，le/lt/plus
         等字段 = S01 同名投影，纯 delta/iota 可逆转换）。
   依赖：S01_BaseRing / S07_RealSetoidExpLog /
         TempSoftmaxInstantiation / fa53_compat_abs。
   对标：UpReqArgminEngine.v:69-203（rae_le_dec/rae_lt_dec/
         probe_le_dec/probe_lt_dec）；UpReqAlgebra.v:1474
         req_lt_plus_compat_lt_le；UpReqAlignRestA.v:80
         ralt_lt_plus_compat_lt_le。
   构造性：语句面全 Set 层（Or/Not/Empty_set 皆 S01 Set 层
         定义），零 Prop 泄露；非平凡真证（投影别名 + 三支
         转换重排 + 平移件转换闭合）。
   编译配方：coqc -native-compiler no -q -Q . ""。
   ============================================================ *)

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
(* 新数学点：req-Id 判定腿转换桥                                  *)
(*   fa53 引擎三分中腿是 Id 证书；六槽语句面中腿是 req 证书。     *)
(*   tsi 装配桥的 req 字段定义性为 Id（fun x y => Id x y），故    *)
(*   转换 = 纯转换级运输；本桥显式成件以承载转换语义并供使用。    *)
(* ============================================================ *)
Theorem db6_id_req :
  forall (a b : @S01_BaseRing.R RI),
    Id a b -> @RealInterfaceEnhancedMod.req (@S01_BaseRing.R RI) TSI a b.
Proof.
  intros a b H. exact H.
Qed.

(* ---- 槽 #34/#36 形：le 二分判定（DO 字段 ord_le_dec 直接给出） ---- *)
Theorem db6_rae_le_dec :
  forall a b : @S01_BaseRing.R RI, Or (rle a b) (Not (rle a b)).
Proof.
  intros a b. exact (db6_ord_le_dec a b).
Qed.

(* ---- 槽 #35/#37 形：三分判定（fa53_lt_dec 直接给出 + eq 腿转换） ----
   inl/inr-inr 两支与引擎产出同形直接给出；inr-inl 腿 = db6_id_req
   转换桥把 Id 判定证书转换为 req 判定证书（本件新数学点）。 *)
Theorem db6_rae_lt_dec :
  forall a b : @S01_BaseRing.R RI,
    Or (rlt a b) (Or (rreq a b) (rlt b a)).
Proof.
  intros a b.
  destruct (db6_lt_dec_id a b) as [Hlt | [Heq | Hgt]].
  - (* a < b：严格腿直接给出 *)
    exact (inl Hlt).
  - (* a == b：Id 证书转换为 req 证书 *)
    exact (inr (inl (db6_id_req a b Heq))).
  - (* b < a：反侧严格腿直接给出 *)
    exact (inr (inr Hgt)).
Qed.

(* ---- 槽 #36/#37：probe 位（与 rae 位同语句；独立成件互核） ---- *)
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
   exact 一击闭合；#39 为 #38 的 ralt 位独立成件。 *)
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
