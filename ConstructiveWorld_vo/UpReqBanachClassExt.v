(* ============================================================ *)
(* ToyR 玩具证替换件 —— T268 台账席 战役包AC（tier2 末段第一批）      *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性收口，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bxce_binom_merge（原 L176，3 句轻证）	*)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBanachClassExt.v —— 席BCE：BanachAlg 类扩字段原型席        *)
(* （20260913，路径 B；冻结类禁改，扩展只在自有前缀文件内）          *)
(* ============================================================ *)
(* 使命：为冻结类 BanachAlg（UpReqBanachExp.v）缺「Q 加法同调入     *)
(*   bcoef」与「Qeq 同调入 bcoef」两字段做原型验证与设计单。         *)
(*   上游挂账：席 BA（UpReqBanachAdd.v）bpow_add 主件带 hplus/hwd   *)
(*   显式假设（其挂账①「类扩字段后假设即消」）；席 B25 exp(0) 等。   *)
(* 20260913 二波（席UNQ）：反可分性字段 bxce_sep 落地——               *)
(*   「范数任意小 ⟹ bae 零」，B25 挂账 exp(0) 等式面与极限唯一性      *)
(*   的共同钥匙；消费件 UpReqBanachLimUniq.v（bxuq_lim_uniq）。      *)
(* 本件承载：                                                      *)
(*   S1 = Class BanachAlgExt（扩展类：底类 + 三新字段，前两形状与     *)
(*        BA 件 hplus/hwd 假设逐字对齐，bxce_hplus_shape/           *)
(*        bxce_hwd_shape 定义形机器验证；第三字段 bxce_sep 见下）；   *)
(*   S2 = bxce_mk 迁移桥（任意 BanachAlg + 两系数引理 → Ext 实例，  *)
(*        波次落地后实例侧迁移的两步作业面）；                       *)
(*   S3 = 消解演示四件（bpa_scal_plus/bpa_pair_mid/bpa_pair_tail    *)
(*        同型引理在 Ext 类下无显式假设重证，四关绿）。              *)
(* 红线自审：                                                      *)
(*   - 语句面全 Set 层：返回型只 bae/Id；bxce_coef_wd 的 Qeq 前提    *)
(*     承袭 BA 件 hwd 假设原形（显式假设面既有形，非新增泄露）；      *)
(*   - 纯构造性：vernac 禁用面零命中、零经典逻辑；                   *)
(*   - 冻结类未动一字：本件只 Require UpReqBanachExp。              *)
(* 设计单（裁决）：完备性字段 bcauchy_complete 为无前提字段 ⟹ Q 载体  *)
(*   不可满足（有理柯西列极限非构造可得）⟹ 具体实例须完备载体，       *)
(*   归上游实例席（B25 卡「实例化席未启动」印证）；本件以 bxce_mk     *)
(*   桥 + 形状机器验证承担原型可行性，实例破坏面为零（见交付报告）。  *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1：Class BanachAlgExt —— 冻结类 BanachAlg 的扩展（禁改原类）    *)
(* 两新字段形状与 UpReqBanachAdd.v 显式假设逐字对齐：                *)
(*   hplus := forall q r, bae (bplus (bcoef q) (bcoef r))          *)
(*                            (bcoef (q + r))                      *)
(*   hwd   := forall q r, q == r -> bae (bcoef q) (bcoef r)        *)
(* 工程注：类投影实例参为隐式（PB 卡），字段引用一律 @显式喂实例。    *)
(* ============================================================ *)

Class BanachAlgExt := {
  bxce_base : BanachAlg;

  (* 新字段一：Q 加法同调入 bcoef（消 hplus） *)
  bxce_coef_plus : forall q r : Q,
    @bae bxce_base (@bplus bxce_base (@bcoef bxce_base q)
                                    (@bcoef bxce_base r))
                   (@bcoef bxce_base (q + r)%Q);

  (* 新字段二：Qeq 同调入 bcoef（消 hwd） *)
  bxce_coef_wd : forall q r : Q,
    q == r -> @bae bxce_base (@bcoef bxce_base q) (@bcoef bxce_base r);

  (* 新字段三（二波，席UNQ 落地）：反可分性——范数小于任意 eps ⟹ bae 零。
     签名与 BCE 报告设计单①草案逐字一致；全 Set 层（QltT : Q->Q->Set，
     S02 L26），无 Prop 前提面。消费件：UpReqBanachLimUniq.v。 *)
  bxce_sep : forall a : (@BA bxce_base),
    (forall eps : Q, QltT 0 eps -> QltT (@bnorm bxce_base a) eps) ->
    @bae bxce_base a (@bzero bxce_base)
}.

(* 形状机器验证：字段形 = BA 件显式假设形（逐字对齐，类型即证明） *)
Definition bxce_hplus_shape (E : BanachAlgExt) (q r : Q) :
  @bae (@bxce_base E) (@bplus (@bxce_base E) (@bcoef (@bxce_base E) q)
                                          (@bcoef (@bxce_base E) r))
       (@bcoef (@bxce_base E) (q + r)%Q)
  := @bxce_coef_plus E q r.

Definition bxce_hwd_shape (E : BanachAlgExt) (q r : Q) :
  q == r -> @bae (@bxce_base E) (@bcoef (@bxce_base E) q)
                                (@bcoef (@bxce_base E) r)
  := @bxce_coef_wd E q r.

(* 反可分性字段形状机器验证（同款：定义形即类型证明） *)
Definition bxce_sep_shape (E : BanachAlgExt) (a : (@BA (@bxce_base E))) :
  (forall eps : Q, QltT 0 eps -> QltT (@bnorm (@bxce_base E) a) eps) ->
  @bae (@bxce_base E) a (@bzero (@bxce_base E))
  := @bxce_sep E a.

(* 范数零推论：Id (bnorm a) 0 ⟹ bae a 0（B25 挂账「范数零⟹相等」直取形） *)
Lemma bxce_sep_norm0 : forall (E : BanachAlgExt) (a : (@BA (@bxce_base E))),
  Id (@bnorm (@bxce_base E) a) 0%Q ->
  @bae (@bxce_base E) a (@bzero (@bxce_base E)).
Proof.
  intros E a H.
  apply (@bxce_sep E a).
  intros eps Heps.
  rewrite H.
  exact Heps.
Qed.

(* ============================================================ *)
(* S2：bxce_mk 迁移桥 —— 实例侧两步迁移作业面                       *)
(* 任意 BanachAlg 模型 + 系数两引理 + 反可分性定理 ⟹ Ext 实例。      *)
(* 二波注：bxce_sep 字段落地后本桥扩为三引理形（签名扩参，           *)
(* 旧两参调用点随字段义务一并补喂——现库调用点为零，破坏面 ∅）。       *)
(* ============================================================ *)

Definition bxce_mk (B : BanachAlg)
  (hp : forall q r : Q,
    @bae B (@bplus B (@bcoef B q) (@bcoef B r)) (@bcoef B (q + r)%Q))
  (hw : forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r))
  (sp : forall a : (@BA B),
    (forall eps : Q, QltT 0 eps -> QltT (@bnorm B a) eps) ->
    @bae B a (@bzero B)) :
  BanachAlgExt
:= {| bxce_base := B; bxce_coef_plus := hp; bxce_coef_wd := hw;
      bxce_sep := sp |}.

(* ============================================================ *)
(* S3：消解演示 —— BA 件显式假设同型引理在 Ext 类下无假设重证          *)
(* 判据：以下四件无 hplus/hwd 字样假设（Print Assumptions Closed）。  *)
(* ============================================================ *)

(* 演示一：bpa_scal_plus 镜像（原版带 hplus 显式假设）
   bcoef q·T + bcoef r·T == bcoef (q+r)·T —— Ext 类下零假设。 *)
Lemma bxce_scal_plus : forall (E : BanachAlgExt) (q r : Q)
    (T : @BA (@bxce_base E)),
  @bae (@bxce_base E)
    (@bplus (@bxce_base E)
       (@bmult (@bxce_base E) (@bcoef (@bxce_base E) q) T)
       (@bmult (@bxce_base E) (@bcoef (@bxce_base E) r) T))
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) (q + r)%Q) T).
Proof.
  intros E q r T.
  eapply bae_trans.
  - apply (@bae_sym (@bxce_base E)).
    exact (@bdistrib_r (@bxce_base E) (@bcoef (@bxce_base E) q)
                        (@bcoef (@bxce_base E) r) T).
  - apply (@bmult_wd (@bxce_base E)
             (@bplus (@bxce_base E) (@bcoef (@bxce_base E) q)
                                    (@bcoef (@bxce_base E) r)) T
             (@bcoef (@bxce_base E) (q + r)%Q) T).
    + exact (@bxce_coef_plus E q r).
    + apply (@bae_refl (@bxce_base E)).
Qed.

(* 演示二：hwd 在乘法语境的下拉（bpa_pair_tail 核心步镜像，原版带 hwd）
   q == r ⟹ bcoef q·X == bcoef r·X —— Ext 类下零假设。 *)
Lemma bxce_mult_coef_wd : forall (E : BanachAlgExt) (q r : Q)
    (X : @BA (@bxce_base E)),
  q == r ->
  @bae (@bxce_base E)
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) q) X)
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) r) X).
Proof.
  intros E q r X H.
  apply (@bmult_wd (@bxce_base E)
           (@bcoef (@bxce_base E) q) X
           (@bcoef (@bxce_base E) r) X).
  - exact (@bxce_coef_wd E q r H).
  - apply (@bae_refl (@bxce_base E)).
Qed.

(* 演示三：bpa_pair_tail 出界收拢形镜像（原版带 hwd + Qplus_0_r）
   c2 == 0 ⟹ bcoef (c1+c2)·Y == bcoef c1·Y —— Ext 类下零假设。 *)
Lemma bxce_pair_tail_shape : forall (E : BanachAlgExt) (c1 c2 : Q)
    (Y : @BA (@bxce_base E)),
  c2 == 0%Q ->
  @bae (@bxce_base E)
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) (c1 + c2)%Q) Y)
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) c1) Y).
Proof.
  intros E c1 c2 Y H2.
  apply (@bmult_wd (@bxce_base E)
           (@bcoef (@bxce_base E) (c1 + c2)%Q) Y
           (@bcoef (@bxce_base E) c1) Y).
  - apply (@bxce_coef_wd E (c1 + c2)%Q c1).
    setoid_rewrite H2.
    apply Qplus_0_r.
  - apply (@bae_refl (@bxce_base E)).
Qed.

(* 演示四：bpa_pair_mid 消费形完整镜像（系数 Pascal 合并进标量载体）
   bcoef (c+d)·Z == bcoef c·Z + bcoef d·Z —— 演示一之对称直接系。 *)
Lemma bxce_binom_merge : forall (E : BanachAlgExt) (c d : Q)
    (Z : @BA (@bxce_base E)),
  @bae (@bxce_base E)
    (@bmult (@bxce_base E) (@bcoef (@bxce_base E) (c + d)%Q) Z)
    (@bplus (@bxce_base E)
       (@bmult (@bxce_base E) (@bcoef (@bxce_base E) c) Z)
       (@bmult (@bxce_base E) (@bcoef (@bxce_base E) d) Z)).
Proof.
  intros E c d Z.
  apply (@bae_sym (@bxce_base E)).
  exact (bxce_scal_plus E c d Z).
Qed.

(* ============================================================ *)
(* 尾注（迁移方案与风险账见 attn/_tbce_交付报告-20260913.md）：       *)
(*   - 正式迁移：改 UpReqBanachExp.v 类声明补两字段 → 实例补字段     *)
(*     （或经 bxce_mk 两步）→ 下游 UpReqBanachAdd.v 18 件摘除        *)
(*   hplus/hwd 携带（bpa_scal_plus/bpa_pair_mid/bpa_pair_tail/       *)
(*   bpa_bpow_add/bpa_esp_term_binom/bpa_esp_binom 及其消费链）。    *)
(*   - 反可分性字段（B25 挂账）：**已落地（20260913 二波，席UNQ）**，    *)
(*     签名 bxce_sep : forall a, (forall eps, QltT 0 eps ->           *)
(*                QltT (bnorm a) eps) -> bae a bzero；形状机器验证     *)
(*     bxce_sep_shape + 范数零直取形 bxce_sep_norm0；极限唯一性        *)
(*     消费件见 UpReqBanachLimUniq.v（bxuq_lim_uniq）。               *)
(* ============================================================ *)

(* ---- ToyR 追印：清单件假设面逐件打印，判读全闭 ---- *)
Print Assumptions bxce_binom_merge.
