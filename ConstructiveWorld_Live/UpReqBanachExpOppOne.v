(* ============================================================ *)
(* UpReqBanachExpOppOne.v —— 席EQV：路径 B S4 等式形收口席        *)
(* （20260913；后台独立席位，独占 CoreN 0）                       *)
(* ============================================================ *)
(* 使命：e^a · e^(−a) == e^0 的 bae 等式收口（S4 可逆性最后一块）。 *)
(*                                                             *)
(* 总装接线图（①→④，与任务书四步一一对位）：                    *)
(*   ① BASM  bxadd_esp_prod_blim（已落 .vo）：                  *)
(*        blim (fun n => esp a n · esp(−a) n) (e^a·e^(−a))      *)
(*      ——序列左极限，纯消费，零新证。                           *)
(*   ② CD3  bxcd_prod_near_one（闸门件，UpReqBanachCauchy.vo）：  *)
(*        ∀q>0 ∃N ∀n≥N, ‖esp a n·esp(−a) n − bone‖<q            *)
(*      ——经 bxoo_nearone_blim 换骨即 blim (同一序列) bone。     *)
(*      闸门未开时本件不硬攻其一般 ε-链（纪律：禁重写 CD3），     *)
(*      将其以 Set 面显式假设槽位（blim 形）参数化。              *)
(*   ③ UNQ  bxuq_lim_uniq（闸门件，UpReqBanachLimUniq.vo）：      *)
(*        同序列双极限 bae 相等 ⟹ e^a·e^(−a) == bone。           *)
(*      极限唯一性被类缺反可分性字段挡死（B25/BASM 双卡在案），   *)
(*      非本席可导出；同②以 bxoo_uniq_shape（Set 面）参数化。     *)
(*   ④ BXB/B25 尾件：bxdef_exp bzero == bone。                  *)
(*      bxb_series_zero/bxdef_esp_zero_series 给「部分和恒一」； *)
(*      bxoo_lim_esp_zero_bone 换骨为 blim (esp bzero) bone；    *)
(*      再吃 ③唯一性 ⟹ 尾件 bae 全等式（本席真实现，参数化于③）。 *)
(*   合取：bae_trans (①③) (④对称) ⟹ e^a·e^(−a) == e^0。        *)
(*                                                             *)
(* 降档声明（如实，非承认件）：闸门双件在飞（截至开工 ls：        *)
(*   CauchyD.v 52KB 在飞无 .vo；LimUniq 全无踪），主件以          *)
(*   bxoo_exp_opp_one_assembly 交付——全链 eps 记账之外的          *)
(*   ①③④装配步骤全部真实现且机器核验，唯②③的两个闸门语句        *)
(*   以显式 Set 面假设（blim 形/bxoo_uniq_shape）留槽。闸门开任一  *)
(*   即按文末接线规格 30 分钟内换槽收口 bxoo_exp_opp_one。        *)
(*                                                             *)
(* 机械件（闸门无关，本席全绿交付）：bxoo_lim_esp_zero_bone       *)
(*   （bzero 邻域换骨）、bxoo_nearone_blim（CD3 形→blim 换骨）、  *)
(*   bxoo_bmult_assoc_sym（emul 整理件）。                       *)
(*                                                             *)
(* 红线自审：语句面全 Set（bae/blim/QltT/sigT/NatLe 均为         *)
(*   S01/S02/Exp 既有 Set 承载面）；无新增 Prop 命题；无假设件；  *)
(*   无公理/承认件/弃证面；类字段投影一律 @ 全显式喂参            *)
(*   （BINV3 卡阴面二纪律）。禁改任何既有 .v。                    *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
Require Import UpReqBanachExpAdd.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1 机械件一（bzero 邻域换骨）：零元级数部分和序列收敛到 bone。  *)
(*   部分和恒一（bxdef_esp_zero_series/BXB bxb_series_zero 同面） *)
(*   ⟹ 距离恒为 ‖bone+(−bone)‖=0 ⟹ N=0 闭式证书。               *)
(* ============================================================ *)

Lemma bxoo_lim_esp_zero_bone : forall (B : BanachAlg),
  blim B (fun n : nat => exp_series_partial B (@bzero B) n) (@bone B).
Proof.
  intros B q Hq.
  refine (existT (fun N : nat => forall n : nat, NatLe N n ->
            QltT (@bnorm B (@bplus B (exp_series_partial B (@bzero B) n)
                                     (@bopp B (@bone B)))) q) 0%nat _).
  intros n Hn.
  rewrite (@bnorm_wd B
      (@bplus B (exp_series_partial B (@bzero B) n)
               (@bopp B (@bone B)))
      (@bplus B (@bone B) (@bopp B (@bone B)))
      (@bplus_wd B (exp_series_partial B (@bzero B) n)
                  (@bopp B (@bone B))
                  (@bone B) (@bopp B (@bone B))
                  (bxdef_esp_zero_series B n)
                  (@bae_refl B (@bopp B (@bone B))))).
  rewrite (@bnorm_wd B
      (@bplus B (@bone B) (@bopp B (@bone B)))
      (@bzero B)
      (@bplus_opp B (@bone B))).
  rewrite (@bnorm_zero B).
  exact Hq.
Qed.

(* ============================================================ *)
(* S1 机械件二（CD3 形→blim 换骨）：near-one 邻域形与 blim 形     *)
(*   在 l=bone 处逐字同构（blim u bone 展开=本假设形）。          *)
(*   CD3 接线槽：若 bxcd_prod_near_one 实形为                    *)
(*     forall B a q, QltT 0 q -> sigT N, forall n, NatLe N n ->  *)
(*       QltT (bnorm (bplus (esp a n·esp(bopp a) n) (bopp bone))) q*)
(*   则 bxoo_nearone_blim B _ (bxcd_prod_near_one B a) 一步上桥。 *)
(* ============================================================ *)

Lemma bxoo_nearone_blim : forall (B : BanachAlg) (S : nat -> (@BA B)),
  (forall q : Q, QltT 0 q ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (@bnorm B (@bplus B (S n) (@bopp B (@bone B)))) q)) ->
  blim B S (@bone B).
Proof.
  intros B S H q Hq. exact (H q Hq).
Qed.

(* ============================================================ *)
(* S1 机械件三（emul 整理件）：乘法结合对称面（非交换类下唯一     *)
(*   保安的整理形；类无 bmult_comm，交换面不可造，如实不硬凑）。   *)
(* ============================================================ *)

Lemma bxoo_bmult_assoc_sym : forall (B : BanachAlg) (x y z : (@BA B)),
  @bae B (@bmult B (@bmult B x y) z) (@bmult B x (@bmult B y z)).
Proof.
  intros B x y z. exact (@bae_sym B _ _ (@bmult_assoc B x y z)).
Qed.

(* ============================================================ *)
(* S2 UNQ 接线形状（Set 面）：同序列双极限 bae 相等——            *)
(*   主件必要件的形状钉。UNQ 落盘后若 bxuq_lim_uniq 与此同形，    *)
(*   接线= exact (bxuq_lim_uniq B)；若参序/类索引异形，           *)
(*   按本形状包一层换序适配（eps 记账为零，纯参序搬运）。          *)
(* ============================================================ *)

Definition bxoo_uniq_shape (B : BanachAlg) : Set :=
  forall (u : nat -> (@BA B)) (x y : (@BA B)),
    blim B u x -> blim B u y -> @bae B x y.

(* ============================================================ *)
(* S3 尾件（④，参数化于③）：bxdef_exp bzero == bone。            *)
(*   两条极限链同喂唯一性：bxdef_exp_spec（ExpDef 出口）+         *)
(*   bxoo_lim_esp_zero_bone（S1 机械件一）。                      *)
(* ============================================================ *)

Lemma bxoo_bzero_eq_bone_assembly : forall (B : BanachAlg),
  bxoo_uniq_shape B -> @bae B (bxdef_exp B (@bzero B)) (@bone B).
Proof.
  intros B Hunq.
  exact (Hunq (fun n : nat => exp_series_partial B (@bzero B) n)
              (bxdef_exp B (@bzero B)) (@bone B)
              (bxdef_exp_spec B (@bzero B))
              (bxoo_lim_esp_zero_bone B)).
Qed.

(* ============================================================ *)
(* S4 主装配件（①+②+③+④ 合取收口，参数化于②③两闸门）：         *)
(*   bae (e^a·e^(−a)) (e^0) := bae_trans                          *)
(*     (唯一性：序列左极限 e^a·e^(−a) == 近邻极限 bone)            *)
(*     (对称(④尾件))。                                            *)
(*   全部装配步骤真实现（bae_trans 合取 + 唯一性两次消费 +         *)
(*   对称换向），唯②的 blim 槽与③的 uniq 槽为显式假设。           *)
(* ============================================================ *)

Theorem bxoo_exp_opp_one_assembly : forall (B : BanachAlg) (a : (@BA B)),
  bxoo_uniq_shape B ->
  blim B (fun n : nat => @bmult B (exp_series_partial B a n)
                                  (exp_series_partial B (bopp a) n))
         (@bone B) ->
  @bae B (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
        (bxdef_exp B (@bzero B)).
Proof.
  intros B a Hunq Hnear.
  exact (@bae_trans B
           (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
           (@bone B)
           (bxdef_exp B (@bzero B))
           (Hunq (fun n : nat => @bmult B (exp_series_partial B a n)
                                  (exp_series_partial B (bopp a) n))
                 (@bmult B (bxdef_exp B a) (bxdef_exp B (bopp a)))
                 (@bone B)
                 (bxadd_esp_prod_blim B a (bopp a))
                 Hnear)
           (@bae_sym B (bxdef_exp B (@bzero B)) (@bone B)
             (bxoo_bzero_eq_bone_assembly B Hunq))).
Qed.

(* ============================================================ *)
(* S5 UNQ 闸收口件（04:25 UpReqBanachLimUniq.vo 落盘，探针预验后   *)
(* 正册收割）：bxdef_exp bzero == bone——Ext 层无条件 bae 全等式，  *)
(* B25 挂账②「exp(0)=one 完全等式面」对 Ext 实例兑现。             *)
(* ============================================================ *)

Corollary bxoo_bzero_eq_bone : forall (E : BanachAlgExt),
  @bae (@bxce_base E)
    (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E)))
    (@bone (@bxce_base E)).
Proof.
  intros E.
  apply (bxoo_bzero_eq_bone_assembly (@bxce_base E)).
  exact (bxuq_lim_uniq E).
Qed.

(* ============================================================ *)
(* 闸门开后接线规格（04:14 按 CD3/UNQ 在飞源件语句实形定稿；        *)
(* 后继席照抄即收口，预算 ≤30 分钟）：                             *)
(*                                                             *)
(*   Require Import UpReqBanachClassExt.                        *)
(*   Require Import UpReqBanachLimUniq.    (* ③ UNQ .vo 落盘 *)   *)
(*   Require Import UpReqBanachCauchyD.    (* ② CD3 .vo 落盘 *)   *)
(*                                                             *)
(*   Theorem bxoo_exp_opp_one : forall (E : BanachAlgExt)        *)
(*     (a : (@BA (@bxce_base E))),                                *)
(*     @bae (@bxce_base E)                                        *)
(*       (@bmult (@bxce_base E) (bxdef_exp (@bxce_base E) a)       *)
(*                    (bxdef_exp (@bxce_base E)                   *)
(*                       (@bopp (@bxce_base E) a)))               *)
(*       (bxdef_exp (@bxce_base E) (@bzero (@bxce_base E))).       *)
(*   Proof.                                                        *)
(*     intros E a.                                                 *)
(*     apply (bxoo_exp_opp_one_assembly (@bxce_base E) a           *)
(*             (bxuq_lim_uniq E)).                                 *)
(*     apply (bxoo_nearone_blim (@bxce_base E)).                   *)
(*     apply (bxcd_prod_near_one (@bxce_base E) a                  *)
(*             (@bxce_coef_plus E) (@bxce_coef_wd E)).             *)
(*   Qed.                                                          *)
(*                                                             *)
(* 实形核验存照（04:14 在飞源读定）：                               *)
(*   ③ bxuq_lim_uniq : forall E u l1 l2, blim base u l1 ->          *)
(*        blim base u l2 -> bae l1 l2 ——剥 E 后=bxoo_uniq_shape     *)
(*        base 同构（UNQ 另赠消费位 bxuq_prod_lim_joint：           *)
(*        blim 乘积列 l ⟹ bae l (la·lb)，等价备选路线）。           *)
(*   ② bxcd_prod_near_one : forall B a, hplus -> hwd ->             *)
(*        forall q, 0<q -> sigT N, forall n, N<=n ->                *)
(*        QltT (bnorm (bplus (esp a n·esp(−a) n) (bopp bone))) q     *)
(*        ——邻域位与 bxoo_nearone_blim 假设形逐字同构；其 hplus/hwd  *)
(*        两假设=恰 Ext 类字段 bxce_coef_plus/bxce_coef_wd，          *)
(*        故终面定理量化在 BanachAlgExt 层（plain BanachAlg 无        *)
(*        coef 相容性不可喂，UNQ bxce_sep 二波同层——接口实形）。     *)
(*   探针 _tbxoo_probe_uniq.v 已 -vos 预校验本接线（除②未落.vo 外   *)
(*   全链类型核验，LimUniq.vos 中间态 inconsistent=ClassExt.vo      *)
(*   04:11 换代所致，UNQ 复编即愈，非本席病）。                      *)
(* ============================================================ *)
