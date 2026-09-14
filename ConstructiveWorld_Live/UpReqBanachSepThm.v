(* ============================================================ *)
(* UpReqBanachSepThm.v —— 席AA7：bxce_sep 论证包落地（B7 首单，       *)
(* 20260914；禁改 ClassExt/LimUniq 本体一行，只 Require 消费）        *)
(* ============================================================ *)
(* 使命：B25 挂账「exp(0) 完全等式面」转化件——bxce_sep 字段            *)
(*   (forall a,(forall eps,QltT 0 eps -> QltT (bnorm a) eps) ->       *)
(*    bae a bzero) 从「假设槽位」转化为「库内可证定理面」（候选 A：     *)
(*   Real 载体实例 bxra_real_pre，AA3 装配）。                        *)
(* 三步论证包（AA5 工单逐级落地）：                                    *)
(*   S0 = ① Q 引擎件 spt_q_abs_arb_small_eq0（+消桥件                  *)
(*        spt_qabs_eq0_inv）：|x| 任意小 ⟹ x == 0；分臂 Qlt_le_dec；   *)
(*        正臂 eps:=½·|x|（Qmult_lt_r 乘积正性，双参数驱动）自反矛盾；  *)
(*        负臂 Qle_antisym 合流 Qabs_nonneg；消桥臂 vm_compute 直拆。  *)
(*   S1 = ② 载体特化 spt_qabs_qnorm_head：范数处方 Qabs∘qnorm∘head      *)
(*        定义级 unwrap（bxib_qnorm_fix 换代表元 + Qabs_wd）。         *)
(*   S2 = ③ bae 闭环 spt_bxce_sep_real（主件：bxra_real_pre 上的       *)
(*        bxce_sep 字段语句面定理化；bae 与范数同读 head，盲区互消）。 *)
(*   S3 = 装配位消费（条件件）：spt_ext_sep_slot_theorem（完备性闸门    *)
(*        Hc 作显式 Set 参数，非承认件，EQV 席先例形）+                *)
(*        spt_ext_of_real（bxce_mk 三引理桥全装配，sp 槽由定理喂入）    *)
(*        + spt_uniq_reap（bxuq_lim_uniq 极限唯一性收割演示）——        *)
(*        B7 骨架落地时零返工接入。                                   *)
(* 适配点（工单→库内实形，详交付报告）：                               *)
(*   - 工单目标形为 Ext 装配槽位级；Ext 实例须完备载体，完备性语句      *)
(*     （bxin_pre_complete）系诚实挂账面，故主件落在 Pre 实例级        *)
(*     （现可达最高级），Ext 级以条件件呈现；                          *)
(*   - 正臂矛盾收口取 eps:=½·|x| 的乘积形（Qmult_lt_r 双参驱动：        *)
(*     Hpos 作 0<z 前提、Hhalfpos 作 x<y 驱动），工单「两边乘 2」      *)
(*     语义等价改走 ≤ 链（Qmult_le_compat_r+Qmult_1_l），少两跳重写。 *)
(* 公理面自审：全件零公理零承认零中断；主件出口 Closed（G3 面）。       *)
(* 语句面注记：Q 引擎件结论 x == 0 为 Qeq 面（Q 层可判定相等，承        *)
(*   ClassExt bxce_coef_wd 前提面既有形），余结论全 Set 面（bae/QeqT/  *)
(*   QltT/Id）。                                                       *)
(* 领土纪律：只新增本件（spt_ 前缀全库零撞名）；冻结类与在飞席位        *)
(*   文件未动一字；编译产物 .ml 定向 attn/_taa7_bak/ml。              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInst.
Require Import UpReqBanachInstReal.
Require Import UpReqBanachClassExt.
Require Import UpReqBanachLimUniq.
From Stdlib Require Import QArith.QArith QArith.Qabs.

(* ============================================================ *)
(* S0：① Q 引擎件                                                     *)
(* ============================================================ *)

(* 消桥件：|x| == 0 ⟹ x == 0（三分构造子级直拆，Qabs 定义级归约） *)
Lemma spt_qabs_eq0_inv : forall x : Q, Qabs x == 0 -> x == 0.
Proof.
  intros [n d] H.
  unfold Qeq in H. unfold Qeq.
  destruct n as [|p|p].
  - exact H.
  - exfalso. revert H. vm_compute. intro Hc. discriminate Hc.
  - exfalso. revert H. vm_compute. intro Hc. discriminate Hc.
Qed.

(* 引擎主件：|x| 小于任意正 eps ⟹ x == 0（AA5 工单①语句面逐字） *)
Theorem spt_q_abs_arb_small_eq0 : forall x : Q,
  (forall eps : Q, QltT 0 eps -> QltT (Qabs x) eps) -> x == 0.
Proof.
  intros x Hall.
  destruct (Qlt_le_dec 0 (Qabs x)) as [Hpos | Hnonpos].
  - (* 正臂 0 < |x|：eps := 0·|x|（=½·|x| 的乘积正性形），Hall 给
       |x| < 0·|x| < ½·|x| ≤ 1·|x| = |x| 自反矛盾 *)
    exfalso.
    assert (Hhalfpos : Qlt 0 (1#2)%Q) by reflexivity.
    assert (Hhalf_le : Qle (1#2)%Q 1%Q).
    { intro Hc. vm_compute in Hc. discriminate Hc. }
    assert (Heps : QltT 0 ((1#2)%Q * Qabs x)%Q).
    { pose proof (proj2 (Qmult_lt_r 0 (1#2)%Q (Qabs x) Hpos) Hhalfpos) as Hp.
      setoid_rewrite (Qmult_0_l (Qabs x)) in Hp.
      apply Qlt_to_QltT. exact Hp. }
    assert (Hle : Qle ((1#2)%Q * Qabs x) (Qabs x)).
    { pose proof (Qmult_le_compat_r (1#2)%Q 1%Q (Qabs x) Hhalf_le
                    (Qabs_nonneg x)) as Hle0.
      setoid_rewrite (Qmult_1_l (Qabs x)) in Hle0.
      exact Hle0. }
    exact (Qlt_irrefl (Qabs x)
             (Qlt_le_trans (Qabs x) ((1#2)%Q * Qabs x) (Qabs x)
                (QltT_to_Qlt _ _ (Hall ((1#2)%Q * Qabs x)%Q Heps)) Hle)).
  - (* 负臂 |x| ≤ 0：与非负性（Qabs_nonneg）合流 ⟹ |x| == 0 ⟹ 消桥 *)
    exact (spt_qabs_eq0_inv x (Qle_antisym (Qabs x) 0 Hnonpos
                                        (Qabs_nonneg x))).
Qed.

(* ============================================================ *)
(* S1：② 载体特化——范数处方的 Qabs 换代表元桥                          *)
(* ============================================================ *)

Lemma spt_qabs_qnorm_head : forall q : Q, QeqT (Qabs (bxib_qnorm q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  apply Qabs_wd.
  apply qeqT_imp_qeq.
  apply bxib_qnorm_fix.
Qed.

(* ============================================================ *)
(* S1.5：③ 核心件（具体 Id 面算法形，G3 提取出口——类投影型语句面       *)
(* 提取必生类型擦除垫片（bxin_bae＝__，先例 bxra_real_pre 实例同因），  *)
(* 故提取走本件；主件保持工单字段面语句、经本件定义级转换接线）          *)
(* ============================================================ *)

Definition spt_bxce_sep_core (a : Real)
  (Hall : forall eps : Q,
    QltT 0 eps -> QltT (Qabs (bxib_qnorm (bxra_head a))) eps) :
  Id (bxib_qnorm (bxra_head a)) (bxib_qnorm (bxra_head bxra_bzero_f)) :=
  bxib_qnorm_id_of_qeqT (bxra_head a) 0%Q
    (qeq_imp_qeqT (bxra_head a) 0%Q
       (spt_q_abs_arb_small_eq0 (bxra_head a)
          (fun eps Heps =>
            bxra_qltT_wd (Qabs (bxib_qnorm (bxra_head a)))
                         (Qabs (bxra_head a)) eps
              (spt_qabs_qnorm_head (bxra_head a)) (Hall eps Heps)))).

(* ============================================================ *)
(* S2：③ 主件——bxce_sep 字段语句面在 bxra_real_pre 上的定理化          *)
(* （工单目标形逐字，底座＝Pre 实例投影：bnorm＝Qabs∘qnorm∘head，       *)
(*   bae＝规范种型 Id(qnorm(head ·))(qnorm(head ·))，bzero＝const 0）  *)
(* ============================================================ *)

Theorem spt_bxce_sep_real : forall a : Real,
  (forall eps : Q, QltT 0 eps -> QltT (@bxin_bnorm bxra_real_pre a) eps) ->
  @bxin_bae bxra_real_pre a (@bxin_bzero bxra_real_pre).
Proof.
  intros a Hall.
  exact (spt_bxce_sep_core a Hall).
Qed.

(* ============================================================ *)
(* S3：装配位消费（条件件，完备性闸门 Hc＝显式 Set 参数，EQV 先例形）    *)
(* ============================================================ *)

(* bxce_sep 槽位定理化面（Ext 装配位点：桥产物 BanachAlg 上的字段形） *)
Lemma spt_ext_sep_slot_theorem :
  forall (Hc : bxin_pre_complete bxra_real_pre)
         (a : (@BA (bxra_BanachAlg_of_real Hc))),
    (forall eps : Q,
      QltT 0 eps -> QltT (@bnorm (bxra_BanachAlg_of_real Hc) a) eps) ->
    @bae (bxra_BanachAlg_of_real Hc) a (@bzero (bxra_BanachAlg_of_real Hc)).
Proof.
  intros Hc a Hall.
  exact (spt_bxce_sep_real a Hall).
Qed.

(* 全装配：bxce_mk 三引理桥，sp 槽由定理喂入（B7 落地时零返工接入） *)
Definition spt_ext_of_real (Hc : bxin_pre_complete bxra_real_pre) :
  BanachAlgExt :=
  bxce_mk (bxra_BanachAlg_of_real Hc)
          (@bcoef_plus (bxra_BanachAlg_of_real Hc))
          (@bcoef_wd (bxra_BanachAlg_of_real Hc))
          (spt_ext_sep_slot_theorem Hc).

(* 收割件：B25 挂账第二件（极限唯一性）在条件装配下的兑现演示——
   bxuq_lim_uniq 消费 spt_ext_of_real，泛型双极限 ⟹ bae 相等 *)
Lemma spt_uniq_reap :
  forall (Hc : bxin_pre_complete bxra_real_pre)
         (u : nat -> (@BA (@bxce_base (spt_ext_of_real Hc))))
         (l1 l2 : (@BA (@bxce_base (spt_ext_of_real Hc)))),
    blim (@bxce_base (spt_ext_of_real Hc)) u l1 ->
    blim (@bxce_base (spt_ext_of_real Hc)) u l2 ->
    @bae (@bxce_base (spt_ext_of_real Hc)) l1 l2.
Proof.
  intros Hc u l1 l2 H1 H2.
  exact (bxuq_lim_uniq (spt_ext_of_real Hc) u l1 l2 H1 H2).
Qed.

(* ============================================================ *)
(* 尾注（G1 面）：本件零公理、零承认、零中断；语句面 Prop 泄露仅        *)
(*   x == 0（Qeq，ClassExt 既有形）；出口闭包自检见编译 stdout。       *)
(* ============================================================ *)

(* ============================================================ *)
(* G3 面：提取探针 + 出口闭包自检                                      *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Set Extraction Output Directory "../attn/_taa7_bak/ml".
Separate Extraction spt_qabs_eq0_inv spt_q_abs_arb_small_eq0
  spt_qabs_qnorm_head spt_bxce_sep_core.

Print Assumptions spt_q_abs_arb_small_eq0.
Print Assumptions spt_bxce_sep_core.
Print Assumptions spt_bxce_sep_real.
Print Assumptions spt_ext_of_real.
Print Assumptions spt_uniq_reap.
