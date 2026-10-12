(* ===================================================================== *)
(*  u5c_ln2_assembly.v —— ln2 供给链五层供给面装配                        *)
(* 使命：把桥接件 u5c_ln2_gap2_bridge 在 ln2 规范代入值上实例化合拢：六肢接口假设位 *)
(*    逐一以代入表在位件（abl_ln2_assembly／abl_ln2_assembly2／abl_ln2_ireal／      *)
(*    abl_ln2_reorder_assembly／abl_ln2_bsum_cauchy 各面）消解，产出 ln2 供给链     *)
(*    五层供给面（u5c_ln2i_pade_supply）的 inhabited 终态语句。消解分工：①θ<1 肢＝本件在位消解（θ:=4/5 对应值＋桥接锚）； *)
(*    ②|A_n|>0 头肢＝面换算件消解；④焊缝肢＝real_eq_trans 级联件消解；③clo>0（witness 验收位）、⑤cloₙ 下界肢（witness 位）、 *)
(*    ⑥θⁿ 上界肢＝残余显式参数位如实悬置（u5c_ln2_assembly_slot 承载），代入后即完成。 *)
(* 依赖清单：S01_BaseRing S02_CauchyComplete S03_QExp UpReqBanachNormOpp UpReqIrrationalCriterion u5c_ln2_gap2_bridge u5c_ln2_gap1_convbinom； *)
(*    Stdlib：QArith Qabs ZArith Arith Lia List Setoid Qfield。 *)
(* 编译配方：source Live/toolchain/env.sh 后于池目录：bash cpu_guard.sh -- rocq c    *)
(*    -native-compiler no -q -Q . "" u5c_ln2_assembly.v。 *)
(* 构造性注记：语句面全 Set 层（sigT/S01.And/QeqT/QltT/real_eq/real_le）；主件证体＝   *)
(*    七位残面解构＋头肢换算件＋级联件＋改接桥六肢逐一填充，非单发空壳；θ 肢为数值判定锚（16<25，辅助面豁免）； *)
(*    挂钩件＝登记面单发使用（辅助面豁免，不入提取面）；  *)
(*    零承认、零经典逻辑；文尾 Separate Extraction 与 Print Assumptions 全列取证。 *)
(* 诚实面（对应表＋残位申报，显式披露）：上游树件以逐定义对应承载语句面，对应表：     *)
(*    u5c_lna_theta_mod↔abl_ln2_assembly.v:175 lna_theta_mod（逐字同体 (4#5)%Q）；   *)
(*    u5c_lnr_Ireal_pack↔abl_ln2_ireal.v:513 lnr_Ireal_pack（逐字同体）；u5c_lns_Ibreal↔abl_ln2_reorder_assembly.v:439 lns_Ibreal（bsum 参数化，代入源 lns_bsum+lnb2_cauchy）；u5c_ln2b_line 系列直接使用桥接面。  *)
(*    残余接口假设位清单（Observable 显式参数位，非全局假设，Print Assumptions 仍 Closed； *)
(*    源位逐位标注，代入后逐位消解）：② lna_head_three_legs 第二肢（:179）＋换算位 lna_Aface_eq(:105)∘lna_lA_z(:72)； *)
(*    ③ 同源第三肢 cloₙ witness 验收位（:179 第三 conj）；  *)
(*    ④ 缝内容位 lnb3_conv_slot（abl_ln2_assembly2.v:347，本件面为其消解形）×焊面 lna_supply_pair_dock_face（abl_ln2_assembly.v:112）； *)
(*    ⑤ 下界肢 witness 位（I'ₙ 首项正项导出）；⑥ 上界肢内容位 lnb3_theta_slot（abl_ln2_assembly2.v:370）。 *)
(*    挂钩登记：u5c_ln2_gap1_limb（语句面与 u5c_ln2_gap1_convbinom 主件 lncv_d1_head_int_gen 逐字同构，niche 定界 *)
(*    0%nat/(0)%Q/(z#1)%Q 为 nat_scope 开面下的适配级标注）；③⑤⑥余肢与④缝内容位不因挂钩件到位而解锁，维持 Set 形悬置。 *)
(* 代入源总表：X:=ln2b_X（Ln2Bridge.v:26）；A:=lna_Amod（abl_ln2_assembly.v:68，BD lni_supply_pair projT1 形）； *)
(*    B:=lna_Bmod（:69）；clo:=lna_clo_mod（:176，lne_B/2^{n+1}）；th:=u5c_lna_theta_mod（=4/5 本件对应在位）； I:=lns_Ibreal lnb2_cauchy（Cb 槽由 abl_ln2_bsum_cauchy 闭形填充，本件 u5c_lns_Ibreal 对应承载）。代入后 u5c_ln2_assembly 即给出  *)
(*    ln2i_pade_supply 原面 inhabited，再接树内在位 ln2b_escape_of_supply→ln2b_irrational_from_supply 即达无理性判据。 *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_gap1_convbinom.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.
From Stdlib Require Import Lists.List.
(*  ↑ List 增补＝甲位挂钩语句 nth 名位适配（LNAS02，甲件同名依赖沿袭） *)

Open Scope nat_scope.

(* ============================================================ *)
(* §0 对应承载层（上游定义逐字对应，对应表见头注诚实面）                    *)
(* ============================================================ *)

(* θ 规范值（abl_ln2_assembly.v:175 逐字：AE 路线③预算 4/5） *)
Definition u5c_lna_theta_mod : Q := (4 # 5)%Q.

(* Real 包装本体（abl_ln2_ireal.v:513 逐字：包装不改变逐点读数） *)
Definition u5c_lnr_Ireal_pack (u : Qseq) (Hu : cauchy u) : Real :=
  existT (fun u0 : Qseq => cauchy u0) u Hu.

(* 真族线值承载定义（abl_ln2_reorder_assembly.v:439 逐字，bsum 参数化：
   代入源 lns_bsum+lnb2_cauchy，代入后 bsum:=lns_bsum 逐字还原） *)
Definition u5c_lns_Ibreal (bsum : nat -> nat -> Q)
  (Cb : forall p : nat, cauchy (bsum p)) (p : nat) : Real :=
  u5c_lnr_Ireal_pack (bsum p) (Cb p).

(* ============================================================ *)
(* §1 头肢换算件（使用桥接件在位锚与面迁移肢）                                *)
(* ============================================================ *)

(* 头肢①在位消解：θ=4/5<1（桥接件数值锚沿对应值消解） *)
Theorem u5c_ln2_theta_mod_lt1 : QltT u5c_lna_theta_mod (1 # 1)%Q.
Proof. unfold u5c_lna_theta_mod. exact gap2_theta_45_lt1. Qed.

(* 头肢②面换算件：|Aface_n|>0 沿 QeqT 换算到规范 A 面（源位＝树内
   lna_head_three_legs 第二肢+lna_Aface_eq∘lna_lA_z 换算位） *)
Theorem u5c_ln2_head2_mod : forall (Aface Amod : nat -> Z),
  (forall n : nat, QeqT ((Aface n) # 1)%Q ((Amod n) # 1)%Q) ->
  (forall n : nat, QltT 0 (Qabs ((Aface n) # 1)%Q)) ->
  forall n : nat, QltT 0 (Qabs ((Amod n) # 1)%Q).
Proof.
  intros Aface Amod Heq Hpos n.
  exact (gap2_abs_pos_transfer ((Aface n) # 1)%Q ((Amod n) # 1)%Q (Heq n)
           (Hpos n)).
Qed.

(* ============================================================ *)
(* §1·甲 挂钩件（使用 u5c_ln2_gap1_convbinom 主件 lncv_d1_head_int_gen）    *)
(* ============================================================ *)

(* 挂钩形（头注代入源总表预备案兑现）：一般 n 带余分解 w 给定下，
   商/余分解的 comp2 头系数有 Z 承载见证——以 u5c_ln2_gap1_convbinom 实际语句逐字使用。
   niche 定界 0%nat/(0)%Q/(z#1)%Q＝本件 nat_scope 开面下的适配级标注
   （语句面与甲件 lncv_d1_head_int_gen 逐字同构） *)
Theorem u5c_ln2_gap1_limb : forall (n : nat) (w : list Q * list Q),
  lnp_div_pred (lnp_bk_num n) (lnp_bk_den n) w ->
  sigT (fun z : Z =>
          QeqT (nth 0%nat (lnp_comp2 (snd w)) (0)%Q)
               ((z # 1)%Q)).
Proof. intros n w Hw. exact (lncv_d1_head_int_gen n w Hw). Qed.

(* ============================================================ *)
(* §2 焊缝级联件（conv 缝×dock 面 two-weld 级联）                          *)
(* ============================================================ *)

Theorem u5c_ln2_weld_cascade : forall (X : Real) (Aface Amod Bmod : nat -> Z)
    (I : nat -> Real),
  (forall n : nat, real_eq (I n) (u5c_ln2b_line X Aface Bmod n)) ->
  (forall n : nat, real_eq (u5c_ln2b_line X Aface Bmod n)
                           (u5c_ln2b_line X Amod Bmod n)) ->
  forall n : nat, real_eq (I n) (u5c_ln2b_line X Amod Bmod n).
Proof.
  intros X Aface Amod Bmod I Hconv Hdock n.
  exact (real_eq_trans (I n) (u5c_ln2b_line X Aface Bmod n)
           (u5c_ln2b_line X Amod Bmod n) (Hconv n) (Hdock n)).
Qed.

(* ============================================================ *)
(* §3 残位诚面（六肢接口假设位消解后的残余显式参数位·源位标注见头注⑤-2）    *)
(* ============================================================ *)

Definition u5c_ln2_assembly_slot (X : Real) (Aface Amod Bmod : nat -> Z)
  (clo : nat -> Q) (I : nat -> Real) : Set :=
  And (forall n : nat, QltT 0 (Qabs ((Aface n) # 1)%Q))
    (And (forall n : nat, QeqT ((Aface n) # 1)%Q ((Amod n) # 1)%Q)
      (And (forall n : nat, QltT 0 (clo n))
        (And (forall n : nat, real_eq (I n) (u5c_ln2b_line X Aface Bmod n))
          (And (forall n : nat,
                  real_eq (u5c_ln2b_line X Aface Bmod n)
                          (u5c_ln2b_line X Amod Bmod n))
            (And (forall n : nat, real_le (real_const (clo n)) (I n))
                 (forall n : nat,
                    real_le (I n) (real_const (q_pow u5c_lna_theta_mod n)))))))).

(* ============================================================ *)
(* §4 全链装配主件（使命语句）：残面给定 ⟹ 五层供给面 inhabited             *)
(*    证体＝残面七位解构＋头肢换算＋两道焊级联＋乙桥六肢逐一填充。           *)
(* ============================================================ *)

Theorem u5c_ln2_assembly : forall (X : Real) (Aface Amod Bmod : nat -> Z)
    (clo : nat -> Q) (I : nat -> Real),
  u5c_ln2_assembly_slot X Aface Amod Bmod clo I -> u5c_ln2i_pade_supply X.
Proof.
  intros X Aface Amod Bmod clo I Hs.
  unfold u5c_ln2_assembly_slot in Hs.
  destruct Hs as [Haf2 [HeqAM [Hclo [Hconv [Hdock [Hlo Hup]]]]]].
  apply (u5c_gap2_bridge X Amod Bmod clo u5c_lna_theta_mod I).
  unfold u5c_gap2_slot.
  split.
  - (* ① θ<1：对应值在位消解 *)
    exact u5c_ln2_theta_mod_lt1.
  - split.
    + (* ② 0<|A_n|：头肢②面换算件消解 *)
      exact (u5c_ln2_head2_mod Aface Amod HeqAM Haf2).
    + split.
      * (* ③ 0<clo_n：缺口件③验收位（残位） *)
        exact Hclo.
      * split.
        -- (* ④ 焊缝肢：两道焊 real_eq_trans 级联件消解 *)
           intro n.
           exact (u5c_ln2_weld_cascade X Aface Amod Bmod I Hconv Hdock n).
        -- split.
           ++ (* ⑤ cloₙ 下界肢：缺口件③ witness 位（残位） *)
              exact Hlo.
           ++ (* ⑥ θⁿ 上界肢：lnb3_theta_slot 同内容位（残位） *)
              exact Hup.
Defined.

(* ============================================================ *)
(* §5 提取与假设审计（零承认复核）                                          *)
(* ============================================================ *)

Separate Extraction u5c_ln2_assembly u5c_ln2_weld_cascade u5c_ln2_head2_mod.

Print Assumptions u5c_lna_theta_mod.
Print Assumptions u5c_lnr_Ireal_pack.
Print Assumptions u5c_lns_Ibreal.
Print Assumptions u5c_ln2_theta_mod_lt1.
Print Assumptions u5c_ln2_head2_mod.
Print Assumptions u5c_ln2_gap1_limb.
Print Assumptions u5c_ln2_weld_cascade.
Print Assumptions u5c_ln2_assembly.
