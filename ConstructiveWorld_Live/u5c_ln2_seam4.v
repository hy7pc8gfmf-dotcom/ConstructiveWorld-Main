(* ===================================================================== *)
(*  u5c_ln2_seam4.v —— ln2 供给链④缝内容位实层铸造                        *)
(* 使命：把④缝内容位从悬置转实层。内容位定义面＝树内 lnb3_conv_slot （abl_ln2_assembly2.v:347）的池内消解形：  *)
(*       forall n, real_eq (I n) (u5c_ln2b_line X Aface Bmod n)           *)
(* （＝装配槽 u5c_ln2_assembly_slot 第四肢）。三段施工： (1) Q 层前置＝列表代数资产使用：分母线性幂系数闭形新肢（den_n =  *)
(* [1;−1/2]^(n+1) 的 k 次系数 == (−1/2)^k·C(n+1,k)，除法余式系数算术 的分母侧承载）；头位 d₁ Z 承载见证已由 u5c_ln2_gap1_limb 机证入链  *)
(* （本件零重复对应）。(2) 实层升位（主件）＝u5c_ln2_seam4_content： ④位线值读数差逐点恒等式＋残差挤压两前提 ⟹ real_eq 内容位  *)
(*        （eps/N 见证构造＋Qabs_wd 目标向导＋Qcompare 传送，零 Qeq 重写）。  *)
(*    (3) 接④位＝塞位证书（装配槽第四肢逐字面机证匹配）＋焊级联             *)
(*        （使用 u5c_ln2_weld_cascade 的 Hconv 位直插）。 *)
(* 依赖：S01_BaseRing S02_CauchyComplete S03_QExp UpReqBanachNormOpp UpReqIrrationalCriterion u5c_ln2_gap2_bridge（u5c_ln2b_line 面）  *)
(*    u5c_ln2_gap1_convbinom（Q 层资产）u5c_ln2_assembly（u5c_lns_Ibreal／    *)
(*    焊级联／装配槽面）；Stdlib：QArith Qabs ZArith Arith Lia List Setoid Qfield。 *)
(*  编译配方：source /Users/apple/Desktop/ConstructiveWorld/Live/toolchain/env.sh 后于池目录： *)
(*    bash cpu_guard.sh -- rocq c -native-compiler no -q -Q . "" u5c_ln2_seam4.v。 *)
(* 构造性注记：语句面全 Set 层（sigT/S01.And/QeqT/QltT/real_eq）；主件证体＝eps/N 见证构造＋ Qabs_wd 目标向导＋Qcompare 传送（gap2_abs_pos_transfer 同款手法；nat_scope 下 Qeq 重写/  *)
(* setoid_rewrite 均不可承载，证内零 Qeq 重写，读数闭 sread_form／sline_form 定义性小件承载） ＋real_eq_trans 级联挂 §4 焊件（非单发空壳）；Q 层前置肢为单发使用（登记面辅助位，数值锚  *)
(*    辅助面豁免先例，不入提取面）；零承认、零经典逻辑、零 solver；文尾 Separate Extraction 与   *)
(*    Print Assumptions 全列取证。 *)
(*  诚实面（工艺出处与冻结申报，显式披露）：④缝内容位树内源位＝abl_ln2_assembly2.v:347        *)
(*    lnb3_conv_slot（池内消解形＝ln2b_line 到 u5c_ln2b_line 面迁移）；有限 M 形勘录坐标＝      *)
(*    树侧 DE 勘录②同款登记面。 *)
(* 冻结申报（真不可达处如实悬置）：主件两前提（线值读数差逐点恒等式 Hid、残差挤压 Hrho）的 树侧供给位＝真族项列／换序闭形与尾界（换序件 abl_ln2_reorder_assembly 换序肢＋勘录②登记面），  *)
(*    不在本池 Require 域——本件以 Observable 显式参数位承载（非全局假设，Print Assumptions 仍    *)
(*    Closed），逐位代入即闭合，不虚报机证。前提形注记：Hid 取「部分和 − ④位线值读数 == 残差」     *)
(* 差形（肢逐点同形）；与树侧有限 M 形原式（Σ bterm == A_n·x − B_n）经 Q 环 ring 等价互化＋ 线值号性面（树侧 dock／供给对承载）；sline_form／sread_form 给出读数与 A_n·x_k − B_n 闭形  *)
(*    之定义性换算。 *)
(*    与三源件关系：甲乙装配三件语句面零改动（只读使用）；三残位不因本件到位而解锁——到位只消解    *)
(*    ④位 Hconv 肢的悬置，⑤⑥两肢仍待缺口件③ witness（theta_slot 内容位）。 *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_gap1_convbinom.
Require Import u5c_ln2_assembly.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia Setoid Qfield.
From Stdlib Require Import Lists.List.

Open Scope nat_scope.

(* ============================================================ *)
(* §1 Q 层前置（列表代数资产使用·新肢）                                    *)
(* ============================================================ *)

(* 分母线性幂系数闭形：den_n = [1;−1/2]^(n+1) 的 k 次系数 ==
   (−1/2)^k·C(n+1,k)——④缝 Q 层内容位的分母侧承载（除法余式系数算术
   之用）。单发使用 u5c_ln2_gap1_convbinom 之 lncv_nth_pow_binom（辅助面豁免先例）。 *)
Theorem u5c_ln2_seam4_q_den_coeff : forall (n k : nat),
  QeqT (nth k (lnp_bk_den n) (0)%Q)
       (q_pow (-(1 # 2)) k * lncv_qz (bkC (Datatypes.S n) k))%Q.
Proof.
  intros n k. unfold lnp_bk_den, lnp_den_lin.
  apply (lncv_nth_pow_binom (-(1 # 2)) (Datatypes.S n) k).
Qed.

(* 带符线值第 k 读数（定义面＝实层规范读出；闭形见 sread_form） *)
Definition u5c_ln2_seam4_sread (X : Real) (A B : nat -> Z) (n k : nat) : Q :=
  projT1 (real_plus (real_mult (real_const ((A n) # 1)%Q) X)
                    (real_opp (real_const ((B n) # 1)%Q))) k.

(* 读数闭形：sread == A_n·X_k − B_n（池内 proj 引理的定义性换算；
   本件证内禁 Qeq 重写——nat_scope 下 Qeq 重写/setoid 均不可承载，
   证体一律走定义工开＋Qcompare 传送〔乙件 gap2_abs_pos_transfer
   同款工艺〕，此为审计面独立小件）。 *)
Lemma u5c_ln2_seam4_sread_form :
  forall (X : Real) (A B : nat -> Z) (n k : nat),
  QeqT (u5c_ln2_seam4_sread X A B n k)
       (((A n) # 1)%Q * projT1 X k + - ((B n) # 1)%Q)%Q.
Proof.
  intros X A B n k. unfold u5c_ln2_seam4_sread.
  destruct X as [u Hu].
  unfold real_plus, real_mult, real_const, real_opp. cbn [projT1].
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ④位线值读数闭形：u5c_ln2b_line 第 k 读数 == |A_n·X_k − B_n|
   （＝Qabs∘sread；审计面独立小件，证体同上定义工开）。 *)
Lemma u5c_ln2_seam4_sline_form :
  forall (X : Real) (A B : nat -> Z) (n k : nat),
  QeqT (projT1 (u5c_ln2b_line X A B n) k)
       (Qabs (u5c_ln2_seam4_sread X A B n k)).
Proof.
  intros X A B n k. unfold u5c_ln2b_line, u5c_ln2_seam4_sread.
  destruct X as [u Hu].
  unfold real_abs, real_plus, real_mult, real_const, real_opp.
  cbn [projT1].
  apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §2 实层升位主件（④缝内容位铸造：Q 层前置 ⟹ real_eq 内容位）             *)
(* ============================================================ *)

(* 两前提（树侧供给位·Observable 显式参数承载，见头注⑤-2）：
   Hid＝④位线值读数差形逐点恒等式（部分和 − 线值读数 == 残差，
   与④位肢逐点同形之有限 M 形差形）；Hrho＝残差挤压。
   证体＝eps/N 见证构造＋Qabs_wd 目标向导＋Qcompare 传送
   （零 Qeq 重写、零 solver）。 *)
Theorem u5c_ln2_seam4_content :
  forall (X : Real) (Aface Bmod : nat -> Z)
         (bsum : nat -> nat -> Q) (Cb : forall p : nat, cauchy (bsum p))
         (rho : nat -> nat -> Q) (n : nat),
  (forall k : nat,
      QeqT ((bsum n k - projT1 (u5c_ln2b_line X Aface Bmod n) k)%Q)
           (rho n k)) ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall k : nat, NatLe N k ->
             QltT (Qabs (rho n k)) eps)) ->
  real_eq (u5c_lns_Ibreal bsum Cb n) (u5c_ln2b_line X Aface Bmod n).
Proof.
  intros X Aface Bmod bsum Cb rho n Hid Hr eps Heps.
  destruct (Hr eps Heps) as [N HN].
  exists N. intros k Hk.
  unfold QltT, Qlt_bool in *.
  unfold u5c_lns_Ibreal, u5c_lnr_Ireal_pack. cbn [projT1].
  assert (HabsEq : (Qabs ((bsum n k
                           - projT1 (u5c_ln2b_line X Aface Bmod n) k)%Q)
                 == Qabs (rho n k))%Q).
  { apply Qabs_wd. apply qeqT_imp_qeq. exact (Hid k). }
  assert (Hcmp : Qcompare (Qabs ((bsum n k
                                  - projT1 (u5c_ln2b_line X Aface Bmod n) k)%Q)) eps
               = Qcompare (Qabs (rho n k)) eps).
  { apply (Qcompare_comp _ _ HabsEq eps eps).
    - apply Qeq_refl. }
  rewrite Hcmp.
  exact (HN k Hk).
Qed.

(* ============================================================ *)
(* §3 接④位：塞位证书＋焊级联就绪件                                       *)
(* ============================================================ *)

(* 塞位证书：本件铸造的内容面 == 装配槽第四肢（④位 Hconv 肢）逐字面
   ——机证匹配，非口径转述。 *)
Theorem u5c_ln2_seam4_fills_slot4 :
  forall (X : Real) (Aface Amod Bmod : nat -> Z) (clo : nat -> Q)
         (I : nat -> Real),
  u5c_ln2_assembly_slot X Aface Amod Bmod clo I ->
  (forall n : nat, real_eq (I n) (u5c_ln2b_line X Aface Bmod n)).
Proof.
  intros X Aface Amod Bmod clo I Hs.
  unfold u5c_ln2_assembly_slot in Hs.
  destruct Hs as [Haf2 [HeqAM [Hclo [Hconv [Hdock [Hlo Hup]]]]]].
  exact Hconv.
Qed.

(* 焊级联就绪件：本件内容位直插 u5c_ln2_weld_cascade 的 Hconv 位，
   接焊面 Hdock 即达规范 Amod 面（④肢两道焊全链成形）。 *)
Theorem u5c_ln2_seam4_to_weld :
  forall (X : Real) (Aface Amod Bmod : nat -> Z) (I : nat -> Real),
  (forall n : nat, real_eq (I n) (u5c_ln2b_line X Aface Bmod n)) ->
  (forall n : nat, real_eq (u5c_ln2b_line X Aface Bmod n)
                           (u5c_ln2b_line X Amod Bmod n)) ->
  forall n : nat, real_eq (I n) (u5c_ln2b_line X Amod Bmod n).
Proof.
  intros X Aface Amod Bmod I Hconv Hdock n.
  exact (u5c_ln2_weld_cascade X Aface Amod Bmod I Hconv Hdock n).
Qed.

(* ============================================================ *)
(* §4 提取与假设审计（零承认复核）                                          *)
(* ============================================================ *)

Separate Extraction u5c_ln2_seam4_sread u5c_ln2_seam4_sread_form
  u5c_ln2_seam4_sline_form u5c_ln2_seam4_content
  u5c_ln2_seam4_fills_slot4 u5c_ln2_seam4_to_weld.

Print Assumptions u5c_ln2_seam4_q_den_coeff.
Print Assumptions u5c_ln2_seam4_sread.
Print Assumptions u5c_ln2_seam4_sread_form.
Print Assumptions u5c_ln2_seam4_sline_form.
Print Assumptions u5c_ln2_seam4_content.
Print Assumptions u5c_ln2_seam4_fills_slot4.
Print Assumptions u5c_ln2_seam4_to_weld.
