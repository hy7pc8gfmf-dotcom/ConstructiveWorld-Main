(* ===================================================================== *)
(*  u5c_ln2_s4fill.v —— ln2 ④缝内容位填充（切片 B 主铸件）                   *)
(* ===================================================================== *)
(*  使命：对 u5c_ln2_seam4_content 的两 Observable 前提位（Hid 线值读数差   *)
(*    形逐点恒等式／Hrho 残差挤压）做切片 B 填充：①Hid 位销案——规范残差    *)
(*    s4f_rho（真族部分和 − ④位线值读数）定义性承领（seam4 的 Hid 系自由    *)
(*    参数位，本件给出其正典见证使 Hid 成定理，缝内容收缩为单一位）；        *)
(*    ②Cb 载体槽代入实化——lns_bsum＋lnb2_cauchy（abl_ln2_bsum_cauchy       *)
(*    闭形填充，代入源总表「I:=lns_Ibreal lnb2_cauchy」兑现）；③验收链——   *)
(*    seam4_content 实例化经 u5c_ln2_seam4_fills_slot4／                    *)
(*    u5c_ln2_seam4_to_weld 直插装配槽，PA Closed；④非负性肢小铸（真族      *)
(*    部分和逐点严格正＋线读数绝对值面）；⑤RunAlive 数值锚 n=2/3 双侧       *)
(*    （线值闭形 vs 部分和 vm_compute 判定，Python Fractions 独立复算       *)
(*    仲裁在卷）。                                                         *)
(*  诚实面（残位如实申报）：Hrho（s4f_rho 的挤压位）＝本件唯一残余          *)
(*    Observable 前提位：其树侧供给位＝勘录②「Σ_k lnf_bterm n k ==          *)
(*    2^{n+1}·q̃_n·ln2 − 2^{n+1}·p_n」有限 M 形（abl_ln2_reorder_assembly   *)
(*    头注勘录②·campaign 级余件），如实冻结不代填；缺口单调收缩已兑现＝    *)
(*    seam4 两位（Hid+Hrho）→ 一位。槽上下文残余前提＝u5c_ln2_assembly     *)
(*    ⑤-2 同款分工：②Haf2／③Hclo／⑤Hlo／⑥Hup（slice C ⑥预算 face 位）    *)
(*    ＋Hdock 焊面（u5c_w1_witness_assembly_precursor 同款显式位；源位＝    *)
(*    conv_slot Aface→Amod 迁移形，候后续位代入消解）。零承认、零经典逻辑、  *)
(*    零 solver。                                                          *)
(*  数值锚仲裁（独立复算仪器）：Python Fractions 精确复算：n=2 K=15 残差     *)
(*    355667/1905131520 ≈ 1.867e-4 < 1/1000；n=2 K=20 残差 ≈ 4.495e-6 <    *)
(*    1/10^5；n=3 K=20 残差 ≈ 4.383e-5 < 1/1000。另勘证：级数总和 ==        *)
(*    2^{n+1}(q̃_n·ln2−p_n) 于 n=2/3 十位小数逐位吻合（勘录②形的数值面正证）。*)
(*  依赖：Stdlib（QArith/Qabs/ZArith/Lia）；S01_BaseRing、                  *)
(*    S02_CauchyComplete、S03_QExp、UpReqBanachNormOpp、                    *)
(*    UpReqIrrationalCriterion、UpReqLn2Irrational、RealIdentity、          *)
(*    PsQReindex、HansonLcm、BeukersLists、BeukersVariant、PolyIntegral、   *)
(*    PadeErrorIntegral、PintMono；u5c_ln2_gap2_bridge、                    *)
(*    u5c_ln2_gap1_convbinom、u5c_ln2_assembly、u5c_ln2_seam4；             *)
(*    abl_ln2_{tail_bound,sharp_weight,ireal,reorder,reorder_assembly,     *)
(*    bsum_cauchy}。零实数层、零经典逻辑、提取 Obj.magic=0。                *)
(*  对标：ln2 无理性 Beukers/Zudilin 型积分族线；lin2 缝线切片 B            *)
(*    （Hid 位填充与 Cb 载体实化）。                                        *)
(*  构造性注记：全语句 Set 承载；Print Assumptions 全谱 Closed              *)
(*    （Hrho 为显式 Observable 前提位·非全局假设声明）。                    *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_s4fill.v       *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachNormOpp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_gap1_convbinom.
Require Import u5c_ln2_assembly.
Require Import u5c_ln2_seam4.
Require Import RealIdentity PsQReindex HansonLcm BeukersLists BeukersVariant.
Require Import PolyIntegral PadeErrorIntegral PintMono.
Require Import UpReqLn2Irrational.
Require Import abl_ln2_tail_bound.
Require Import abl_ln2_sharp_weight.
Require Import abl_ln2_ireal.
Require Import abl_ln2_reorder.
Require Import abl_ln2_reorder_assembly.
Require Import abl_ln2_bsum_cauchy.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia.

Open Scope nat_scope.

(* ============================================================ *)
(* §1 规范残差与 Hid 位销案（④缝真内容·定义性承领）                           *)
(* ============================================================ *)

(* ★ 规范残差：真族部分和 − ④位线值读数（与 seam4 Hid 逐点同形之差形；
   line 读出面＝|A_n·X_k − B_n|，见 u5c_ln2_seam4_sline_form）。 *)
Definition s4f_rho (X : Real) (Aface Bmod : nat -> Z) (n k : nat) : Q :=
  (lns_bsum n k - projT1 (u5c_ln2b_line X Aface Bmod n) k)%Q.

(* ★ Hid 位销案：bsum − 线值读数 == s4f_rho——seam4 的 Hid 自由参数位
   经规范残差见证成定理（缝内容收缩为单一位：挤压位）。 *)
Theorem s4f_hid : forall (X : Real) (Aface Bmod : nat -> Z) (n k : nat),
  QeqT ((lns_bsum n k - projT1 (u5c_ln2b_line X Aface Bmod n) k)%Q)
       (s4f_rho X Aface Bmod n k).
Proof.
  intros X Aface Bmod n k. unfold s4f_rho.
  apply qeq_imp_qeqT. reflexivity.
Qed.

(* ============================================================ *)
(* §2 seam4_content 实例化（Cb 槽代入 lnb2_cauchy·代入源总表兑现）            *)
(* ============================================================ *)

Theorem s4f_content : forall (X : Real) (Aface Bmod : nat -> Z) (n : nat),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun N : nat => forall k : nat, NatLe N k ->
             QltT (Qabs (s4f_rho X Aface Bmod n k)) eps)) ->
  real_eq (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)
          (u5c_ln2b_line X Aface Bmod n).
Proof.
  intros X Aface Bmod n Hrho.
  exact (u5c_ln2_seam4_content X Aface Bmod lns_bsum lnb2_cauchy
           (fun p k => s4f_rho X Aface Bmod p k) n
           (fun k => s4f_hid X Aface Bmod n k) Hrho).
Qed.

(* ============================================================ *)
(* §3 验收链：两前提承领 ⟹ 装配槽 inhabited ＋ fills_slot4／to_weld 直插      *)
(*    （Hconv 肢＝s4f_content；残余位②③⑤⑥＋Hdock 显式承载，              *)
(*      诚实面见头注二）                                                    *)
(* ============================================================ *)

Theorem s4f_slot4_fills :
  forall (X : Real) (Aface Amod Bmod : nat -> Z) (clo : nat -> Q),
    (forall n : nat, QltT 0 (Qabs ((Aface n) # 1)%Q)) ->
    (forall n : nat, QeqT ((Aface n) # 1)%Q ((Amod n) # 1)%Q) ->
    (forall n : nat, QltT 0 (clo n)) ->
    (forall n : nat, forall eps : Q, QltT 0 eps ->
       sigT (fun N : nat => forall k : nat, NatLe N k ->
               QltT (Qabs (s4f_rho X Aface Bmod n k)) eps)) ->
    (forall n : nat,
       real_eq (u5c_ln2b_line X Aface Bmod n)
               (u5c_ln2b_line X Amod Bmod n)) ->
    (forall n : nat,
       real_le (real_const (clo n)) (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)) ->
    (forall n : nat,
       real_le (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)
               (real_const (q_pow (4 # 5)%Q n))) ->
    u5c_ln2_assembly_slot X Aface Amod Bmod clo
      (u5c_lns_Ibreal lns_bsum lnb2_cauchy).
Proof.
  intros X Aface Amod Bmod clo Haf2 HeqAM Hclo Hrho Hdock Hlo Hup.
  unfold u5c_ln2_assembly_slot.
  split.
  - exact Haf2.
  - split.
    + exact HeqAM.
    + split.
      * exact Hclo.
      * split.
        -- intro n. exact (s4f_content X Aface Bmod n (Hrho n)).
        -- split.
           ++ exact Hdock.
           ++ split.
              ** exact Hlo.
              ** exact Hup.
Qed.

(* 塞位证书方向：本件装配的槽实例经 u5c_ln2_seam4_fills_slot4 抽出
   Hconv 肢（逐字面机证匹配）。 *)
Theorem s4f_fills_slot4_of :
  forall (X : Real) (Aface Amod Bmod : nat -> Z) (clo : nat -> Q),
    (forall n : nat, QltT 0 (Qabs ((Aface n) # 1)%Q)) ->
    (forall n : nat, QeqT ((Aface n) # 1)%Q ((Amod n) # 1)%Q) ->
    (forall n : nat, QltT 0 (clo n)) ->
    (forall n : nat, forall eps : Q, QltT 0 eps ->
       sigT (fun N : nat => forall k : nat, NatLe N k ->
               QltT (Qabs (s4f_rho X Aface Bmod n k)) eps)) ->
    (forall n : nat,
       real_eq (u5c_ln2b_line X Aface Bmod n)
               (u5c_ln2b_line X Amod Bmod n)) ->
    (forall n : nat,
       real_le (real_const (clo n)) (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)) ->
    (forall n : nat,
       real_le (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)
               (real_const (q_pow (4 # 5)%Q n))) ->
    forall n : nat,
      real_eq (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)
              (u5c_ln2b_line X Aface Bmod n).
Proof.
  intros X Aface Amod Bmod clo Haf2 HeqAM Hclo Hrho Hdock Hlo Hup n.
  exact (u5c_ln2_seam4_fills_slot4 X Aface Amod Bmod clo
           (u5c_lns_Ibreal lns_bsum lnb2_cauchy)
           (s4f_slot4_fills X Aface Amod Bmod clo
              Haf2 HeqAM Hclo Hrho Hdock Hlo Hup) n).
Qed.

(* 焊级联方向：Hconv 肢＋Hdock 经 u5c_ln2_seam4_to_weld 直插达规范 Amod 面。 *)
Theorem s4f_to_weld :
  forall (X : Real) (Aface Amod Bmod : nat -> Z),
    (forall n : nat, forall eps : Q, QltT 0 eps ->
       sigT (fun N : nat => forall k : nat, NatLe N k ->
               QltT (Qabs (s4f_rho X Aface Bmod n k)) eps)) ->
    (forall n : nat,
       real_eq (u5c_ln2b_line X Aface Bmod n)
               (u5c_ln2b_line X Amod Bmod n)) ->
    forall n : nat,
      real_eq (u5c_lns_Ibreal lns_bsum lnb2_cauchy n)
              (u5c_ln2b_line X Amod Bmod n).
Proof.
  intros X Aface Amod Bmod Hrho Hdock n.
  exact (u5c_ln2_seam4_to_weld X Aface Amod Bmod
           (u5c_lns_Ibreal lns_bsum lnb2_cauchy)
           (fun n0 : nat => s4f_content X Aface Bmod n0 (Hrho n0))
           Hdock n).
Qed.

(* ============================================================ *)
(* §4 非负性肢小铸（载体面严格正＋线读数绝对值面非负）                         *)
(* ============================================================ *)

(* ★ 真族部分和逐点严格正：首项锚（1/6 档）沿单调传送。 *)
Theorem s4f_bsum_pos : forall (n k : nat), QltT 0 (lns_bsum n k).
Proof.
  intros n k.
  assert (E0 : (lnf_bterm n 0)%Q == (lns_bsum n 0)%Q)
    by (symmetry; apply lns_bsum_head).
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (lns_bsum n 0)%Q).
  - apply (lnr_qlt_transfer_r 0 (lnf_bterm n 0) (lns_bsum n 0)).
    + exact (lnf_bterm_pos n 0).
    + exact E0.
  - apply lns_bsum_mono. lia.
Qed.

(* 线读数绝对值面非负：u5c_ln2b_line 读出面＝Qabs（定义面）。 *)
Theorem s4f_line_readout_nonneg :
  forall (X : Real) (Aface Bmod : nat -> Z) (n k : nat),
  QleT' 0 (projT1 (u5c_ln2b_line X Aface Bmod n) k).
Proof.
  intros X Aface Bmod n k.
  unfold u5c_ln2b_line.
  apply (lnt_leT'_eq_r 0
          (Qabs (projT1
             (real_plus (real_mult (real_const ((Aface n) # 1)%Q) X)
                        (real_opp (real_const ((Bmod n) # 1)%Q))) k))
          (projT1 (real_abs
             (real_plus (real_mult (real_const ((Aface n) # 1)%Q) X)
                        (real_opp (real_const ((Bmod n) # 1)%Q)))) k)).
  - symmetry. apply real_abs_proj.
  - apply qabs_nonnegT.
Qed.

(* ============================================================ *)
(* §5 RunAlive 数值锚（n=2/3 双侧·线值闭形 vs 部分和·vm_compute 判定）        *)
(*    锚值经 Python Fractions 独立复算仲裁（头注四）。                       *)
(* ============================================================ *)

Theorem s4f_runalive_n2 :
  QltT (Qabs ((lns_bsum 2 15
        - (q_pow (2 # 1)%Q 3
            * ((Z.of_nat (bk_Qn_qtilde 2) # 1)%Q * ln2i_x 15
               - bv_p 2)%Q))%Q))
       ((1 # 1000)%Q).
Proof. reflexivity. Qed.

Theorem s4f_runalive_n2_tight :
  QltT (Qabs ((lns_bsum 2 20
        - (q_pow (2 # 1)%Q 3
            * ((Z.of_nat (bk_Qn_qtilde 2) # 1)%Q * ln2i_x 20
               - bv_p 2)%Q))%Q))
       ((1 # 100000)%Q).
Proof. reflexivity. Qed.

Theorem s4f_runalive_n3 :
  QltT (Qabs ((lns_bsum 3 20
        - (q_pow (2 # 1)%Q 4
            * ((Z.of_nat (bk_Qn_qtilde 3) # 1)%Q * ln2i_x 20
               - bv_p 3)%Q))%Q))
       ((1 # 1000)%Q).
Proof. reflexivity. Qed.

(* ============================================================ *)
(* §6 提取与假设审计（零承认复核·Obj.magic 专项检验）                        *)
(* ============================================================ *)

Separate Extraction s4f_rho.

Print Assumptions s4f_hid.
Print Assumptions s4f_content.
Print Assumptions s4f_slot4_fills.
Print Assumptions s4f_fills_slot4_of.
Print Assumptions s4f_to_weld.
Print Assumptions s4f_bsum_pos.
Print Assumptions s4f_line_readout_nonneg.
Print Assumptions s4f_runalive_n2.
Print Assumptions s4f_runalive_n2_tight.
Print Assumptions s4f_runalive_n3.
