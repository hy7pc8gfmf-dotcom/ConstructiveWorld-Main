(* ============================================================ *)
(* UpReqLogLinD.v —— 槽放电战役 #2：log_le_linear 四站点同构族扫清      *)
(*   （承 E-GIBBSD-1：席58 UpReqGibbsD.v Part A/C 缺口件跨战役复用）    *)
(* ------------------------------------------------------------------ *)
(* 四站点坐标（E-GIBBSD-1 卡；逐站 sed 实读勘误后确认同构）：            *)
(*   站点 1  UpReqU2.v         L313  Hypothesis log_le_linear          *)
(*   站点 2  UpReqFEPAttn.v    L90   Hypothesis log_le_linear          *)
(*   站点 3  UpReqTempEntropy.v L60  Hypothesis dist_log_le_linear     *)
(*   站点 4  UpFirewallReq.v   L101  Variable  dist_log_le_linear      *)
(*   四槽语句逐字同形：forall x Hx, le (log x Hx) (req_minus x one)。   *)
(* ------------------------------------------------------------------ *)
(* 形状勘误（E-GIBBSD-1 判词四站全同，逐站确认无出入）：                 *)
(*   槽输出序为接口 le（RealEnhancedReal 实例 le 字段 := real_le，      *)
(*   CW219:41130 Or 编码）；B 形引擎 real_log_le_linear_B               *)
(*   （UpRealLeB:535）输出 real_le_b（Bishop 形）。逆向桥              *)
(*   real_le_b → real_le 即 Or 形精确收口，构造性不可证                  *)
(*   （UpRealLeB 尾注台账；席58 战役 #1 同判词）。按普查 §380 落点      *)
(*   纪律，四站点放电件一律升格为「Real 实例化定理」：序以 real_le_b    *)
(*   交付，槽位由引擎直喂；若接口扩展批补 le_b 形参数位，本文件四件     *)
(*   喂定形直连（零改动）。                                             *)
(* ------------------------------------------------------------------ *)
(* 下游消费位实读（槽被喂定的下游族，逐站勘误）：                        *)
(*   站点 1：w2_gibbs_eq @UpReqU2:477 → req_gibbs_equality              *)
(*           @UpReqDist:2148（槽+log_eq_linear 双参数位）。              *)
(*   站点 2：req_attention_minimizes_free_energy_unique @UpReqFEPAttn:  *)
(*           211 → req_min_free_energy_is_boltzmann（≤ 腿，槽位）+      *)
(*           req_free_energy_min_unique（唯一腿，槽+eq_linear 双位）。   *)
(*   站点 3：件 2/件 4（L554/L592）消费 req_gibbs_inequality（槽位）；  *)
(*           件 5（L593）消费 req_gibbs_equality（槽+eq_linear 双位）。  *)
(*   站点 4：件 5/件 6（L312/L378）消费 @req_gibbs_inequality（槽位，   *)
(*           (fw_bt t1, fw_bt t2) 温度对）。                             *)
(* 阻塞裁决（兜底，逐站如实报）：                                        *)
(*   a. 四站点下游终局件（gibbs_equality / min_energy_unique）全量       *)
(*      Real 复演共同卡两缺件，本席零越权：                              *)
(*      (i)  E-GIBBSD-2 边界——下游 KL 项为 p·(log p−log q) 形           *)
(*           （req2_rel_ent @UpReqAlign2:111 / req_relative_entropy     *)
(*           同形），与 real_kl_term 规范形恒等需 log 逆消去             *)
(*           （log(inv p)==−log p），CW219 未备；                       *)
(*      (ii) req 层 fsum_zero_nonneg 的 Bishop 对位（Σd==0 + 逐点        *)
(*           0 ≤_B d ⟹ d s==0）需 In-machinery 部分和机，Part A/C 未备。*)
(*   b. 抽象 sumf 下游定理 @ 实例化路同判 ZPosD 档：real_list_sum_pos   *)
(*      携非空 datum 前提（CW219:41666），无法喂抽象 fsum_pos 参数位    *)
(*      （δ 前提形不匹配）——故站点 3/4 温度对以本文件 BTReal 节具体     *)
(*      重放（E354 装法先例）。                                          *)
(*   c. datum 非空前提为既有先例签名形（zposd_Z_pos @UpReqZPosD:82      *)
(*      「Not (enum = nil) 基座 Set 版 Not」，CW219 real_list_sum_pos    *)
(*      同位），零放大主张。                                             *)
(* ------------------------------------------------------------------ *)
(* 交付：                                                              *)
(*   [共享地基层] lld_lt_zero_sub_r / lld_le_b_zero_sub——              *)
(*     lt 减形正性 + Bishop 序减形升格（Part A 缺口延伸 2 件）。         *)
(*   [四站点喂定件] lld_{u2,fep,tempent,fw}_log_le_linear_B——四站点    *)
(*     槽的 Real 实例化 Bishop 形（引擎直喂，同构四连）。                *)
(*   [站点 1] lld_u2_gibbs_eq_step1_B——req_gibbs_equality 首步腿       *)
(*     （Hd_nonneg：0 ≤ d(s) 逐点）Bishop 形，gibbsd_gibbs_pointwise_B  *)
(*     一次喂定。                                                        *)
(*   [站点 2] FEPReal 节：softmax/boltzmann 载体对 Real 具体形          *)
(*     （base/invT/Zf/softmax/boltz 五 Definition 逐位镜像站点参数位，  *)
(*     datum 形）+ 逐点正性 3 件 + lld_fep_softmax_boltz_pointwise_B    *)
(*     （件 4 旗舰载体对的范式实例位）。                                 *)
(*   [站点 3] BTReal 节温度 Boltzmann 族（lld_btz/lld_bt 具体形 +       *)
(*     正性/归一化）+ lld_tempent_kl_nonneg_B（L554 腿 Bishop 形）+     *)
(*     lld_tempent_entropy_neg_sum_B（req_entropy_neg_sum 消费位        *)
(*     eq 伴随件，实_list_sum 层）。                                     *)
(*   [站点 4] lld_fw_kl_boltz_pair_nonneg_B——件 5/件 6 Hkl/Hkl21 腿    *)
(*     （req_gibbs_inequality 温度对）Bishop 形。                        *)
(* 复用确认（E-GIBBSD-1 卡回填）：Part A 五件（lt_add_opp_r / le_b_opp   *)
(*   / le_b_id_l / minus_flip / le_b_mult_pos_r）+ Part C 和层机六件    *)
(*   经本战役下游裁决面全数核销可复用性；Part D 范本 D0 直喂形于四站点   *)
(*   喂定件逐字复演。                                                    *)
(* 红线：Set 层零 Prop（real_le_b / real_eq / real_lt 全 Set 值； datum  *)
(*   前提为 zposd 先例口径单列）；全 Qed 闭合；零公理；既有文件零改；    *)
(*   lld_ 前缀全库防撞（建前 grep 实测零命中）。                         *)
(* 编译配方：_sqp_guard.ps1 温控包装（stage 名 lldg* 错峰）              *)
(*   coqc -Q . "" UpReqLogLinD.v（CoreN 选空闲核，零裸调）。             *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpReqGibbsD.
Require Import UpReqU2.
Require Import UpReqFEPAttn.
Require Import UpReqTempEntropy.
Require Import UpFirewallReq.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part H：共享地基层（Part A 缺口延伸 2 件）                            *)
(* ============================================================ *)

(* H1：lt 减形正性：a < c ⟹ 0 < c − a（Bishop 减形入口） *)
Lemma lld_lt_zero_sub_r : forall a c : Real,
  real_lt a c -> real_lt real_zero (real_plus c (real_opp a)).
Proof.
  intros a c Hac.
  apply (RealSetoid.real_lt_compat
           (real_plus (real_opp a) a) real_zero
           (real_plus (real_opp a) c) (real_plus c (real_opp a))).
  - apply (real_eq_trans (real_plus (real_opp a) a)
                         (real_plus a (real_opp a)) real_zero).
    + exact (real_plus_comm (real_opp a) a).
    + exact (real_plus_opp a).
  - exact (real_plus_comm (real_opp a) c).
  - exact (real_lt_plus_translate (real_opp a) a c Hac).
Qed.

(* H2：Bishop 序减形升格：a ≤_B b ⟹ 0 ≤_B b − a                          *)
(*   （站点 1 step1 腿的引擎位；swap_mid + plus_zero 换形收口）           *)
Lemma lld_le_b_zero_sub : forall a b : Real,
  real_le_b a b -> real_le_b real_zero (real_plus b (real_opp a)).
Proof.
  intros a b H. unfold real_le_b. intros eps Heps.
  apply (RealSetoid.real_lt_compat
           real_zero real_zero
           (real_plus (real_plus b eps) (real_opp a))
           (real_plus (real_plus b (real_opp a)) eps)).
  - apply real_eq_refl.
  - exact (real_eq_trans
             (real_plus (real_plus b eps) (real_opp a))
             (real_plus (real_plus b eps) (real_plus (real_opp a) real_zero))
             (real_plus (real_plus b (real_opp a)) eps)
             (RealSetoid.real_eq_plus_compat
                (real_plus b eps) (real_opp a)
                (real_plus b eps) (real_plus (real_opp a) real_zero)
                (real_eq_refl (real_plus b eps))
                (real_eq_sym (real_plus (real_opp a) real_zero)
                             (real_opp a)
                             (real_plus_zero (real_opp a))))
             (real_eq_trans
                (real_plus (real_plus b eps)
                           (real_plus (real_opp a) real_zero))
                (real_plus (real_plus b (real_opp a))
                           (real_plus eps real_zero))
                (real_plus (real_plus b (real_opp a)) eps)
                (real_plus_swap_mid b eps (real_opp a) real_zero)
                (RealSetoid.real_eq_plus_compat
                   (real_plus b (real_opp a)) (real_plus eps real_zero)
                   (real_plus b (real_opp a)) eps
                   (real_eq_refl (real_plus b (real_opp a)))
                   (real_plus_zero eps)))).
  - exact (lld_lt_zero_sub_r a (real_plus b eps) (H eps Heps)).
Qed.

(* ============================================================ *)
(* Part S：四站点喂定件（槽的 Real 实例化 Bishop 形，同构四连）           *)
(*   四槽语句逐字同形（E-GIBBSD-1 坐标 sed 实读），喂定形同构——          *)
(*   逐站独立命名钉死 provenance，勘误口径见头注。                       *)
(* ============================================================ *)

(* 站点 1（UpReqU2.v L313 log_le_linear）喂定形 *)
Lemma lld_u2_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 2（UpReqFEPAttn.v L90 log_le_linear）喂定形 *)
Lemma lld_fep_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 3（UpReqTempEntropy.v L60 dist_log_le_linear）喂定形 *)
Lemma lld_tempent_log_le_linear_B :
  forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* 站点 4（UpFirewallReq.v L101 dist_log_le_linear）喂定形 *)
Lemma lld_fw_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. exact (real_log_le_linear_B x Hx).
Qed.

(* ============================================================ *)
(* Part U2：站点 1（UpReqU2.v L313）下游首步腿                           *)
(*   槽消费位 w2_gibbs_eq（UpReqU2:477）→ req_gibbs_equality            *)
(*   （UpReqDist:2148）首步 Hd_nonneg：0 ≤ d(s) 逐点（req le 形）——     *)
(*   Bishop 形由 gibbsd_gibbs_pointwise_B（Part D 范本 D0）+ H2 升格。   *)
(*   终局复演阻塞裁决见头注 a(i)(ii)。                                   *)
(* ============================================================ *)

Lemma lld_u2_gibbs_eq_step1_B : forall (X : Type) (p q : X -> Real) (s : X)
  (Hps : real_lt real_zero (p s)) (Hqs : real_lt real_zero (q s)),
  real_le_b real_zero
    (real_plus (real_kl_term (p s) (q s) Hps Hqs)
               (real_opp (real_plus (p s) (real_opp (q s))))).
Proof.
  intros X p q s Hps Hqs.
  apply lld_le_b_zero_sub.
  exact (gibbsd_gibbs_pointwise_B X p q s Hps Hqs).
Qed.

(* ============================================================ *)
(* Part FEP：站点 2（UpReqFEPAttn.v L90）载体对具体形                     *)
(*   站点节参数（base/invT/Zf/softmax_z/boltz_z，UpReqFEPAttn:107-121）  *)
(*   逐位 Real 镜像；sumf := real_list_sum（datum 形，zposd 先例口径）； *)
(*   exp_pos_fn_setoid y == exp_neg (opp y)（CW219:66191）——站点        *)
(*   softmax 的 exp 项经 base := opp z 逐位归位（δ 透明）。              *)
(* ============================================================ *)

Section FEPReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable zz : X -> Real.
Variable TT : Real.
Variable TT_pos : real_lt real_zero TT.

Definition lld_fep_base (s : X) : Real := real_opp (zz s).
Definition lld_fep_invT : Real := real_inv_pos TT TT_pos.
Definition lld_fep_Zf : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX.

(* 辅件 1：Boltzmann 因子逐项正性（站点 Zf_pos 的 sum_pos 腿） *)
Lemma lld_fep_boltz_factor_pos : forall s : X,
  real_lt real_zero (real_exp_neg (real_mult lld_fep_invT (zz s))).
Proof.
  intro s. exact (real_exp_neg_pos (real_mult lld_fep_invT (zz s))).
Qed.

(* 配分函数正性（站点 Zf_pos 的 datum 形） *)
Lemma lld_fep_Zf_pos : real_lt real_zero lld_fep_Zf.
Proof.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult lld_fep_invT (zz s))) lX
           lld_fep_boltz_factor_pos lX_ne).
Qed.

(* softmax_z / boltz_z 逐位镜像（站点 UpReqFEPAttn:118/120） *)
Definition lld_fep_softmax (s : X) : Real :=
  real_mult (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
            (real_inv_pos lld_fep_Zf lld_fep_Zf_pos).
Definition lld_fep_boltz (s : X) : Real :=
  real_mult (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
            (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s))).

Lemma lld_fep_softmax_pos : forall s : X, real_lt real_zero (lld_fep_softmax s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)).
Qed.

Lemma lld_fep_boltz_pos : forall s : X, real_lt real_zero (lld_fep_boltz s).
Proof.
  intro s.
  exact (real_mult_positive
           (real_inv_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg (real_mult lld_fep_invT (lld_fep_base s)))
           (real_inv_pos_pos lld_fep_Zf lld_fep_Zf_pos)
           (real_exp_neg_pos (real_mult lld_fep_invT (lld_fep_base s)))).
Qed.

(* 旗舰载体对范式实例位：件 4（req_attention_minimizes_free_energy_     *)
(* unique 的 softmax/boltz 对）逐点 Gibbs 切线 Bishop 形——Part D 范本   *)
(* D0 在站点 2 载体上的 @ 全显装配。≤ 腿/唯一腿全量复演阻塞见头注 a。    *)
Lemma lld_fep_softmax_boltz_pointwise_B : forall s : X,
  real_le_b (real_plus (lld_fep_softmax s) (real_opp (lld_fep_boltz s)))
            (real_kl_term (lld_fep_softmax s) (lld_fep_boltz s)
                          (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Proof.
  intro s.
  exact (gibbsd_gibbs_pointwise_B X lld_fep_softmax lld_fep_boltz s
           (lld_fep_softmax_pos s) (lld_fep_boltz_pos s)).
Qed.

End FEPReal.

(* ============================================================ *)
(* Part BT：站点 3/4 共用温度 Boltzmann 族（Real 具体形）                 *)
(*   站点 3 tB（UpReqTempEntropy:71）/站点 4 fw_bt（UpFirewallReq:105）  *)
(*   的 real_list_sum 具体形（reqd_boltzmann_dist_temp 的 Real 重放，   *)
(*   E354 装法：抽象 fsum_pos 参数位 δ 不匹配，沿 ZPosD 先例具体重放）。 *)
(* ============================================================ *)

Section BTReal.

Variable X : Set.
Variable lX : list X.
Variable lX_ne : lX <> nil.
Variable be : X -> Real.

(* 温度配分函数 Z_t（站点 Z_temp_spec 的具体形） *)
Definition lld_btz (t : Real) (Ht : real_lt real_zero t) : Real :=
  real_list_sum X (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX.

Lemma lld_btz_pos : forall (t : Real) (Ht : real_lt real_zero t),
  real_lt real_zero (lld_btz t Ht).
Proof.
  intros t Ht.
  exact (real_list_sum_pos X
           (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s))) lX
           (fun s : X => real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           lX_ne).
Qed.

(* 温度 Boltzmann 分布（站点 tB / fw_bt 的具体形） *)
Definition lld_bt (t : Real) (Ht : real_lt real_zero t) (s : X) : Real :=
  real_mult (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)).

Lemma lld_bt_pos : forall (t : Real) (Ht : real_lt real_zero t) (s : X),
  real_lt real_zero (lld_bt t Ht s).
Proof.
  intros t Ht s.
  exact (real_mult_positive
           (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
           (real_exp_neg_pos (real_mult (real_inv_pos t Ht) (be s)))
           (real_inv_pos_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
Qed.

(* 归一化（站点 tBnorm / fw_norm 的具体形；线性提因子 + 逆元收口） *)
Lemma lld_bt_norm : forall (t : Real) (Ht : real_lt real_zero t),
  real_eq (real_list_sum X (lld_bt t Ht) lX) real_one.
Proof.
  intros t Ht.
  apply (real_eq_trans
           (real_list_sum X (lld_bt t Ht) lX)
           (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                      (lld_btz t Ht))
           real_one).
  - apply (real_eq_trans
             (real_list_sum X (lld_bt t Ht) lX)
             (real_list_sum X
                (fun s : X => real_mult (real_inv_pos (lld_btz t Ht)
                                                          (lld_btz_pos t Ht))
                                        (real_exp_neg
                                           (real_mult (real_inv_pos t Ht)
                                                      (be s)))) lX)
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))).
    + apply real_list_sum_ext. intro s.
      exact (real_mult_comm (real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
                            (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))).
    + exact (real_list_sum_linear X
               (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
               (fun s : X => real_exp_neg (real_mult (real_inv_pos t Ht) (be s)))
               lX).
  - apply (real_eq_trans
             (real_mult (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                        (lld_btz t Ht))
             (real_mult (lld_btz t Ht)
                        (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht)))
             real_one).
    + exact (real_mult_comm (real_inv_pos (lld_btz t Ht) (lld_btz_pos t Ht))
                            (lld_btz t Ht)).
    + exact (real_inv_pos_correct (lld_btz t Ht) (lld_btz_pos t Ht)).
Qed.

(* ============================================================ *)
(* 站点 3 件：L554 腿（req_gibbs_inequality p (tB t)，UpReqTempEntropy   *)
(*   件 2/件 4 槽消费位）的 Real 实例化 Bishop 形——Part D 范本 D1 在     *)
(*   站点 3 消费对 (p, lld_bt t) 上的 @ 全显装配。                       *)
(* ============================================================ *)

Lemma lld_tempent_kl_nonneg_B : forall (t : Real) (Ht : real_lt real_zero t)
  (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
  (Hnormp : real_eq (real_list_sum X p lX) real_one),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (p s) (lld_bt t Ht s)
                     (Hp s) (lld_bt_pos t Ht s)) lX).
Proof.
  intros t Ht p Hp Hnormp.
  exact (gibbsd_gibbs_inequality X lX p (lld_bt t Ht)
           Hp (lld_bt_pos t Ht) Hnormp (lld_bt_norm t Ht)).
Qed.

(* 站点 3 eq 伴随件：req_entropy_neg_sum（UpReqDist:1947，站点熵链      *)
(*   消费位）的 real_list_sum 层对位——Σ p·log p == −Σ p·(−log p)。      *)
Lemma lld_tempent_entropy_neg_sum_B : forall (p : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
          (real_opp (real_list_sum X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX)).
Proof.
  intros p Hp.
  apply (real_eq_trans
           (real_list_sum X (fun s : X => real_mult (p s) (real_log (p s) (Hp s))) lX)
           (real_list_sum X
              (fun s : X => real_opp (real_mult (p s)
                                                (real_opp (real_log (p s) (Hp s))))) lX)
           (real_opp (real_list_sum X
              (fun s : X => real_mult (p s)
                                      (real_opp (real_log (p s) (Hp s)))) lX))).
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_opp (real_mult (p s) (real_opp (real_log (p s) (Hp s)))))).
    + exact (real_eq_sym (real_opp (real_opp (real_mult (p s) (real_log (p s) (Hp s)))))
                         (real_mult (p s) (real_log (p s) (Hp s)))
                         (real_opp_opp (real_mult (p s) (real_log (p s) (Hp s))))).
    + exact (RealSetoid.real_eq_opp_compat
               (real_opp (real_mult (p s) (real_log (p s) (Hp s))))
               (real_mult (p s) (real_opp (real_log (p s) (Hp s))))
               (real_opp_mult (p s) (real_log (p s) (Hp s)))).
  - exact (real_list_sum_opp X
             (fun s : X => real_mult (p s) (real_opp (real_log (p s) (Hp s)))) lX).
Qed.

(* ============================================================ *)
(* 站点 4 件：L312/L378 腿（@req_gibbs_inequality (fw_bt t1) (fw_bt t2)，*)
(*   件 5 Hkl / 件 6 Hkl21 槽消费位）的 Real 实例化 Bishop 形——Part D    *)
(*   范本 D1 在站点 4 温度对上的 @ 全显装配。                            *)
(* ============================================================ *)

Lemma lld_fw_kl_boltz_pair_nonneg_B : forall (t1 t2 : Real)
  (Ht1 : real_lt real_zero t1) (Ht2 : real_lt real_zero t2),
  real_le_b real_zero
    (real_list_sum X
       (fun s : X => real_kl_term (lld_bt t1 Ht1 s) (lld_bt t2 Ht2 s)
                     (lld_bt_pos t1 Ht1 s) (lld_bt_pos t2 Ht2 s)) lX).
Proof.
  intros t1 t2 Ht1 Ht2.
  exact (gibbsd_gibbs_inequality X lX (lld_bt t1 Ht1) (lld_bt t2 Ht2)
           (lld_bt_pos t1 Ht1) (lld_bt_pos t2 Ht2)
           (lld_bt_norm t1 Ht1) (lld_bt_norm t2 Ht2)).
Qed.

End BTReal.

(* ============================================================ *)
(* 对账（槽放电战役 #2 交付清单，18 Qed）：                              *)
(*   共享地基 2 件：lld_lt_zero_sub_r / lld_le_b_zero_sub（Part A       *)
(*   缺口延伸：lt 减形正性 + Bishop 序减形升格）。                       *)
(*   四站点喂定件 4 件：lld_{u2,fep,tempent,fw}_log_le_linear_B          *)
(*   （四槽同构，引擎直喂；勘误口径见头注）。                            *)
(*   站点 1：lld_u2_gibbs_eq_step1_B（gibbs_equality 首步腿 Bishop 形）。*)
(*   站点 2：FEPReal 节 5 Qed（boltz_factor_pos / Zf_pos / softmax_pos / *)
(*   boltz_pos / softmax_boltz_pointwise_B）+ 5 Definition 载体镜像。    *)
(*   站点 3：BTReal 节内 lld_tempent_kl_nonneg_B +                       *)
(*   lld_tempent_entropy_neg_sum_B；BT 族 3 件（btz_pos/bt_pos/bt_norm） *)
(*   为站点 3/4 共用。                                                   *)
(*   站点 4：lld_fw_kl_boltz_pair_nonneg_B。                             *)
(* 沉淀卡（索引回填行见交付报告）：                                      *)
(*   E-LOGLIN-1：log_le_linear 四站点同构槽放电——Part A/C 复用确认       *)
(*   （E-GIBBSD-1 预言全数核销）；下游终局共同阻塞双缺件：log 逆消去     *)
(*   （E-GIBBSD-2 边界再证，p·(log p−log q) 形四站全同）+ Bishop         *)
(*   fsum_zero_nonneg（In-machinery 部分和机）；抽象 fsum_pos @ 实例化   *)
(*   δ 判词沿 ZPosD/E354 装法先例（datum 非空前提单列口径）。            *)
(*   E-LOGLIN-2：Bishop 减形升格器 lld_le_b_zero_sub（a ≤_B b ⟹         *)
(*   0 ≤_B b−a）——槽放电族通用入轨件，实_lt_zero_sub_r + swap_mid        *)
(*   收口，建议入 Part A 复用清单。                                      *)
(* ============================================================ *)
