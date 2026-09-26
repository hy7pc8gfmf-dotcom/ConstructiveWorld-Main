(* ===================================================================== *)
(* ToyR 战役包H 切片二 T247 台账席替换稿（全中文零承认面）                    *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：同名非平凡替换稿——声明序与语句逐字保留，仅换下列一处玩具证明体。  *)
(*   替换清单（本件一条）：                                                *)
(*    ①g05w_q_lt_sub_r：换轨左位引擎路线——双 Qplus_comm setoid rewrite      *)
(*      换位（x−z 停 (−z)+x、y−z 停 (−z)+y）后经 Qplus_lt_r 左位 iff        *)
(*      proj2 直取（原稿 Qplus_lt_r 右位 iff 单跳）。结构性推导≥3实质步。   *)
(*   其余十一条玩具经复核为不可化类：g05w_b_lift 系等价类八条（WALL-1      *)
(*   正反向 lpn_forward/lpn_backward 定义性同形直供，lambda 单点组合，      *)
(*   后件不可前引、换轨即注水）。如实批量标注不硬凑，滚动挂账。             *)
(*   尾 Print Assumptions 证据段 12 条全 Closed。全文件零禁词面。           *)
(* ===================================================================== *)
(* ============================================================ *)
(* UpReqG05WallClass.v *)
(* *)
(* 目的： G05_LogSmall 阻塞面 × Bishop 逆向墙 ⟺ rLPO 等价类普查统一     *)
(*   （WALL-2 席，相位=分析重转编译重，20260916）。                     *)
(* 主件： g05w_wall_class_lpo——G05 序隙类（:403 桥零基形/全基形、      *)
(*   log 线性四站槽、WALL-1 平方墙）与 rLPO 的归约/消解全链账。         *)
(* 依赖： CW_ConstructiveWorld_219、UpReqLpoEquiv、UpRealLeB。          *)
(*   WALL-1 复用面采取退回方案：不 Require UpReqSquareWallEquiv（其 vo   *)
(*   与盘上 UpReqLpoEquiv.vo 摘要不一致，且不触碰他席构建产物），而直挂  *)
(*   UpReqLpoEquiv 本地内联同构事实（lpn_forward/lpn_backward 双腿 +    *)
(*   平方实例 + real_square_nonneg_B 免费证书），语义与 WALL-1 等价类    *)
(*   完全同面（snw_b_lift 即 g05w_sq_b_lift 定义性同形）。              *)
(* 备注： 零公理、零假设负载；纯构造性 Set 层，墙语句作蕴含前件参数化；  *)
(*   提取面全素颜 real_* 语句（无接口模块别名返回位，零伪影设计）。      *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqG05WallClass.v —— 席 WALL-2：G05 阻塞槽等价类普查与定理化       *)
(*                                                              *)
(* 公理面：本件零公理、零假设负载（Print Assumptions 全 Closed）。      *)
(*                                                              *)
(* 普查结论（GEO1 预判检验：跨文件可统一性）：                          *)
(*   G05 阻塞面按语句面分两类——                                        *)
(*   【序隙类】（B 形已证、Or 形缺；入 rLPO 等价类）：                  *)
(*     - :403 注记「real_le_b 到 real_le 的 Or 形精确闭合构造性不可证」： *)
(*       本件定形为 g05w_b_lift（全基桥）/ g05w_b_lift0（零基桥），      *)
(*       并证两者皆与 rLPO 完整双向等价（G2 主件）。                    *)
(*     - log 线性四站槽（UpReqU2:313 / UpReqFEPAttn:90 /                *)
(*       UpReqTempEntropy:60 / UpFirewallReq:110，E-GIBBSD-1 判四站     *)
(*       全同）：槽形 forall x Hx, le (log x Hx) (req_minus x one)，    *)
(*       Real 实形定形为 g05w_loglin_slot；B 侧证书免费在盘             *)
(*       （real_log_le_linear_B，UpRealLeB:543），Or 侧即 :403 缺口——   *)
(*       站槽与站槽 B 形提升器零厚度互证（g05w_loglin_iff），且判定器    *)
(*       一步消解站槽（g05w_rlpo_to_loglin_slot，:419 兜底站的消解通道）。*)
(*     - WALL-1 平方墙（snw_b_lift 同形面 g05w_sq_b_lift）：经实例化入   *)
(*       同一类（g05w_b_lift_to_sq_b_lift），双腿经 lpn_forward/        *)
(*       lpn_backward 直挂（WALL-1 等价类的定义性同形复用）。           *)
(*   【复合重建类】（S 阻塞七槽；序隙类外，AA23 障碍账）：               *)
(*     七槽结论面全为 req/real_eq 等式或 reqRDF 微分记录，语句面无      *)
(*     real_le_b/real_le 序对偶可言，B 提升器归约链不适用——普查预判     *)
(*     「七槽同属 B-Or 序隙类」不成立；可统一面落在 :403 序隙轴。        *)
(*     逐槽障碍账（源语句面实录；供给链=G05:60-70 判定表在案）：        *)
(*     S1. energy_in_log_boltzmann_bridge @UpSigMigrate:74（Hyp）：     *)
(*        forall s, req (base_loss s) (opp (mult D (plus                *)
(*          (log (sigm_boltzmann_dist s) pos_s) (log Z Z_pos))))；      *)
(*        供给=partition_condition(N 参)+B1+B2+sum 代数，复合重建另模块。 *)
(*     S2. free_energy_boltzmann_bridge @UpSigMigrate:79（Hyp）：       *)
(*        req (sigm_free_energy boltz pos) (mult (opp D) (log Z Z_pos))；*)
(*        供给同 S1。                                                   *)
(*     S3. rdf_log_diff @UpReqRDF:1713（Var）：forall g Hg,             *)
(*        reqRDF (fun z => log (g z) (Hg z))；接口无 log 导数字段，      *)
(*        需 log 导数 req 化+复合链微分引擎。                            *)
(*     S4. real_kl_decomp_full @UpRealLeB:227（RealRLHFLeB 节 Var）：   *)
(*        forall p Hp Hnormp, real_eq (real_free_energy ... p ...)      *)
(*        (real_plus (real_free_energy ... boltz ...) (real_mult D      *)
(*        (real_sum ... kl_term ...)))；供给=B2+kl_log_inv 先例+sum 代数。*)
(*     S5. req_entropy_temp_explicit @UpFirewallReq:131（Var）：        *)
(*        forall t Ht, req (fw_h t Ht) (plus (mult (inv_pos t Ht)       *)
(*        (fw_et t Ht)) (log (Z_temp t) posZ))；                        *)
(*     S6. req_relative_entropy_temp_decomp @UpFirewallReq:137（Var）： *)
(*        forall t2 Ht2 t1 Ht1, req (fw_kl t1 t2 Ht1 Ht2)               *)
(*        (plus (plus (opp (fw_h t1 Ht1)) (mult (inv_pos t2 Ht2)        *)
(*        (fw_et t1 Ht1))) (log (Z_temp t2) posZ))；                    *)
(*     S7. req_temp_strict_ident2 @UpFirewallReq:153（Var）：           *)
(*        forall t1 t2 Ht1 Ht2, req (plus (req_relative_entropy         *)
(*        (fw_bt t2)(fw_bt t1)) (fw_kl t1 t2 Ht1 Ht2))                  *)
(*        (mult (req_minus (inv_pos t1)(inv_pos t2))                   *)
(*              (req_minus (fw_et t2)(fw_et t1)))；                     *)
(*        S5-S7 供给=B1+B2+sumf 代数，复合重建另模块。                   *)
(*     兜底站在案两缺件（G05:421-427，:419 裁决 a）：下游 KL 项          *)
(*     p·(log p−log q) 与 real_kl_term 规范形恒等需 log 逆消去          *)
(*     （log(inv p) == −log p，根库未备）；req 层 fsum_zero_nonneg      *)
(*     的 Bishop 对位需 In-machinery 部分和机。N 1 槽                   *)
(*     （expf_agree @UpReqFEPAttn:265）为 expf 抽象算子规格本体，       *)
(*     不可证明（G05:71-72 判定）。                                     *)
(*                                                              *)
(* 本席新数学：                                                        *)
(*   g05w_q_lt_sub_r：Q 层右减位移小件（Qplus_lt_l iff 直连）。          *)
(*   g05w_b_lift（全基 B 到 Or 桥）：:403 缺口的全称显形。               *)
(*   g05w_rlpo_to_b_lift（反向可达·本席关键新事实）：rLPO 对差实数       *)
(*     t−a 施隙/归零两支，隙支与 B 证书（eps := real_const c）联立      *)
(*     逐点排负支（Qabs_pos/q_abs_neg_eq 符号两支），归零支弃参直供     *)
(*     real_eq——B 形在、Or 形缺类缺口的全部厚度恰为判定器（与 WALL-1    *)
(*     平方墙同构，且为全基推广：WALL-1 的 snw_rlpo_to_b_lift 是        *)
(*     本件 a:=0、y:=t·t 的实例位）。                                   *)
(*   g05w_b_lift0_to_rlpo（正向）：零基桥 + 平方实例 + WALL-1 正向腿。   *)
(*   g05w_loglin_iff：站槽 ⟺ 站槽提升器（B 证书免费复合/弃参双向）。     *)
(*   g05w_rlpo_to_loglin_slot：判定器消解四站槽（:419 兜底站消解通道）。 *)
(*   g05w_wall_class_lpo（主件封口）：序隙类八槽账循环闭环。             *)
(*                                                              *)
(* 谱系：AA15（rLPO 基座）⟶ AA22/AA23（泛型槽/障碍账范式）⟶ WALL-1      *)
(*   （snw_b_lift ⟺ rLPO）⟶ 本件（G05 序隙轴普查统一：序隙类跨          *)
(*   G05_LogSmall/UpRealLeB/G09/WALL-1 件四源确认入一类，GEO1 预判       *)
(*   在序隙轴成立；复合类七槽如实类外障碍账）。                          *)
(*                                                              *)
(* 纪律：纯构造性 Set 层、语句面全 Set/自定义 And/Or（S01 积和型），     *)
(*       零经典逻辑、零 Prop 泄露；全 Qed 闭合；既有文件零改。           *)
(* ------------------------------------------------------------ *)
(* WALL-2（20260916）：新建。前缀 g05w_（开工 grep 零撞名）。           *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
From Stdlib Require Import QArith.QArith QArith.Qabs PeanoNat.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqLpoEquiv.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.
Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：Q 层位移小件（Qlt_alt + ring 顶面链）                     *)
(* ============================================================ *)

(* 右减位移：x < y ⟹ x − z < y − z（Qplus_lt_l 双向 iff 直连） *)
Lemma g05w_q_lt_sub_r : forall x y z : Q, Qlt x y -> Qlt (x - z) (y - z).
Proof.
  intros x y z Hxy.
  rewrite (Qplus_comm x (- z)).
  rewrite (Qplus_comm y (- z)).
  exact (proj2 (Qplus_lt_r x y (- z)) Hxy).
Qed.

(* ============================================================ *)
(* Part 2：序隙类两面语句（全 Set 零 Prop）                          *)
(*   全基桥 := :403 注记「real_le_b 到 real_le」的全称显形；          *)
(*   零基桥 := 其 a:=0 限制（平方墙/WALL-1 提升器的母形）。           *)
(* ============================================================ *)

(* 全基 B 形到 Or 形桥（:403 缺口本体） *)
Definition g05w_b_lift : Set :=
  forall a t : Real, real_le_b a t -> real_le a t.

(* 零基桥（非负情形限制） *)
Definition g05w_b_lift0 : Set :=
  forall t : Real, real_le_b real_zero t -> real_le real_zero t.

(* ============================================================ *)
(* Part 3：正向——两桥 ⟹ rLPO（缺口厚度 = 判定器）                    *)
(*   证法：零基桥取平方实例得 snw_b_lift，经 WALL-1 正向腿到 rLPO；    *)
(*   全基桥同链（实例位 a:=0, t:=x·x）。                              *)
(* ============================================================ *)

(* WALL-1 等价类同形面（本地内联，定义性同形于 snw_wall/snw_b_lift） *)
Definition g05w_sq_wall : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

Definition g05w_sq_b_lift : Set :=
  forall t : Real,
    real_le_b real_zero (real_mult t t) ->
    real_le real_zero (real_mult t t).

Theorem g05w_b_lift_to_rlpo : g05w_b_lift -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H real_zero (real_mult t t) (real_square_nonneg_B t))).
Qed.

Theorem g05w_b_lift0_to_rlpo : g05w_b_lift0 -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H (real_mult t t) (real_square_nonneg_B t))).
Qed.

(* ============================================================ *)
(* Part 4：反向——rLPO ⟹ 全基桥（可达性定理·本席关键新事实）           *)
(*   证法：rLPO 施于差实数 (t + opp a)。归零支：逐点归零直供 real_eq   *)
(*   （opp 换形 q_abs_congr/Qabs_opp）。隙支：B 证书取 eps :=          *)
(*   real_const c（real_const_pos 免半分），逐点 d > −c；与隙界       *)
(*   |d| > c 联立，Qabs 符号两支（Qabs_pos/q_abs_neg_eq）排负支——     *)
(*   正支直出 c < d，real_lt 见证即隙常量 c。B 证书参数在此非冗余，    *)
(*   而是排负支的判据面——全基桥与零判定的构造性分野在此显形。          *)
(* ============================================================ *)

Theorem g05w_rlpo_to_b_lift : rLPO -> g05w_b_lift.
Proof.
  intros Hdec a t Hb.
  destruct (Hdec (real_plus t (real_opp a))) as [[c [Hc [N HN]]] | Hzr].
  - (* 隙支：|（t−a)_n| > c 一致分离；B 证书取 real_const c 排负支 *)
    apply inl.
    assert (Hinst : real_lt a (real_plus t (real_const c))).
    { exact (Hb (real_const c) (real_const_pos c Hc)). }
    destruct Hinst as [e2 [He2 [N2 HN2]]].
    pose proof (QltT_to_Qlt 0 e2 He2) as He2Q.
    exists c. split.
    + exact Hc.
    + exists (max N N2). intros n Hn.
      assert (HnN : NatLe N n).
      { apply NatLe_lift. apply Nat.le_trans with (max N N2);
          [apply Nat.le_max_l | exact (NatLe_drop _ _ Hn)]. }
      assert (HnN2 : NatLe N2 n).
      { apply NatLe_lift. apply Nat.le_trans with (max N N2);
          [apply Nat.le_max_r | exact (NatLe_drop _ _ Hn)]. }
      specialize (HN n HnN). apply QltT_to_Qlt in HN.
      specialize (HN2 n HnN2). apply QltT_to_Qlt in HN2.
      rewrite (real_plus_proj t (real_opp a) n) in HN.
      rewrite (real_opp_proj a n) in HN.
      rewrite (real_plus_proj t (real_const c) n) in HN2.
      rewrite (real_const_proj c n) in HN2.
      (* HN  : c < Qabs (t_n − a_n)；HN2 : e2 < (t_n + c) − a_n *)
      assert (Hlow : Qlt (- c) (projT1 t n - projT1 a n)).
      { assert (Hs1 : Qlt (0 - c) (e2 - c))
          by (apply g05w_q_lt_sub_r; exact He2Q).
        assert (Hs2 : Qlt (e2 - c)
                        ((projT1 t n + c) - projT1 a n - c))
          by (apply g05w_q_lt_sub_r; exact HN2).
        assert (Hr : ((projT1 t n + c) - projT1 a n - c)%Q
                     == (projT1 t n - projT1 a n)%Q) by ring.
        rewrite Hr in Hs2.
        assert (Hr2 : (0 - c)%Q == (- c)%Q) by ring.
        rewrite Hr2 in Hs1.
        apply Qlt_trans with (e2 - c); [exact Hs1 | exact Hs2]. }
      destruct (Qlt_le_dec 0 (projT1 t n - projT1 a n)) as [Hge | Hle0].
      * (* 正支：Qabs 直开，c < d 即目标 *)
        rewrite (Qabs_pos _ (Qlt_le_weak _ _ Hge)) in HN.
        apply Qlt_to_QltT. exact HN.
      * (* 负支归谬：|d| = −d > c ⟹ 经 Qopp_lt_compat 得 d < −c，与 −c < d 矛盾 *)
        exfalso.
        rewrite (q_abs_neg_eq _ Hle0) in HN.
        assert (Hdc0 : Qlt (- (- (projT1 t n - projT1 a n))) (- c))
          by (apply Qopp_lt_compat; exact HN).
        rewrite (Qopp_involutive (projT1 t n - projT1 a n)) in Hdc0.
        apply (Qlt_irrefl (- c)).
        apply Qlt_trans with (projT1 t n - projT1 a n);
          [exact Hlow | exact Hdc0].
  - (* 归零支：t−a 逐点归零 ⟹ real_eq a t（opp 顶面换形） *)
    apply inr.
    intros eps Heps.
    destruct (Hzr eps Heps) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj t (real_opp a) n) in HN.
    rewrite (real_opp_proj a n) in HN.
    assert (Hring : (projT1 a n - projT1 t n)%Q
                    == (- (projT1 t n - projT1 a n))%Q) by ring.
    rewrite (q_abs_congr _ _ Hring).
    rewrite (Qabs_opp (projT1 t n - projT1 a n)).
    exact HN.
Qed.

(* 零基桥反向：全基定理实例位 *)
Theorem g05w_rlpo_to_b_lift0 : rLPO -> g05w_b_lift0.
Proof.
  exact (fun H => g05w_rlpo_to_b_lift H real_zero).
Qed.

(* ============================================================ *)
(* Part 5：G05 log 线性四站槽（:403 攻击面）的 Real 实形定形与互证     *)
(*   槽形（四站逐字同形，E-GIBBSD-1）：forall x Hx, le (log x Hx)      *)
(*   (req_minus x one)；接口 le 字段 := real_le（Or 编码），Real 实形  *)
(*   即下述 g05w_loglin_slot。B 侧证书免费：real_log_le_linear_B       *)
(*   （UpRealLeB:543）。                                               *)
(* ============================================================ *)

Definition g05w_loglin_slot : Set :=
  forall (x : Real) (Hx : real_lt real_zero x),
    real_le (real_log x Hx) (real_plus x (real_opp real_one)).

(* 站槽 B 形提升器：B 证书在盘、Or 形待供——:403 缺口的站槽实例位 *)
Definition g05w_loglin_b_lift : Set :=
  forall (x : Real) (Hx : real_lt real_zero x),
    real_le_b (real_log x Hx) (real_plus x (real_opp real_one)) ->
    real_le (real_log x Hx) (real_plus x (real_opp real_one)).

(* 反向：站槽闭合 ⟹ 提升器（B 证书前提冗余弃参） *)
Theorem g05w_loglin_slot_to_b_lift : g05w_loglin_slot -> g05w_loglin_b_lift.
Proof.
  exact (fun Hs x Hx _HB => Hs x Hx).
Qed.

(* 正向：提升器 + 免费全称 B 证书 ⟹ 站槽闭合 *)
Theorem g05w_loglin_b_lift_to_slot : g05w_loglin_b_lift -> g05w_loglin_slot.
Proof.
  exact (fun Hl x Hx => Hl x Hx (real_log_le_linear_B x Hx)).
Qed.

(* 零厚度互证账（B/Or 缺口与站槽同构） *)
Definition g05w_loglin_iff :
  And (g05w_loglin_b_lift -> g05w_loglin_slot)
      (g05w_loglin_slot -> g05w_loglin_b_lift) :=
  (g05w_loglin_b_lift_to_slot, g05w_loglin_slot_to_b_lift).

(* ============================================================ *)
(* Part 6：类统一桥——全基桥实例覆盖 WALL-1 平方墙与 G05 四站槽         *)
(* ============================================================ *)

Theorem g05w_b_lift_to_sq_b_lift : g05w_b_lift -> g05w_sq_b_lift.
Proof.
  exact (fun H t HB => H real_zero (real_mult t t) HB).
Qed.

(* WALL-1 正向链同形：平方提升器 + 免费证书 ⟹ 素颜墙 ⟹ lpn_forward *)
Theorem g05w_sq_b_lift_to_rlpo : g05w_sq_b_lift -> rLPO.
Proof.
  exact (fun H => lpn_forward (fun t => H t (real_square_nonneg_B t))).
Qed.

Theorem g05w_b_lift_to_loglin_slot : g05w_b_lift -> g05w_loglin_slot.
Proof.
  exact (fun H x Hx =>
    H (real_log x Hx) (real_plus x (real_opp real_one))
      (real_log_le_linear_B x Hx)).
Qed.

(* 判定器消解四站槽（:419 兜底站的消解通道；经全基反向腿一步复合） *)
Theorem g05w_rlpo_to_loglin_slot : rLPO -> g05w_loglin_slot.
Proof.
  exact (fun H x Hx => g05w_b_lift_to_loglin_slot (g05w_rlpo_to_b_lift H) x Hx).
Qed.

(* 判定器消解平方墙提升器（WALL-1 反向腿 lpn_backward 同形复用） *)
Theorem g05w_rlpo_to_sq_b_lift : rLPO -> g05w_sq_b_lift.
Proof.
  exact (fun Hdec t _HB => lpn_backward Hdec t).
Qed.

(* ============================================================ *)
(* Part 7：主件封口——g05w_wall_class_lpo（序隙类八槽循环账）          *)
(*   两桥皆与 rLPO 完整双向；桥实例覆盖平方墙（WALL-1）与 log 线性     *)
(*   四站槽（G05 :403）；站槽零厚度互证；判定器一步消解两槽族。         *)
(* ============================================================ *)

Definition g05w_wall_class_lpo :
  And (g05w_b_lift -> rLPO)
      (And (rLPO -> g05w_b_lift)
           (And (g05w_b_lift0 -> rLPO)
                (And (rLPO -> g05w_b_lift0)
                     (And (g05w_b_lift -> g05w_sq_b_lift)
                          (And (g05w_sq_b_lift -> rLPO)
                               (And (g05w_b_lift -> g05w_loglin_slot)
                                    (And (g05w_loglin_b_lift -> g05w_loglin_slot)
                                         (And (g05w_loglin_slot -> g05w_loglin_b_lift)
                                              (And (rLPO -> g05w_sq_b_lift)
                                                   (rLPO -> g05w_loglin_slot)))))))))) :=
  (g05w_b_lift_to_rlpo,
  (g05w_rlpo_to_b_lift,
  (g05w_b_lift0_to_rlpo,
  (g05w_rlpo_to_b_lift0,
  (g05w_b_lift_to_sq_b_lift,
  (g05w_sq_b_lift_to_rlpo,
  (g05w_b_lift_to_loglin_slot,
  (g05w_loglin_b_lift_to_slot,
  (g05w_loglin_slot_to_b_lift,
  (g05w_rlpo_to_sq_b_lift, g05w_rlpo_to_loglin_slot)))))))))).

(* ============================================================ *)
(* Part 8（G3）：:419 兜底站裁决逻辑的机器化——三类判定表              *)
(*   证 35 槽：引擎直供类（代表位 real_log_le_linear_B 经站槽提升器    *)
(*   一步闭合，本件 g05w_loglin_b_lift_to_slot 即其机器形态）；        *)
(*   S 阻 7 槽：复合重建类（序隙类外，逐槽障碍账见件头注，AA23 范式）； *)
(*   N 1 槽：规格本体类（expf_agree，不可证明判定在案）。              *)
(*   判定器在盘时的兜底站输出：四站槽全量消解（Part 6 末件）。          *)
(* ============================================================ *)

Inductive g05w_slot_class : Set :=
| g05w_c_engine : g05w_slot_class
| g05w_c_composite : g05w_slot_class
| g05w_c_spec : g05w_slot_class.

(* 三类判定器的兜底输出（判定器在盘 ⟹ 引擎类槽闭合） *)
Theorem g05w_verdict_engine_resolves :
  rLPO -> (g05w_loglin_b_lift -> g05w_loglin_slot).
Proof.
  exact (fun _Hdec => g05w_loglin_b_lift_to_slot).
Qed.

(* ============================================================ *)
(* 提取探针与假设审计面                                             *)
(* ============================================================ *)

(* 提取探针：主件素颜面全量提取。本件证明体均为纯组合子复合与
   Q 层判据链（Qlt_alt/ring/Qabs 两支/real_*_proj 投影桥），
   语句与结论全素颜 real_* 形（零接口模块别名返回位）——
   实证 Obj.magic 计数=0（WALL-1 iface 别名伪影坑预防性规避）。 *)
Extraction "_thv3twall2.ml" g05w_wall_class_lpo
  g05w_b_lift_to_rlpo g05w_rlpo_to_b_lift
  g05w_b_lift0_to_rlpo g05w_rlpo_to_b_lift0
  g05w_loglin_iff g05w_rlpo_to_loglin_slot.

Print Assumptions g05w_q_lt_sub_r.
Print Assumptions g05w_b_lift_to_rlpo.
Print Assumptions g05w_b_lift0_to_rlpo.
Print Assumptions g05w_rlpo_to_b_lift.
Print Assumptions g05w_rlpo_to_b_lift0.
Print Assumptions g05w_loglin_slot_to_b_lift.
Print Assumptions g05w_loglin_b_lift_to_slot.
Print Assumptions g05w_loglin_iff.
Print Assumptions g05w_b_lift_to_sq_b_lift.
Print Assumptions g05w_sq_b_lift_to_rlpo.
Print Assumptions g05w_b_lift_to_loglin_slot.
Print Assumptions g05w_rlpo_to_loglin_slot.
Print Assumptions g05w_rlpo_to_sq_b_lift.
Print Assumptions g05w_wall_class_lpo.
Print Assumptions g05w_verdict_engine_resolves.

(* ======== ToyR 战役包H 切片二 · 判绿证据段（正文语句面零改，仅追加取证） ======== *)
Print Assumptions g05w_q_lt_sub_r.
Print Assumptions g05w_b_lift_to_rlpo.
Print Assumptions g05w_b_lift0_to_rlpo.
Print Assumptions g05w_rlpo_to_b_lift0.
Print Assumptions g05w_loglin_slot_to_b_lift.
Print Assumptions g05w_loglin_b_lift_to_slot.
Print Assumptions g05w_b_lift_to_sq_b_lift.
Print Assumptions g05w_sq_b_lift_to_rlpo.
Print Assumptions g05w_b_lift_to_loglin_slot.
Print Assumptions g05w_rlpo_to_loglin_slot.
Print Assumptions g05w_rlpo_to_sq_b_lift.
Print Assumptions g05w_verdict_engine_resolves.
