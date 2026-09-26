(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(*   正文系 Main/Live 基准件全文，仅换下列证明体；定理名/语句面/Require 面/  *)
(*   声明名序与原件零改动，头注与本节为增补。纪律：全中文零承认件（承认     *)
(*   命令四类与弃证字面零出现），纯构造性 Set 层，真 Qed，零新增 Require。   *)
(*   一、ralt_lt_plus_translate：同族导出件换轨——弃 B 桥直连加双 comm 运输， *)
(*       改使用先落之 1.4 导出件 ralt_lt_plus_compat_le_lt（le_refl b 填腿）， *)
(*       零交换律运输直达（单路引擎面收窄至同族件单点）。 *)
(*   二、ralt_minus_plus_common：脱钩独立重演——弃 req_minus_plus_congr 单点， *)
(*       req_minus 载体展开后四引擎链原地重演：req_opp_plus 负号分配、 *)
(*       req_plus_swap_mid 中项换序、plus_opp 对消、req_plus_zero_l 零元闭合。 *)
(*   三、ralt_log_exp_neg：对数桥脱钩——弃 req_log_exp_neg 引擎单点，经本节 *)
(*       自持假设位 ralt_log_inv_exp_neg_req 与 log_inv_log 桥面对接： *)
(*       req_opp_compat 双腿运输、req_double_neg 双负闭合、req_trans 双段链。 *)
(*   留记（如实登记不强造）： *)
(*   ralt_mult_lt_compat_l：lt_mult_compat 系严格乘法唯一引擎，comm 运输 *)
(*       位置唯一（左形必经双 comm），单路唯一形，不化。 *)
(*   ralt_lt_plus_compat_le_lt：B 桥 le_lt 导出复刻本体（comm 运输即导出 *)
(*       路线全体，单桥假设位无第二引信），不化。 *)
(*   ralt_dpo_reward_diff_is_log_ratio_diff：delta 透明件（ralt_dir 定义即 *)
(*       beta·log_ratio，req_minus 自反即装法定义同构），不化。 *)
(*   ralt_dpo_pair_denom_pos：req_sigmoid_denom_pos 系分母正性唯一见证， *)
(*       单路唯一形，不化。 *)
(*   ralt_pi_star_implicit_reward_diff：ralt_dpo_reward_relative_exact 单点 *)
(*       喂定，独立重演＝其 15 步链体复制注水，留记。 *)
(*   ralt_sigmoid_strict_inc：exp_neg_decr＋B 桥 le_lt＋区1 消解件三段装配 *)
(*       序唯一（内行严格化仅 le_lt 单桥），留记。 *)
(*   ralt_real_const_req_qleT/ralt_real_const_req_eq_bool：区5 接口投影喂 *)
(*       定，连接引理唯一（QleT_to_Qle/Qeq_bool_iff 单入口），不化。 *)
(* ============================================================ *)
(* ============================================================ *)
(* UpReqAlignRestA.v *)
(* *)
(* 目的： 对齐族剩余段 A：DPO 奖励差与对数比面。 *)
(* 主件： ralt_dpo_reward_recovers / ralt_dpo_reward_diff_is_log_ratio_diff 与 ralt_log_pi_star。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign。 *)
(* 备注： 奖励、温度、逐点正性以 Variable 前提给出；对数比差为显式构造。 *)
(* ============================================================ *)

(*
   源文件：签名迁移规划书.md（组 3 余量清单）
     pi_star_req/req_pi_star_pos/sigmoid_req 系成品——KLProjection 16 对位批 3 件已建，
   Set 层语句（req/lt/le 均 Set 值，零 Prop 泄露）。
   ----------------------------------------------------------------
   余件清单（grep 实证：UpReqAlign/2/3、UpReqAlgebra、UpReqDist、UpSigMigrate2
   全部 decl 扫描后扣除已结果件；基座坐标 = ）：
   [区1 DPO Real 闭合块 L38524-39193（DpoPreludeMain/DpoPrelude+LogMono 14 件）]
       Id 层 L21013 诚实 Variable，req 接口有 lt_mult_compat/inv_pos_correct 字段，
       ralt_lt_plus_compat_le_lt（B 桥导出，批 1 同款复刻）+ B 桥假设位 2
       （ralt_lt_plus_compat_lt_le/ralt_log_lt_mono，Id L21020/L21024 同位——
       各件自持假设位=既定纪律）；账面冻结 7（Q 层 5 件 log_seq_pair_bound/_r/
       q_three_sum/q_lt_half_half/q_abs_diff_gt_neg 双层并行 + Real 锚点深链 2 件
       log_mid_sign/log_mid_diff 引用 log_seq/log_lower/log_upper 具体机，
       接口不可表达）；账面同位 1（real_mult_lt_compat 本体 = 接口字段
       lt_mult_compat，字段即 req 同位不重建）。
   [区2 dpo_reward 簇 L19086-19850] ralt_log_pi_star（真证：log_mult 双层 +
       （闭式基线偏移真证）+ ralt_dpo_reward_relative_exact（基线消去真证）+
       ralt_dpo_reward_diff_is_log_ratio_diff（δ 透明件）。
   [区3 preference 節 L20101-20258] ralt_implicit_reward_diff/dpo_pair_loss/_star
       定义 3 + denom_pos（平凡直引批 3 req_sigmoid_denom_pos）+
       total_loss 簇冻结（fold_right_ext 载体，批 3 登记表 4 双层并行）。
   [区4 sigmoid/DPO 损失簇 L20880-21059] ralt_log_ratio/dpo_loss_pair 定义 +
       dpo_loss_at_pi_star（真证：log_pi_star 消去 Z/π_ref + β·(1/β)=1 吸收）+
       sigmoid_strict_inc（真证：**使用区1消解件**）+ dpo_loss_pi_star_bounded
       （真证：log_lt_mono B 桥使用）；sigmoid_denom_pos/sigmoid_pos/
   [区5 KL 投影区合并块余件 L95420-95508：A2 Q↔Real 桥 6 件] req 系签名定位
       （instance RealEnhancedReal 的 req/lt/le 投影 = real_eq/real_lt/real_le，
       与升级包 1-3（seq_eqb/in_seq/count_true/sf_*）nat/list/Q 层冻结；
       KLProjection Section 16 对位批 3 件已建（req_Z_aud_le_one 等，不重复）。
   ----------------------------------------------------------------
   诚实签名变化登记表（规划书 §7.4）：
     的 req 版携带分母正性显式位（区3 定义前置 denom 引理）。
   2. minus 载体 = UpReqAlgebra.req_minus（δ 透明同形 Id minus）。
   3. B 类桥假设位 4（本节自持，Id 同位）：ralt_lt_plus_compat_lt_le /
     ralt_log_lt_mono（Id L21020/L21024 Variable 同形）+ ralt_log_req_compat /
     ralt_log_inv_exp_neg_req（批 1 ReqLogBridge 接口缺口桥同形）。
   4. 冻结账（双层并行）：区1 Q 层/锚点深链 7 件 + total_loss fold 簇 + 区5
     A1 桥/升级包（nat/list/Q 层 Id，规划书 §1.1 边界 2）。
   ---------------------------------------------------------------- *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
Import RealInterfaceEnhancedMod.

(* ============================================================ *)
(* ReqRestACore：DPO/Preference 余件主体节                        *)
(*   （节参数与批 3 ReqAlignCore 逐位对齐 + preference 三参）      *)
(* ============================================================ *)
Section ReqRestACore.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis ralt_sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
(* T5 扩槽（ B39 后，T4R §⑤-A1 配方）：pi_star_req canonical 签名顶入
   sum_pos 位——本节原无此槽，仿 G12 W 方增补；Z_align_pos 槽闲置保留
  （log/inv_pos 内部供给位仍在用，防下游语句面引用断裂）。 *)
Hypothesis ralt_sum_pos :
  forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
Variable reward : S -> R.
Variable beta : R.
Variable beta_pos : lt zero beta.
Variable pi_ref : S -> R.
Variable pi_ref_pos : forall s : S, lt zero (pi_ref s).
Variable Z_align_pos : lt zero (Z_align_req S sumf reward beta beta_pos pi_ref).

Hypothesis ralt_lt_plus_compat_lt_le :
  forall a b c d : R, lt a b -> le c d -> lt (plus a c) (plus b d).
Hypothesis ralt_log_lt_mono :
  forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
    lt a b -> lt (log a Ha) (log b Hb).
(* ---- 接口缺口桥（批 1 ReqLogBridge 同位） ---- *)
Hypothesis ralt_log_req_compat :
  forall (x y : R) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Hypothesis ralt_log_inv_exp_neg_req :
  forall x : R, req (log_inv (exp_neg x) (exp_neg_pos x)) x.

(* ============ 区1：DPO Real 闭合块 req 化（基座 L38524-39193） ============ *)


Lemma ralt_log_exp_neg : forall x : R,
  req (log (exp_neg x) (exp_neg_pos x)) (opp x).
Proof.
  intro x.
  exact (req_trans (log (exp_neg x) (exp_neg_pos x))
                   (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                   (opp x)
                   (req_sym (opp (opp (log (exp_neg x) (exp_neg_pos x))))
                            (log (exp_neg x) (exp_neg_pos x))
                            (req_double_neg (log (exp_neg x) (exp_neg_pos x))))
                   (req_opp_compat (opp (log (exp_neg x) (exp_neg_pos x))) x
                      (req_trans (opp (log (exp_neg x) (exp_neg_pos x)))
                                 (log_inv (exp_neg x) (exp_neg_pos x))
                                 x
                                 (req_sym (log_inv (exp_neg x) (exp_neg_pos x))
                                          (opp (log (exp_neg x) (exp_neg_pos x)))
                                          (log_inv_log (exp_neg x) (exp_neg_pos x)))
                                 (ralt_log_inv_exp_neg_req x)))).
Qed.

(* 1.1 real_mult_lt_compat_l 同位（基座 L38577）：左乘严格保序。
   真证：右形式字段 lt_mult_compat + req_lt_compat 交换律运输（平凡直引级） *)
Lemma ralt_mult_lt_compat_l : forall a b c : R,
  lt a b -> lt zero c -> lt (mult c a) (mult c b).
Proof.
  intros a b c Hab Hc.
  apply (req_lt_compat (mult a c) (mult c a) (mult b c) (mult c b)
                       (mult_comm a c) (mult_comm b c)).
  exact (lt_mult_compat a b c Hc Hab).
Qed.

(* 1.2 real_inv_pos_lt_contra 同位（基座 L38589；Id 层 L21013 诚实 Variable）：
   inv 反单调 —— **B 类假设位消解**。真证链：
   inv b ≡ (inv a·a)·inv b < (inv a·b)·inv b ≡ inv a
   （两端 inv_pos_correct 吸收，中段 lt_mult_compat 两次 + 交换运输） *)
Lemma ralt_inv_pos_lt_contra : forall (a b : R) (Ha : lt zero a) (Hb : lt zero b),
  lt a b -> lt (inv_pos b Hb) (inv_pos a Ha).
Proof.
  intros a b Ha Hb Hab.
  set (ia := inv_pos a Ha).
  set (ib := inv_pos b Hb).
  assert (Hia1 : req (mult ia a) one).
  { exact (req_trans (mult ia a) (mult a ia) one (mult_comm ia a) (inv_pos_correct a Ha)). }
  assert (Hib1 : req (mult b ib) one).
  { exact (inv_pos_correct b Hb). }
  (* 中点左端：ib ≡ (ia·a)·ib *)
  assert (Hmid : req (mult (mult ia a) ib) ib).
  { apply (req_trans (mult (mult ia a) ib) (mult one ib) ib).
    - exact (req_mult_compat (mult ia a) one ib ib Hia1 (req_refl ib)).
    - exact (req_trans (mult one ib) (mult ib one) ib (mult_comm one ib) (mult_one ib)). }
  (* 中段严格：lt (ia·a) (ia·b)（lt_mult_compat 左乘 + 交换运输） *)
  assert (Hlt1 : lt (mult ia a) (mult ia b)).
  { apply (req_lt_compat (mult a ia) (mult ia a) (mult b ia) (mult ia b)
                         (mult_comm a ia) (mult_comm b ia)).
    exact (lt_mult_compat a b ia (inv_pos_pos a Ha) Hab). }
  assert (Hltmid : lt (mult (mult ia a) ib) (mult (mult ia b) ib)).
  { exact (lt_mult_compat (mult ia a) (mult ia b) ib (inv_pos_pos b Hb) Hlt1). }
  (* 中点右端：(ia·b)·ib ≡ ia·(b·ib) ≡ ia·1 ≡ ia *)
  assert (Hright : req (mult (mult ia b) ib) ia).
  { apply (req_trans (mult (mult ia b) ib) (mult ia (mult b ib)) ia).
    - exact (req_sym (mult ia (mult b ib)) (mult (mult ia b) ib) (mult_assoc ia b ib)).
    - apply (req_trans (mult ia (mult b ib)) (mult ia one) ia).
      + exact (req_mult_compat ia ia (mult b ib) one (req_refl ia) Hib1).
      + exact (mult_one ia). }
  apply (lt_id_r ib (mult (mult ia b) ib) ia Hright).
  exact (lt_id_l ib (mult (mult ia a) ib) (mult (mult ia b) ib)
                   (req_sym (mult (mult ia a) ib) ib Hmid) Hltmid).
Qed.

(* 1.3 real_lt_plus_compat_lt_le 同位：B 类桥假设位 ralt_lt_plus_compat_lt_le
   （Id L21020 Variable 同形；UpReqAlgebra ReqStrictOrderBridge 同位，本节自持） *)
(* 1.4 real_lt_plus_compat_le_lt 同位（基座 L38654）：B 桥导出（批 1 同款复刻：
   交换律 + req_lt_compat 运输，零新假设） *)
Lemma ralt_lt_plus_compat_le_lt :
  forall a b c d : R, le a b -> lt c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  apply (req_lt_compat (plus c a) (plus a c) (plus d b) (plus b d)
                       (plus_comm c a) (plus_comm d b)).
  exact (ralt_lt_plus_compat_lt_le c d a b Hcd Hab).
Qed.

(* 1.5 real_lt_plus_translate 同位（基座 L38635）：加性平移。
   真证（零新假设）：B 桥 lt_le 形 + le_refl + 交换律运输 *)
Lemma ralt_lt_plus_translate : forall (b c d : R),
  lt c d -> lt (plus b c) (plus b d).
Proof.
  intros b c d Hcd.
  exact (ralt_lt_plus_compat_le_lt b b c d (le_refl b) Hcd).
Qed.

(* 1.6 minus_plus_common 同位（基座 L19692）：共同被加项消去。
   平凡直引：批 1 req_minus_plus_congr 即同位件（req_minus δ 载体） *)
Lemma ralt_minus_plus_common : forall A B C : R,
  req (req_minus (plus A B) (plus A C)) (req_minus B C).
Proof.
  intros A B C. unfold req_minus.
  apply (req_trans (plus (plus A B) (opp (plus A C)))
                   (plus (plus A B) (plus (opp A) (opp C)))
                   (plus B (opp C))).
  - exact (req_plus_compat (plus A B) (plus A B)
                           (opp (plus A C)) (plus (opp A) (opp C))
                           (req_refl (plus A B)) (req_opp_plus A C)).
  - apply (req_trans (plus (plus A B) (plus (opp A) (opp C)))
                     (plus (plus A (opp A)) (plus B (opp C)))
                     (plus B (opp C))).
    + exact (req_plus_swap_mid A B (opp A) (opp C)).
    + apply (req_trans (plus (plus A (opp A)) (plus B (opp C)))
                       (plus zero (plus B (opp C)))
                       (plus B (opp C))).
      * exact (req_plus_compat (plus A (opp A)) zero
                               (plus B (opp C)) (plus B (opp C))
                               (plus_opp A) (req_refl (plus B (opp C)))).
      * exact (req_plus_zero_l (plus B (opp C))).
Qed.

(* 1.7 real_log_lt_mono 同位：B 类桥假设位 ralt_log_lt_mono
   （Id L21024 Variable 同形；接口仅 log_le_linear_eps，严格形不可导出） *)

(* ============ 区2：dpo_reward 簇 req 化（基座 L19086-19850） ============ *)

(* 对数几率比（基座 log_ratio L20880 req 同形；log 前提化携带见证） *)
Definition ralt_log_ratio (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s : S) : R :=
  req_minus (log (pi s) (Hpi s)) (log (pi_ref s) (pi_ref_pos s)).

(* DPO 隐式奖励（基座 dpo_implicit_reward L19086 req 同形） *)
Definition ralt_dir (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s : S) : R :=
  mult beta (ralt_log_ratio pi Hpi s).

(* π* 逐点正性（使用批 3 成品；见证固定形态） *)
Definition ralt_pistar_pos (s : S)
  : lt zero (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) :=
  req_pi_star_pos S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s.

(* pi* abbreviation (delta transparent) *)
Definition ralt_pistar : S -> R :=
  pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos.

(* T4R2 桥（ B39 后）：canonical π* 闭式（UpReqAlign.Z_align_pos 内部前置引理
   实例）与本节 Z_align_pos 槽闭式的逐点 req——两者仅差 inv_pos 的正性证明参，
   非转换面（T4R 经验卡 canonical-vs-pinned 墙）；Close uac_pstr_cross 同款：
   req_mult_cancel_l + inv_pos_correct 双折运输。 *)
Lemma ralt_pistar_cross : forall s : S,
  req (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
      (mult (inv_pos (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos)
            (mult (pi_ref s)
                  (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s)))))).
Proof.
  intro s.
  unfold pi_star_req.
  apply (req_mult_compat _ _ _ _
    (req_mult_cancel_l (Z_align_req S sumf reward beta beta_pos pi_ref) _ _
       (@UpReqAlign.Z_align_pos R RIS S sumf ralt_sum_pos reward beta beta_pos
          pi_ref pi_ref_pos)
       (req_trans _ _ _
          (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
             (@UpReqAlign.Z_align_pos R RIS S sumf ralt_sum_pos reward beta beta_pos
                pi_ref pi_ref_pos))
          (req_sym _ _
             (inv_pos_correct (Z_align_req S sumf reward beta beta_pos pi_ref)
                Z_align_pos))))
    (req_refl (mult (pi_ref s)
                    (exp_neg (opp (mult (inv_pos beta beta_pos) (reward s))))))).
Qed.

(* 2.1 log_pi_star 同位（基座 L18812）：log π*(s) ≡ -log Z + (log π_ref(s) + r(s)/β)。
   ralt_log_exp_neg + double_neg 折叠；T4R2：闭式见证据 ralt_pistar_cross 运输 *)
Lemma ralt_log_pi_star : forall s : S,
  req (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
            (ralt_pistar_pos s))
      (plus (opp (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))
            (plus (log (pi_ref s) (pi_ref_pos s))
                  (mult (inv_pos beta beta_pos) (reward s)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (Z := Z_align_req S sumf reward beta beta_pos pi_ref).
  set (lgZ := log Z Z_align_pos).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  set (e := exp_neg (opp (mult iv (reward s)))).
  set (lgI := log (inv_pos Z Z_align_pos) (inv_pos_pos Z Z_align_pos)).
  set (lgM := log (mult (pi_ref s) e) (mult_positive (pi_ref s) e (pi_ref_pos s) (exp_neg_pos (opp (mult iv (reward s)))))).
  assert (HlogE : req (log e (exp_neg_pos (opp (mult iv (reward s))))) (mult iv (reward s))).
  { apply (req_trans (log e (exp_neg_pos (opp (mult iv (reward s)))))
                     (opp (opp (mult iv (reward s)))) (mult iv (reward s))).
    - exact (ralt_log_exp_neg (opp (mult iv (reward s)))).
    - exact (req_double_neg (mult iv (reward s))). }
  assert (HlgM : req lgM (plus lgR (mult iv (reward s)))).
  { apply (req_trans lgM (plus lgR (log e (exp_neg_pos (opp (mult iv (reward s))))))
                        (plus lgR (mult iv (reward s)))).
    - exact (log_mult (pi_ref s) e (pi_ref_pos s) (exp_neg_pos (opp (mult iv (reward s))))).
    - exact (req_plus_compat lgR lgR (log e (exp_neg_pos (opp (mult iv (reward s))))) (mult iv (reward s))
                             (req_refl lgR) HlogE). }
  set (wit := mult_positive (inv_pos Z Z_align_pos) (mult (pi_ref s) e)
                            (inv_pos_pos Z Z_align_pos)
                            (mult_positive (pi_ref s) e (pi_ref_pos s)
                               (exp_neg_pos (opp (mult iv (reward s)))))).
  apply (req_trans (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
                        (ralt_pistar_pos s))
                   (log (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)) wit)
                   (plus (opp lgZ) (plus lgR (mult iv (reward s))))).
  - exact (ralt_log_req_compat (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s)
                               (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e))
                               (ralt_pistar_pos s) wit
                               (ralt_pistar_cross s)).
  - apply (req_trans (log (mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)) wit)
                     (plus lgI lgM)
                     (plus (opp lgZ) (plus lgR (mult iv (reward s))))).
    + exact (log_mult (inv_pos Z Z_align_pos) (mult (pi_ref s) e)
                      (inv_pos_pos Z Z_align_pos) (mult_positive (pi_ref s) e (pi_ref_pos s)
                         (exp_neg_pos (opp (mult iv (reward s)))))).
    + exact (req_plus_compat lgI (opp lgZ) lgM (plus lgR (mult iv (reward s)))
                             (@rkl_log_inv_one_inv R RIS ralt_log_req_compat Z Z_align_pos)
                             HlgM).
Qed.

(* 2.2 dpo_reward_recovers_up_to_baseline 同位（基座 L19626）：
   真证：ralt_log_pi_star + 减法链（assoc/换序/plus_opp 消去）+
   distrib + β·(1/β)=1 吸收（mult_assoc + inv_pos_correct + mult_one） *)
Lemma ralt_dpo_reward_recovers : forall s : S,
  req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                (ralt_pistar_pos) s)
      (plus (reward s)
            (opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos)))).
Proof.
  intro s.
  set (iv := inv_pos beta beta_pos).
  set (lgZ := log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos).
  set (lgR := log (pi_ref s) (pi_ref_pos s)).
  set (Y := mult iv (reward s)).
  (* 减法消去：(A+(L+Y))−L ≡ A+Y *)
  assert (Hsub : req (req_minus (plus (opp lgZ) (plus lgR Y)) lgR) (plus (opp lgZ) Y)).
  { unfold req_minus.
    apply (req_trans (plus (plus (opp lgZ) (plus lgR Y)) (opp lgR))
                     (plus (opp lgZ) (plus (plus lgR Y) (opp lgR)))
                     (plus (opp lgZ) Y)).
    - exact (req_sym (plus (opp lgZ) (plus (plus lgR Y) (opp lgR)))
                     (plus (plus (opp lgZ) (plus lgR Y)) (opp lgR))
                     (plus_assoc (opp lgZ) (plus lgR Y) (opp lgR))).
    - apply (req_plus_compat (opp lgZ) (opp lgZ)
                             (plus (plus lgR Y) (opp lgR)) Y (req_refl (opp lgZ))).
      apply (req_trans (plus (plus lgR Y) (opp lgR))
                       (plus lgR (plus Y (opp lgR)))
                       Y).
      + exact (req_sym (plus lgR (plus Y (opp lgR))) (plus (plus lgR Y) (opp lgR))
                       (plus_assoc lgR Y (opp lgR))).
      + apply (req_trans (plus lgR (plus Y (opp lgR)))
                         (plus (plus lgR (opp lgR)) Y) Y).
      * apply (req_trans (plus lgR (plus Y (opp lgR)))
                         (plus lgR (plus (opp lgR) Y))
                         (plus (plus lgR (opp lgR)) Y)).
        -- exact (req_plus_compat lgR lgR (plus Y (opp lgR)) (plus (opp lgR) Y)
                    (req_refl lgR) (plus_comm Y (opp lgR))).
        -- exact (plus_assoc lgR (opp lgR) Y).
      * apply (req_trans (plus (plus lgR (opp lgR)) Y) (plus zero Y) Y).
        -- exact (req_plus_compat (plus lgR (opp lgR)) zero Y Y (plus_opp lgR) (req_refl Y)).
        -- exact (req_plus_zero_l Y). }
  (* β·(1/β) 吸收 *)
  assert (Hbetaone : req (mult beta iv) one).
  { exact (inv_pos_correct beta beta_pos). }
  assert (Hbetaiv : req (mult beta (mult iv (reward s))) (reward s)).
  { apply (req_trans (mult beta (mult iv (reward s)))
                     (mult (mult beta iv) (reward s)) (reward s)).
    - exact (mult_assoc beta iv (reward s)).
    - apply (req_trans (mult (mult beta iv) (reward s))
                       (mult one (reward s)) (reward s)).
      + exact (req_mult_compat (mult beta iv) one (reward s) (reward s)
                               Hbetaone (req_refl (reward s))).
      + exact (req_trans (mult one (reward s)) (mult (reward s) one) (reward s)
                         (mult_comm one (reward s)) (mult_one (reward s))). }
  unfold ralt_dir, ralt_log_ratio.
  apply (req_trans (mult beta (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR))
                   (mult beta (plus (opp lgZ) Y))
                   (plus (reward s) (opp (mult beta lgZ)))).
  - apply (req_mult_compat beta beta
             (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR)
             (plus (opp lgZ) Y) (req_refl beta)).
    apply (req_trans (req_minus (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s)) lgR)
                     (req_minus (plus (opp lgZ) (plus lgR Y)) lgR)
                     (plus (opp lgZ) Y)).
    + unfold req_minus.
      exact (req_plus_compat (log (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos s) (ralt_pistar_pos s))
                             (plus (opp lgZ) (plus lgR Y))
                             (opp lgR) (opp lgR)
                             (ralt_log_pi_star s) (req_refl (opp lgR))).
    + exact Hsub.
  - apply (req_trans (mult beta (plus (opp lgZ) Y))
                     (plus (mult beta (opp lgZ)) (mult beta Y))
                     (plus (reward s) (opp (mult beta lgZ)))).
    + exact (distrib beta (opp lgZ) Y).
    + apply (req_trans (plus (mult beta (opp lgZ)) (mult beta Y))
                       (plus (opp (mult beta lgZ)) (reward s))
                       (plus (reward s) (opp (mult beta lgZ)))).
      * exact (req_plus_compat (mult beta (opp lgZ)) (opp (mult beta lgZ))
                               (mult beta Y) (reward s)
                               (req_opp_mult_l beta lgZ) Hbetaiv).
      * exact (plus_comm (opp (mult beta lgZ)) (reward s)).
Qed.

(* 2.3 dpo_reward_relative_exact 同位（基座 L19717）：
   r_DPO(π*,s) − r_DPO(π*,s') ≡ r(s) − r(s')（基线严格消去）。
   真证：2.2 双实例 + req_minus 兼容 + 共同项消去（req_minus_plus_congr） *)
Lemma ralt_dpo_reward_relative_exact : forall s s' : S,
  req (req_minus (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                           (ralt_pistar_pos) s)
                 (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                           (ralt_pistar_pos) s'))
      (req_minus (reward s) (reward s')).
Proof.
  intros s s'.
  set (B := opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))).
  assert (Hrec : req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                               (ralt_pistar_pos) s)
                     (plus (reward s) B))
    by (apply ralt_dpo_reward_recovers).
  assert (Hrec' : req (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                (ralt_pistar_pos) s')
                      (plus (reward s') B))
    by (apply ralt_dpo_reward_recovers).
  apply (req_trans (req_minus (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                        (ralt_pistar_pos) s)
                              (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                        (ralt_pistar_pos) s'))
                   (req_minus (plus (reward s) B) (plus (reward s') B))
                   (req_minus (reward s) (reward s'))).
  - exact (req_plus_compat (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                     (ralt_pistar_pos) s)
                           (plus (reward s) B)
                           (opp (ralt_dir (pi_star_req S sumf ralt_sum_pos reward beta beta_pos pi_ref pi_ref_pos)
                                          (ralt_pistar_pos) s'))
                           (opp (plus (reward s') B))
                           Hrec (req_opp_compat _ _ Hrec')).
  - apply (req_trans (req_minus (plus (reward s) B) (plus (reward s') B))
                     (req_minus (plus B (reward s)) (plus B (reward s')))
                     (req_minus (reward s) (reward s'))).
    + exact (req_plus_compat (plus (reward s) B) (plus B (reward s))
                             (opp (plus (reward s') B)) (opp (plus B (reward s')))
                             (plus_comm (reward s) B)
                             (req_opp_compat (plus (reward s') B) (plus B (reward s'))
                                             (plus_comm (reward s') B))).
    + exact (req_minus_plus_congr B (reward s) (reward s')).
Qed.

(* 2.4 dpo_reward_diff_is_log_ratio_diff 同位（基座 L19802）：
   δ 透明件——ralt_dir 与 β·log_ratio 在 req_minus 载体下逐位同形 *)
Lemma ralt_dpo_reward_diff_is_log_ratio_diff :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s s' : S),
    req (req_minus (ralt_dir pi Hpi s) (ralt_dir pi Hpi s'))
        (req_minus (mult beta (ralt_log_ratio pi Hpi s))
                   (mult beta (ralt_log_ratio pi Hpi s'))).
Proof.
  intros pi Hpi s s'.
  exact (req_refl (req_minus (mult beta (ralt_log_ratio pi Hpi s))
                             (mult beta (ralt_log_ratio pi Hpi s')))).
Qed.

(* ============ 区3：preference 節 req 化（基座 L20101-20258） ============ *)

Variable Preference : Set.
Variable pref_win : Preference -> S.
Variable pref_lose : Preference -> S.

(* 隐式奖励差分（基座 implicit_reward_diff L20106 req 同形；minus → req_minus） *)
Definition ralt_implicit_reward_diff
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference) : R :=
  req_minus (ralt_dir pi Hpi (pref_win pref)) (ralt_dir pi Hpi (pref_lose pref)).

(* 单对损失分母正性（基座 dpo_pair_loss_denom_pos L20115 req 同形；
   平凡直引批 3 req_sigmoid_denom_pos——先于定义结果，供 log 见证槽） *)
Lemma ralt_dpo_pair_denom_pos :
  forall (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference),
    lt zero (plus one (exp_neg (ralt_implicit_reward_diff pi Hpi pref))).
Proof.
  intros pi Hpi pref.
  exact (req_sigmoid_denom_pos (ralt_implicit_reward_diff pi Hpi pref)).
Qed.

(* DPO 单对损失（基座 dpo_pair_loss L20111 req 同形；log 前提化携带分母见证） *)
Definition ralt_dpo_pair_loss
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (pref : Preference) : R :=
  log (plus one (exp_neg (ralt_implicit_reward_diff pi Hpi pref)))
      (ralt_dpo_pair_denom_pos pi Hpi pref).

(* π* 处星形分母正性 + 星形损失常数（基座 dpo_pair_loss_star L20136 req 同形） *)
Definition ralt_pair_denom_pos_star (pref : Preference)
  : lt zero (plus one (exp_neg (req_minus (reward (pref_win pref))
                                          (reward (pref_lose pref))))) :=
  req_sigmoid_denom_pos (req_minus (reward (pref_win pref))
                                   (reward (pref_lose pref))).

Definition ralt_dpo_pair_loss_star (pref : Preference) : R :=
  log (plus one (exp_neg (req_minus (reward (pref_win pref))
                                    (reward (pref_lose pref)))))
      (ralt_pair_denom_pos_star pref).

(* 3.1 pi_star_implicit_reward_diff 同位（基座 L20126）：
   π* 处隐式奖励差分 ≡ 真实奖励差分（使用 2.3；真证在彼处） *)
Theorem ralt_pi_star_implicit_reward_diff : forall pref : Preference,
  req (ralt_implicit_reward_diff ralt_pistar ralt_pistar_pos pref)
      (req_minus (reward (pref_win pref)) (reward (pref_lose pref))).
Proof.
  intro pref.
  exact (ralt_dpo_reward_relative_exact (pref_win pref) (pref_lose pref)).
Qed.

(* 3.2 dpo_pair_loss_at_star 同位（基座 L20139）：π* 处损失退化为
   真实奖励差分的 sigmoid 交叉熵。真证：3.1 + exp_neg 兼容 + log 缺口桥 *)
Theorem ralt_dpo_pair_loss_at_star : forall pref : Preference,
  req (ralt_dpo_pair_loss ralt_pistar ralt_pistar_pos pref)
      (ralt_dpo_pair_loss_star pref).
Proof.
  intro pref.
  unfold ralt_dpo_pair_loss, ralt_dpo_pair_loss_star.
  apply ralt_log_req_compat.
  apply (req_plus_compat one one
           (exp_neg (ralt_implicit_reward_diff ralt_pistar ralt_pistar_pos pref))
           (exp_neg (req_minus (reward (pref_win pref)) (reward (pref_lose pref))))
           (req_refl one)).
  apply exp_neg_req_compat_setoid.
  exact (ralt_pi_star_implicit_reward_diff pref).
Qed.

(* 3.3 relative_entropy_ext_r 同位（基座 L20242）：右端外延。
   真证：sum_ext 逐点 + mult/req_minus/log 兼容链 *)
Theorem ralt_relative_entropy_ext_r :
  forall (p q1 q2 : S -> R) (Hp : forall s : S, lt zero (p s))
         (Hq1 : forall s : S, lt zero (q1 s)) (Hq2 : forall s : S, lt zero (q2 s)),
    (forall s : S, req (q1 s) (q2 s)) ->
    req (relative_entropy_req S sumf p q1 Hp Hq1)
        (relative_entropy_req S sumf p q2 Hp Hq2).
Proof.
  intros p q1 q2 Hp Hq1 Hq2 Hext.
  unfold relative_entropy_req.
  apply (ralt_sum_ext (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q1 s) (Hq1 s))))
                      (fun s => mult (p s) (req_minus (log (p s) (Hp s)) (log (q2 s) (Hq2 s))))).
  intro s.
  apply (req_mult_compat (p s) (p s)
           (req_minus (log (p s) (Hp s)) (log (q1 s) (Hq1 s)))
           (req_minus (log (p s) (Hp s)) (log (q2 s) (Hq2 s)))
           (req_refl (p s))).
  exact (req_plus_compat (log (p s) (Hp s)) (log (p s) (Hp s))
                         (opp (log (q1 s) (Hq1 s))) (opp (log (q2 s) (Hq2 s)))
                         (req_refl (log (p s) (Hp s)))
                         (req_opp_compat (log (q1 s) (Hq1 s)) (log (q2 s) (Hq2 s))
                           (ralt_log_req_compat (q1 s) (q2 s) (Hq1 s) (Hq2 s) (Hext s)))).
Qed.

(* ---- total_loss 簇（基座 L20151-20240）冻结：fold_right_ext 及 list fold
   机器为 nat/list 层 Id（规划书 §1.1 边界 2；批 3 登记表 4 同款双层并行）。
   ppo_gap_nonneg（基座 L20083）冻结：min plain-le 形（批 3 冻结先例）。 ---- *)

(* ============ 区4：sigmoid/DPO 损失簇 req 化（基座 L20880-21059） ============ *)
(* sigmoid_denom_pos/sigmoid_pos/sigmoid_zero_half 三件批 3 已建
   （UpReqAlign ReqSigmoidQuick：req_sigmoid_denom_pos/sigmoid_req/
   req_sigmoid_pos/req_sigmoid_zero_half），使用不重建。 ---- *)

(* 4.1 成对 DPO 损失（基座 dpo_loss_pair L20885 req 同形；
   sigmoid_req 批 3 成品 + req_minus 载体 + log 见证显式位） *)
Definition ralt_dpo_loss_pair
  (pi : S -> R) (Hpi : forall s : S, lt zero (pi s)) (s_w s_l : S) : R :=
  opp (log (sigmoid_req (req_minus (mult beta (ralt_log_ratio pi Hpi s_w))
                                   (mult beta (ralt_log_ratio pi Hpi s_l))))
           (req_sigmoid_pos (req_minus (mult beta (ralt_log_ratio pi Hpi s_w))
                                       (mult beta (ralt_log_ratio pi Hpi s_l))))).

(* 4.2 dpo_loss_at_pi_star 同位（基座 L20892）：π* 处损失 ≡ -log σ(r_w - r_l)。
   真证：2.2 消去 Z/π_ref（差分中基线成对消去）+ inv_pos_ext 运输 +
   log 缺口桥。 *)
Theorem ralt_dpo_loss_at_pi_star : forall s_w s_l : S,
  req (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
      (opp (log (sigmoid_req (req_minus (reward s_w) (reward s_l)))
                 (req_sigmoid_pos (req_minus (reward s_w) (reward s_l))))).
Proof.
  intros s_w s_l.
  unfold ralt_dpo_loss_pair.
  set (MW := mult beta (ralt_log_ratio ralt_pistar ralt_pistar_pos s_w)).
  set (ML := mult beta (ralt_log_ratio ralt_pistar ralt_pistar_pos s_l)).
  set (X := req_minus (reward s_w) (reward s_l)).
  set (B := opp (mult beta (log (Z_align_req S sumf reward beta beta_pos pi_ref) Z_align_pos))).
  assert (Hw : req MW (plus (reward s_w) B))
    by (exact (ralt_dpo_reward_recovers s_w)).
  assert (Hl : req ML (plus (reward s_l) B))
    by (exact (ralt_dpo_reward_recovers s_l)).
  assert (Hdiff : req (req_minus MW ML) X).
  { apply (req_trans (req_minus MW ML)
                     (req_minus (plus (reward s_w) B) (plus (reward s_l) B)) X).
    - exact (req_plus_compat MW (plus (reward s_w) B) (opp ML) (opp (plus (reward s_l) B))
                             Hw (req_opp_compat ML (plus (reward s_l) B) Hl)).
    - apply (req_trans (req_minus (plus (reward s_w) B) (plus (reward s_l) B))
                       (req_minus (plus B (reward s_w)) (plus B (reward s_l))) X).
      + exact (req_plus_compat (plus (reward s_w) B) (plus B (reward s_w))
                               (opp (plus (reward s_l) B)) (opp (plus B (reward s_l)))
                               (plus_comm (reward s_w) B)
                               (req_opp_compat (plus (reward s_l) B) (plus B (reward s_l))
                                               (plus_comm (reward s_l) B))).
      + exact (req_minus_plus_congr B (reward s_w) (reward s_l)). }
  apply req_opp_compat.
  apply ralt_log_req_compat.
  apply (inv_pos_ext (plus one (exp_neg (req_minus MW ML))) (plus one (exp_neg X))
                     (req_sigmoid_denom_pos (req_minus MW ML)) (req_sigmoid_denom_pos X)).
  apply (req_plus_compat one one (exp_neg (req_minus MW ML)) (exp_neg X) (req_refl one)).
  apply exp_neg_req_compat_setoid.
  exact Hdiff.
Qed.

(* 4.3 sigmoid_strict_inc 同位（基座 L21030）：sigmoid 严格递增。
   真证：exp_neg_decr + ralt_lt_plus_compat_le_lt + **区1 消解件
   ralt_inv_pos_lt_contra**（Id 层 Variable 位在本批关闭） *)
Theorem ralt_sigmoid_strict_inc : forall x y : R,
  lt x y -> lt (sigmoid_req x) (sigmoid_req y).
Proof.
  intros x y Hxy.
  apply (ralt_inv_pos_lt_contra (plus one (exp_neg y)) (plus one (exp_neg x))
                                (req_sigmoid_denom_pos y) (req_sigmoid_denom_pos x)).
  exact (ralt_lt_plus_compat_le_lt one one (exp_neg y) (exp_neg x) (le_refl one)
                                   (exp_neg_decr x y Hxy)).
Qed.

(* 4.4 dpo_loss_pi_star_bounded 同位（基座 L21059）：
   真证：4.2 + 4.3 + ralt_log_lt_mono（B 类桥使用）+ opp_lt_compat +
   log(1/2) = -log 2（req_log_inv_one_inv + double_neg） *)
Theorem ralt_dpo_loss_pi_star_bounded : forall s_w s_l : S,
  lt (reward s_l) (reward s_w) ->
  lt (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
     (log (plus one one) (req_two_pos)).
Proof.
  intros s_w s_l Hrw.
  set (D := req_minus (reward s_w) (reward s_l)).
  assert (Hpos : lt zero D).
  (* Hpos: 0 < r_w - r_l *)
  { apply (lt_id_l zero (plus (reward s_l) (opp (reward s_l)))
                    (plus (reward s_w) (opp (reward s_l)))).
    - exact (req_sym (plus (reward s_l) (opp (reward s_l))) zero
                     (plus_opp (reward s_l))).
    - exact (ralt_lt_plus_compat_lt_le (reward s_l) (reward s_w) (opp (reward s_l))
                                       (opp (reward s_l)) Hrw (le_refl (opp (reward s_l)))). }
  assert (Hsig : lt (sigmoid_req zero) (sigmoid_req D))
    by (exact (ralt_sigmoid_strict_inc zero D Hpos)).
  assert (Hlog : lt (log (sigmoid_req zero) (req_sigmoid_pos zero))
                    (log (sigmoid_req D) (req_sigmoid_pos D)))
    by (exact (ralt_log_lt_mono (sigmoid_req zero) (sigmoid_req D)
                                (req_sigmoid_pos zero) (req_sigmoid_pos D) Hsig)).
  assert (Hopp : lt (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                    (opp (log (sigmoid_req zero) (req_sigmoid_pos zero))))
    by (exact (opp_lt_compat (log (sigmoid_req zero) (req_sigmoid_pos zero))
                             (log (sigmoid_req D) (req_sigmoid_pos D)) Hlog)).
  assert (Hval : req (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                     (log (plus one one) (req_two_pos))).
  { apply (req_trans (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                     (opp (log (inv_pos (plus one one) (req_two_pos))
                               (inv_pos_pos (plus one one) (req_two_pos))))
                     (log (plus one one) (req_two_pos))).
    - apply req_opp_compat.
      exact (ralt_log_req_compat (sigmoid_req zero)
                                 (inv_pos (plus one one) (req_two_pos))
                                 (req_sigmoid_pos zero)
                                 (inv_pos_pos (plus one one) (req_two_pos))
                                 (req_sigmoid_zero_half)).
    - apply (req_trans (opp (log (inv_pos (plus one one) (req_two_pos))
                                  (inv_pos_pos (plus one one) (req_two_pos))))
                       (opp (opp (log (plus one one) (req_two_pos))))
                       (log (plus one one) (req_two_pos))).
      + apply req_opp_compat.
        exact (@req_log_inv_one_inv R RIS ralt_log_req_compat
                 (plus one one) (req_two_pos)).
      + exact (req_double_neg (log (plus one one) (req_two_pos))). }
  exact (lt_id_l (ralt_dpo_loss_pair ralt_pistar ralt_pistar_pos s_w s_l)
                 (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                 (log (plus one one) (req_two_pos))
                 (ralt_dpo_loss_at_pi_star s_w s_l)
                 (lt_id_r (opp (log (sigmoid_req D) (req_sigmoid_pos D)))
                          (opp (log (sigmoid_req zero) (req_sigmoid_pos zero)))
                          (log (plus one one) (req_two_pos)) Hval Hopp)).
Qed.


End ReqRestACore.

(* ============================================================ *)
(* 区5：KL 投影区合并块余件 —— A2 Q↔Real 桥 req 系签名定位          *)
(*   （基座 仅存 real_const_pos(L36290)/real_const_lt(L37095)  *)
(*     两件；合并块 L95422-95508 的 eq/le/qleT/eq_bool 四件    *)

(*     将全部六件以接口投影 req 形态定位。instance RealEnhancedReal  *)
(*     的 req/lt/le 逐位 = real_eq/real_lt/real_le：change 暴露具体  *)
(*     形态后全显式 exact/逐字证明——具体层禁 apply 类字段投影，       *)

(*   A1 nat↔Q 桥 7 件与升级包 1-3（seq_eqb/in_seq/pick_passing/      *)
(*     count_true/majority_audit/sf_*）为 nat/list/Q 层 Id，双层冻结  *)
(*     （规划书 §1.1 边界 2）。                                       *)
(* ============================================================ *)

(* 5.1 嵌入相等（L95422 补件 + 定位） *)
Lemma ralt_real_const_req_eq : forall x y : Q, x == y -> req (real_const x) (real_const y).
Proof.
  intros x y Hxy.
  change (real_eq (real_const x) (real_const y)).
  intros eps Heps. exists 0%nat. intros n Hn.
  cbn [projT1 real_const].
  unfold QltT, Qlt_bool.
  assert (H0lt : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Hcmp0 : Qcompare 0 eps = Lt) by (apply Qlt_alt; exact H0lt).
  assert (Hd0 : (x - y == 0)%Q).
  { unfold Qminus.
    apply (Qeq_trans _ (y + (- y))).
    - apply (proj2 (Qplus_inj_r x y (- y))). exact Hxy.
    - apply Qplus_opp_r. }
  assert (Hz : Qabs (x - y) == 0).
  { apply (Qeq_trans _ (Qabs 0%Q)).
    - apply Qabs_wd. exact Hd0.
    - reflexivity. }
  assert (Hcmp : Qcompare (Qabs (x - y)) eps = Lt).
  { assert (Hc1 : Qcompare (Qabs (x - y)) eps = Qcompare 0 eps).
    { exact (Qcompare_comp (Qabs (x - y)) 0 Hz eps eps (Qeq_refl eps)). }
    rewrite Hc1. exact Hcmp0. }
  rewrite Hcmp. reflexivity.
Qed.

(* 5.2 严格序嵌入（L37095 现成件定位） *)
Lemma ralt_real_const_req_lt : forall c d : Q,
  Qlt c d -> lt (real_const c) (real_const d).
Proof.
  intros c d Hcd.
  change (real_lt (real_const c) (real_const d)).
  exact (real_const_lt c d Hcd).
Qed.

(* 5.3 弱序嵌入（L95447 补件 + 定位；Q 三分装配：左严格/中矛盾/右相等） *)
Lemma ralt_real_const_req_le : forall x y : Q,
  Qle x y -> le (real_const x) (real_const y).
Proof.
  intros x y Hxy.
  change (real_le (real_const x) (real_const y)).
  destruct (Q_dec x y) as [[Hlt | Hgt] | Heq].
  - left. exact (ralt_real_const_req_lt x y Hlt).
  - exfalso. exact (Qlt_irrefl y (Qlt_le_trans y x y Hgt Hxy)).
  - right. exact (ralt_real_const_req_eq x y Heq).
Qed.

(* 5.4 Set 层推论 QleT' 版（L95478 补件 + 定位） *)
Lemma ralt_real_const_req_qleT : forall x y : Q,
  QleT' x y -> le (real_const x) (real_const y).
Proof.
  intros x y H.
  exact (ralt_real_const_req_le x y (QleT'_to_Qle x y H)).
Qed.

(* 5.5 Set 层推论 Qeq_bool 判定版（L95484 补件 + 定位） *)
Lemma ralt_real_const_req_eq_bool : forall x y : Q,
  Id (Qeq_bool x y) true -> req (real_const x) (real_const y).
Proof.
  intros x y H.
  exact (ralt_real_const_req_eq x y
           (proj1 (Qeq_bool_iff x y) (RealSetoid.Id_eq (Qeq_bool x y) true H))).
Qed.

(* 5.6 正性嵌入（L36290 现成件定位） *)
Lemma ralt_real_const_req_pos : forall c : Q,
  QltT 0 c -> lt zero (real_const c).
Proof.
  intros c Hc.
  change (real_lt real_zero (real_const c)).
  exact (real_const_pos c Hc).
Qed.



(* （ToyR 增补·非原件改动）假设面闭合申报节：玩具面逐件申报，
    全 Closed 为已证结论标识；基准对照件以同文申报节同法试编比对。 *)
Print Assumptions ralt_log_exp_neg.
Print Assumptions ralt_mult_lt_compat_l.
Print Assumptions ralt_lt_plus_compat_le_lt.
Print Assumptions ralt_lt_plus_translate.
Print Assumptions ralt_minus_plus_common.
Print Assumptions ralt_dpo_reward_diff_is_log_ratio_diff.
Print Assumptions ralt_dpo_pair_denom_pos.
Print Assumptions ralt_pi_star_implicit_reward_diff.
Print Assumptions ralt_sigmoid_strict_inc.
Print Assumptions ralt_real_const_req_qleT.
Print Assumptions ralt_real_const_req_eq_bool.