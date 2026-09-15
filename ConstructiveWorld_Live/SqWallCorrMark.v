(* SqWallCorrMark.v

   目的：登记「平方非负全称」类前提位（forall a, le zero (mult a a)）
   的结构性勘误结论：该接口面在 Real 实例下与「墙」SqWall 同面，而
   Or 编码的全称墙与受限 LPO 双向等价（UpReqLpoEquiv 机器检验），故
   全称供给不可达；本件给出消费位衔接件（接口投影面转换 / 双向指针 /
   等价件镜像）与补 Bishop 逐 eps 前提的同构重述定理（可达替代）。
   本件标识符均以 swc_ 前缀命名（全库实扫无重名）。

   主件：swc_lpn_equivalence_slot（双向指针等价件，lpn_equivalence 的
   前提位面镜像）；swc_sq_ge_a_b_form（补 real_le_b 前提的同构重述）；
   swc_sq_wall_b_reachable（B 形全称平方非负）。

   依赖：CW_ConstructiveWorld_219；UpReqLpoEquiv（SqWall:230 /
   rLPO:234 / lpn_forward:249 / lpn_backward:342 / lpn_equivalence:429，
   vo 基座在盘）；UpRealLeB（real_le_b 系）；RealInterfaceEnhancedMod
   （S07:7895 接口与 RealEnhancedReal 实例）。

   备注：Or 编码全称形=墙（与受限 LPO 等价，不可全称供给）；Bishop
   逐 eps 形=可达（real_square_nonneg_B 全称可证）；条件形/带前提形
   非墙位（见下逐条判定）。源位清单：UpReqAlign.v:1111-1163 /
   UpReqSqrtF.v:660-726 / SqrtfCauchy.v:76,560,827 /
   S05_AlignmentGRPO.v:5576-5623 / G01_CoreMicro.v:316-332 /
   S15_TailFEPUp.v:2062-2075 / G09_MiscSmall.v:316-530 /
   UpRealLeB.v:63,373,424,814 / S08_RealMainlineDPO.v:3626-3631 /
   S07_RealSetoidExpLog.v:7906,8557。

   ============================================================
   【勘误结论】「平方非负全称」类前提位的结构性判定
   ============================================================

   总判定：接口面 forall a, le zero (mult a a) 在 Real 实例
   （S07:8557 RealEnhancedReal，字段 le:=real_le / zero:=real_zero /
   mult:=real_mult）下与 SqWall 定义性相同——即本前提位就是
   UpReqLpoEquiv 已证与受限 LPO 双向等价的「墙」的数据形。三类形态分判：

   ▌位1 UpReqAlign.v:1122（Section ReqNaturalGradient 泛型 R 前提位）
   ├ 结构性判定：诚实前提位=墙面（接口泛型下无法内证；构造性有序域
   │  无三分律，符号判定数据不可供给——S02:802 墙注同源）。
   ├ 消费位：:1157 唯一直接消费（req_fisher_zero_implies_pointwise
   │  证明体 le_id_l/le_mult_compat 链注入逐点平方非负）。
   ├ GRPO T1.5 同位先例：S05:5582 根 Variable square_nonneg
   │  （消费 :5623 group_variance_le_raw_second_moment）。
   ├ 指针：lpn_backward 供前提（rLPO -> 前提位面，本件
   │  swc_lpn_backward_slot）；lpn_forward 耗前提（前提位面 -> rLPO）。
   └ 衔接：G09:490 已立 Real 实例化升参形
      sqp_fisher_zero_implies_pointwise_real，其 Hsq 参数位
      （forall a, le zero (mult a a)）即本前提位面——补一实参
      (swc_lpn_backward_slot Hdec) 即从受限 LPO 消解。

   ▌位2 UpReqSqrtF.v:707（Section SqrtF 泛型 R 前提位，路线 a 诚实位）
   ├ 结构性判定：同位1；§8 勘误补注（:692-706）已实证 plain 形在
   │  Real 层不可供给——Or 编码两侧在 t_n^2 无一致正尾部时皆假
   │  （t := 1/n 序列形反例）；接口 abs 族不敷用（|t|·|t| 与 t·t
   │  无 req 桥：符号不可判定且接口无分解字段）。
   ├ 消费位：:725 直接消费（sqrtf_sq_ge_a 的 le_plus_compat 前提注入
   │  链）；下游 sqrtf_iterate_sq_ge 全量传播；SqrtfCauchy.v:76
   │  同位升参形 sfc_square_nonneg（消费 :560/:827）。
   ├ 指针：同位1——lpn_backward 供前提即收敛链解锁。
   └ 衔接：SqrtfCauchy 链的前提参数位补一实参
      (swc_lpn_backward_slot Hdec)；或改走本件 B 形同构重述定理
      swc_sq_ge_a_b_form（可达替代，见下）。

   ▌位3 全库检索补全消费位清单（结构性判定逐条）
   ├ S15_TailFEPUp.v:2069 / G01_CoreMicro.v:324
   │  real_var_nonneg_cond：条件形态（逐项假设给足即消解）——
   │  非墙位，但其假设位仍是墙面；求和侧镜像与位1 同源。
   ├ S06_DiffSamplingGibbs.v:1689 set_square_nonneg /
   │  UpReqSLM.v:735 req_set_square_nonneg：带前提条件形
   │  （le zero t -> le zero (mult t t)）——可证形（乘法非负
   │  闭包），非墙位，无需勘误。
   ├ S11_TP3B5.v Q 层 Qsquare_nonneg：有理数可判定三分律——
   │  可证形，非墙位（墙仅在 Real/柯西层）。
   ├ UpReqU2/UpReqRDF 等 le zero (mult a b) 双非负前提型：
   │  乘法保序消费形，非墙位，不在本结论范围。
   └ G09_MiscSmall.v:491/518 两升参形：前提位隔离已就位（余留
      前提=位本身），其 Hsq 参数位=本件判定面。

   ▌可达替代指针（real_le_b 路线，已证件）
   ├ UpRealLeB.v:424 real_square_nonneg_B：
   │  forall t:Real, real_le_b real_zero (real_mult t t)
   │  （0 ≤_B t·t，全称可证、Closed，假设审计见 UpRealLeB:814；
   │  证书链 = real_le_closure_b_one:373 + eps 形直连）。
   ├ eps 形源：S08:3628 real_square_nonneg_eps
   │  （forall t eps, 0 < eps -> real_le real_zero (t·t + eps)）。
   └ 判定：Or 编码全称形=墙（rLPO 等价）；Bishop 逐 eps 形=可达
      （同数学内容换编码后可全称供给）——同构重述定理见
      swc_sq_wall_b_reachable / swc_sq_ge_a_b_form。

   ============================================================ *)

From Stdlib Require Import Extraction.
Require Import CW_ConstructiveWorld_219.
Require Import UpReqLpoEquiv.
Require Import UpRealLeB.
Import RealInterfaceEnhancedMod.

(* 衔接件一：接口投影前提位面 -> 墙面（Real 实例字段映射的转换件；
   唯一承担实例 delta/iota 归约负担的引理，后件全走素颜面） *)
Lemma swc_interface_slot_face :
  (forall t : Real,
     @le Real RealEnhancedReal (@zero Real RealEnhancedReal)
         (@mult Real RealEnhancedReal t t)) ->
  (forall t : Real, real_le real_zero (real_mult t t)).
Proof.
  exact (fun H => H).
Qed.

(* 衔接件二：前提位面（素颜）即 SqWall（UpReqLpoEquiv:230 逐字同面）；
   与衔接件一复合 = 任意接口泛型前提位在 Real 实例的衔接通道 *)
Definition swc_sq_wall_face : Set :=
  forall t : Real, real_le real_zero (real_mult t t).

Lemma swc_sq_wall_face_is_sq_wall : swc_sq_wall_face -> SqWall.
Proof.
  exact (fun H => H).
Qed.

Lemma swc_sq_wall_is_sq_wall_face : SqWall -> swc_sq_wall_face.
Proof.
  exact (fun H => H).
Qed.

(* 衔接件三：LpoEquiv 双向指针衔接消费位（补一实参即用）
   供前提（消解）：rLPO 证书 -> 前提位面 —— lpn_backward 直接提供实参
   耗前提（判定）：前提位面证书 -> rLPO —— lpn_forward 直接提供实参 *)
Theorem swc_lpn_backward_slot :
  rLPO -> (forall t : Real, real_le real_zero (real_mult t t)).
Proof.
  exact lpn_backward.
Qed.

Theorem swc_lpn_forward_slot :
  (forall t : Real, real_le real_zero (real_mult t t)) -> rLPO.
Proof.
  exact lpn_forward.
Qed.

(* 衔接件四：等价件前提位面镜像（lpn_equivalence:429 的同构重申）。
   语句面勘误（20260915）：原语句首元写作
   And (forall t : Real, real_le real_zero (real_mult t t) -> rLPO)，
   ∀ 作用域吞掉尾随「-> rLPO」，成逐点双前提形
   forall t, (real_le real_zero (real_mult t t) -> rLPO)——与前提位
   构造对的整墙形 ((forall t, real_le real_zero (real_mult t t))
   -> rLPO) 积结构不同构：前者首个 binder 域为 Real、后者为全称面，
   内核转换在该处即不可达（实测 pair 合一失败恰在此点）。重括号修正
   为整墙形，首尾元与 lpn_equivalence 逐元同构（面经 SqWall delta
   相等）。变更前后对照见同日交付报告。 *)
Definition swc_lpn_equivalence_slot :
  And ((forall t : Real, real_le real_zero (real_mult t t)) -> rLPO)
      (rLPO -> (forall t : Real, real_le real_zero (real_mult t t))) :=
  (swc_lpn_forward_slot, swc_lpn_backward_slot).

(* ============================================================ *)
(* 【可达替代件】B 形（Bishop 逐 eps）同构重述定理                *)
(* ============================================================ *)

(* 重述一：B 形全称平方非负——墙面在 real_le_b 编码下的可达形态
   （指针件 UpRealLeB:424 real_square_nonneg_B 一步重申） *)
Theorem swc_sq_wall_b_reachable :
  forall t : Real, real_le_b real_zero (real_mult t t).
Proof.
  exact real_square_nonneg_B.
Qed.

(* 重述二：eps 形源逐字重申（S08:3628 real_square_nonneg_eps；
   B 形的证书供给链原件，一步重申防散悬） *)
Theorem swc_square_nonneg_eps_face : forall (t eps : Real),
  real_lt real_zero eps ->
  real_le real_zero (real_plus (real_mult t t) eps).
Proof.
  exact real_square_nonneg_eps.
Qed.

(* 重述三（主交付）：补 B 形前提的同构重述定理——
   位2 消费面（sqrtf_sq_ge_a 的前提注入链：前提给 s·s 非负，
   le_plus_compat 收 a ≤ s·s + a）在 B 形前提下的同构重述。
   前提由诚实位（Or 编码墙面）换为 B 形前提（real_le_b，可达），
   结论面同步换 B 形：a ≤_B s·s + a。
   证法：B 形前提在 eps 处直供 0 < s·s + eps，a 平移
   （real_lt_plus_translate）+ assoc/comm 换形链闭合；
   real_eq_plus_compat 按 S07:209 交叉式签名（a≈c / b≈d）排实参。 *)
Theorem swc_sq_ge_a_b_form : forall (a s : Real),
  real_lt real_zero a ->
  real_le_b real_zero (real_mult s s) ->
  real_le_b a (real_plus (real_mult s s) a).
Proof.
  intros a s Ha Hsq.
  unfold real_le_b in Hsq.
  unfold real_le_b.
  intros eps Heps.
  assert (H2 : real_lt real_zero (real_plus (real_mult s s) eps))
    by exact (Hsq eps Heps).
  assert (H3 : real_lt (real_plus a real_zero)
                       (real_plus a (real_plus (real_mult s s) eps)))
    by exact (real_lt_plus_translate a real_zero
                (real_plus (real_mult s s) eps) H2).
  assert (H4 : real_lt (real_plus a real_zero)
                       (real_plus (real_plus (real_mult s s) a) eps)).
  { apply (RealSetoid.real_lt_id_r (real_plus a real_zero)
             (real_plus a (real_plus (real_mult s s) eps))
             (real_plus (real_plus (real_mult s s) a) eps)).
    - apply (real_eq_trans
               (real_plus a (real_plus (real_mult s s) eps))
               (real_plus (real_plus a (real_mult s s)) eps)
               (real_plus (real_plus (real_mult s s) a) eps)
               (real_plus_assoc a (real_mult s s) eps)
               (RealSetoid.real_eq_plus_compat
                  (real_plus a (real_mult s s))
                  eps
                  (real_plus (real_mult s s) a)
                  eps
                  (real_plus_comm a (real_mult s s))
                  (real_eq_refl eps))).
    - exact H3. }
  apply (RealSetoid.real_lt_id_l a (real_plus a real_zero)
           (real_plus (real_plus (real_mult s s) a) eps)).
  - apply real_eq_sym.
    apply real_plus_zero.
  - exact H4.
Qed.

(* ============================================================ *)
(* 提取探针与假设审计面                                          *)
(* ============================================================ *)

(* 提取探针（KLWallClosed 命名式）：主三件全量提取面。
   本三件证明体均不触 RealEnhancedReal 类实例打包常量
   （lpn 系纯 S01/S02/Q 层；B 形系纯 real_* 顶层函数链），
   预期 Obj.magic 计数=0；G05 先例（magic 计数=73 全落实例打包
   常量）供对照定位。 *)
Extraction "_thv3sw3_G3.ml" swc_lpn_equivalence_slot
  swc_sq_wall_b_reachable swc_sq_ge_a_b_form.

Print Assumptions swc_interface_slot_face.
Print Assumptions swc_sq_wall_face_is_sq_wall.
Print Assumptions swc_lpn_backward_slot.
Print Assumptions swc_lpn_forward_slot.
Print Assumptions swc_sq_wall_b_reachable.
Print Assumptions swc_sq_ge_a_b_form.
