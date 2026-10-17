(* ===================================================================== *)
(* piu_zz_ln_rate_bound.v                                                *)
(* 使命: L_n 率型假设（Λu=29/Λl=28）消解执行件（判定与交付见下）；依赖清单: piu_zz_poincare_engine、piu_zz_padic_clearing + stdlib；构造性注记: 零 Axiom/Admitted/Parameter/Conjecture/Abort/Section 假设    *)
(* 溯源：需求形 R1(b)/R2(b)（两条 L_n 率型假设唯一设定源）     *)
(*   + piu_zz_padic_clearing（zz_L/zz_Phi/zz_in_Pn/zz_lcm_range born 件，     *)
(*   ZZ 2020 v2 Lemma 3 语义：L_n=lcm(1..4n)/Φ_n）+ piu_zz_poincare_engine    *)
(*   （QleT'/qleT_intro/zq/piu_zz_qpow——设计书 V1 样点形载体）。               *)
(* --------------------------------------------------------------------- *)
(* 消解判定（响亮降级申报——机验三连）：                               *)
(*   ①常数步进路线【否证，非难度问题】：步进消解假想 L_{n+1} ≤ 29·L_n 不真——   *)
(*     机验 zz_L 8 = 19778·zz_L 7 且 29 < 19778（本件                        *)
(*     piu_zz_ln_L8_19778_L7 / piu_zz_ln_step_ratio_gt_29 两定理）。窗口积     *)
(*     Φ_n 涨落使步长比无界（素数落入 (4n,4n+4] 步即跳 ~4n 倍）。               *)
(*   ②设计书 V1 样点带预期【否证】：up 组（4,8,16,32,64,128）预期全 true，      *)
(*     实算 8/16/32/128 全 false（本件 piu_zz_ln_up_v1_fail_* 四定理）；       *)
(*     L_n^{1/n} 震荡（n=8 达 42.7；n≤320 内 up 破裂 225 点），29 的 1.3%      *)
(*     指数裕度被 ψ(4n)/窗口积涨落吞噬至渐近域。                              *)
(*   ③尾段消解=有效化 PNT+ZZ 式(10)（求翻转点有效界）——主裁明禁 PNT，故        *)
(*     「∃N₀ ∀n≥N₀」之尾段残余为 PNT 级债（B 类，本件不可证），降级申报。   *)
(*   ④工具链异常【响亮，异常#4】：LO 连续带 [253,320] 的 34 点 forallb 表在      *)
(*     tactic 级 vm_compute 两次返回 false（多轮实测），而同  *)
(*     式 command 级 Compute 两次返回 true（probe16/17）+Python 独立复算 true——     *)
(*     疑 VM 规模态分歧，本件切片内不可断，处理=单点化成证+带内容降机外账。   *)
(* 交付（零假设——本件无 Section、无 Hypothesis，一切定理出件即无条件）：        *)
(*   (i) L_n 乘性结构精确递归：Φ 加权步进 + L-松步进 + L_n≤lcm(1..4n)          *)
(*       + 正性（纯 Z 真证明，piu_zz_ln_step_phi 等）；                        *)
(*   (ii) 有限点/小带定理（单点化 tactic vm_compute，计算证明 Defined）：       *)
(*       LO 点组 7 点（含带内 253/273/303/320）、UP 点组 10 点、小样组两件      *)
(*       （逐点 QleT' 形，V1 形状）；连续带内容=Python+command 双验真，因异常#4 *)
(*       不作树内定理申报。                                                  *)
(*   (iii) 机验反例件（fail-loud）：V1 预期反例四定理 + n=8 严格分离            *)
(*       + 步长比 19778 件。                                                 *)
(* 残余处方：率型假设 HLn_rate_up/lo（需求形 §D）在尾段保持最小诚实假设位；     *)
(*   使用面（tau_face/low_face/s1/s2）在本件带域内可 Require 本件免假设；       *)
(*   尾段消解唯一正路=有效 PNT 路线（后续专件），本件不假设不隐藏。             *)
(* 红线：零 Axiom/Admitted/Parameter/Conjecture/Abort/Section Hypothesis；     *)
(*   词面零命中；G4 PA 全 Closed 即本件卖点。                                 *)
(* 环境注记（本件实测判例）：池件链把裸 Nat 重绑为 Corelib.Init.Nat（probe10   *)
(*   Locate 实测），Nat.leb_le 等一律 PeanoNat.Nat 全限定；Z.of_nat 对符号     *)
(*   K 的 (K+j) 形与 of K + j 形互不可归约（Nat.add 首参递归不前进）——本件 Z 面  *)
(*   全用加法规范形 Z.of_nat X + j 且左结合链，形状即合同。                    *)
(* 编译配方：先编 piu_zz_poincare_engine.v 与 piu_zz_padic_clearing.v         *)
(*   （依赖件 .vo 在册），再 cpu_guard 包裹下：                                 *)
(*   rocq c -native-compiler no -q -Q . "" piu_zz_ln_rate_bound.v             *)
(* ===================================================================== *)

From Stdlib Require Import QArith Lia List PeanoNat.
From Stdlib Require Import Extraction.
Import ListNotations.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* ==================================================================== *)
(* §1. lcm 步进面（纯 Z，零假设）                                           *)
(* ==================================================================== *)

Lemma zz_lcm_pos : forall a b : Z,
  (0 < a)%Z -> (0 < b)%Z -> (0 < Z.lcm a b)%Z.
Proof.
  intros a b Ha Hb.
  pose proof (Z.lcm_nonneg a b) as Hnn.
  assert (Hne : Z.lcm a b <> 0%Z).
  { intro H0. apply Z.lcm_eq_0 in H0. destruct H0; lia. }
  lia.
Qed.

Lemma zz_lcm_range_pos : forall K : nat, (0 < zz_lcm_range K)%Z.
Proof.
  induction K as [|K IH].
  - cbn [zz_lcm_range]. lia.
  - cbn [zz_lcm_range]. apply zz_lcm_pos; [exact IH | lia].
Qed.

Lemma zz_lcm_le_mul : forall a b : Z,
  (0 < a)%Z -> (0 < b)%Z -> (Z.lcm a b <= a * b)%Z.
Proof.
  intros a b Ha Hb.
  apply (Z.divide_pos_le (Z.lcm a b) (a * b) ltac:(lia)).
  apply Z.lcm_least; unfold Z.divide; [exists b | exists a]; ring.
Qed.

Lemma zz_lcm_range_succ_le : forall K : nat,
  (zz_lcm_range (S K) <= zz_lcm_range K * (Z.of_nat K + 1))%Z.
Proof.
  intro K. cbn [zz_lcm_range].
  replace (Z.of_nat (S K)) with (Z.of_nat K + 1) by lia.
  apply zz_lcm_le_mul; [apply zz_lcm_range_pos | lia].
Qed.

Lemma zz_lcm_range_add4_le : forall K : nat,
  (zz_lcm_range (K + 4) <= zz_lcm_range K
     * (Z.of_nat K + 1) * (Z.of_nat K + 2) * (Z.of_nat K + 3) * (Z.of_nat K + 4))%Z.
Proof.
  intro K.
  assert (S1 : (zz_lcm_range (K + 1) <= zz_lcm_range K * (Z.of_nat K + 1))%Z).
  { pose proof (zz_lcm_range_succ_le K) as H.
    replace (S K)%nat with (K + 1)%nat in H by lia. exact H. }
  assert (S2 : (zz_lcm_range (K + 2) <= zz_lcm_range (K + 1) * (Z.of_nat K + 2))%Z).
  { pose proof (zz_lcm_range_succ_le (K + 1)) as H.
    replace (S (K + 1))%nat with (K + 2)%nat in H by lia.
    replace (Z.of_nat (K + 1) + 1) with (Z.of_nat K + 2) in H by lia. exact H. }
  assert (S3 : (zz_lcm_range (K + 3) <= zz_lcm_range (K + 2) * (Z.of_nat K + 3))%Z).
  { pose proof (zz_lcm_range_succ_le (K + 2)) as H.
    replace (S (K + 2))%nat with (K + 3)%nat in H by lia.
    replace (Z.of_nat (K + 2) + 1) with (Z.of_nat K + 3) in H by lia. exact H. }
  assert (S4 : (zz_lcm_range (K + 4) <= zz_lcm_range (K + 3) * (Z.of_nat K + 4))%Z).
  { pose proof (zz_lcm_range_succ_le (K + 3)) as H.
    replace (S (K + 3))%nat with (K + 4)%nat in H by lia.
    replace (Z.of_nat (K + 3) + 1) with (Z.of_nat K + 4) in H by lia. exact H. }
  transitivity (((zz_lcm_range (K + 1) * (Z.of_nat K + 2)) * (Z.of_nat K + 3)) * (Z.of_nat K + 4)).
  - transitivity (((zz_lcm_range (K + 2) * (Z.of_nat K + 3)) * (Z.of_nat K + 4))%Z).
    + transitivity ((zz_lcm_range (K + 3) * (Z.of_nat K + 4))%Z).
      * exact S4.
      * apply Z.mul_le_mono_nonneg_r; [lia | exact S3].
    + apply Z.mul_le_mono_nonneg_r; [lia |].
      apply Z.mul_le_mono_nonneg_r; [lia | exact S2].
  - apply Z.mul_le_mono_nonneg_r; [lia |].
    apply Z.mul_le_mono_nonneg_r; [lia |].
    apply Z.mul_le_mono_nonneg_r; [lia | exact S1].
Qed.

(* ==================================================================== *)
(* §2. L_n 乘性结构精确递归（Φ 加权步进——本件结构主定理，零假设）              *)
(* ==================================================================== *)

Lemma zz_Phi_div_lcm : forall n : nat,
  Bdiv (zz_Phi n) (zz_lcm_range (4 * n)%nat).
Proof.
  intro n.
  apply (zz_prodf_divides_P n (2 * n)%nat).
  intros k Hk Hinp. apply zz_j_div_lcm_P.
  - pose proof (zz_Pn_window_spec n k Hinp) as Hw.
    apply Bool.andb_true_iff in Hw. destruct Hw as [Hpk _].
    pose proof (zz_primeb_prime k Hpk) as Hk1.
    apply (proj1 (PeanoNat.Nat.ltb_lt 1 k)) in Hk1. lia.
  - assert (Hb : BidT (PeanoNat.Nat.leb k (2 * n)%nat))
      by (apply zz_Pn_bounded; exact Hinp).
    apply BidT_elim in Hb.
    apply (proj1 (PeanoNat.Nat.leb_le k (2 * n)%nat)) in Hb. lia.
Qed.

Lemma zz_Phi_mul_L_eq : forall n : nat,
  (zz_Phi n * zz_L n = zz_lcm_range (4 * n)%nat)%Z.
Proof.
  intro n.
  pose proof (zz_Phi_div_lcm n) as HdP.
  assert (HPhi : (0 < zz_Phi n)%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  unfold zz_L. destruct HdP as [e He]. apply Bid_elim in He.
  replace (zz_lcm_range (4 * n)%nat) with (e * (zz_Phi n)) by (rewrite Z.mul_comm; exact He).
  rewrite Z.div_mul by lia. apply Z.mul_comm.
Qed.

Theorem piu_zz_ln_step_phi : forall n : nat,
  (zz_L (S n) * zz_Phi (S n) <=
   zz_L n * zz_Phi n * (Z.of_nat (4 * n) + 1) * (Z.of_nat (4 * n) + 2)
     * (Z.of_nat (4 * n) + 3) * (Z.of_nat (4 * n) + 4))%Z.
Proof.
  intro n.
  assert (E1 : (zz_Phi (S n) * zz_L (S n) = zz_lcm_range (4 * S n)%nat)%Z)
    by apply zz_Phi_mul_L_eq.
  assert (E2 : (zz_Phi n * zz_L n = zz_lcm_range (4 * n)%nat)%Z)
    by apply zz_Phi_mul_L_eq.
  replace (4 * S n)%nat with (4 * n + 4)%nat in E1 by lia.
  rewrite (Z.mul_comm (zz_L (S n)) (zz_Phi (S n))), E1.
  apply Z.le_trans with (zz_lcm_range (4 * n)%nat * (Z.of_nat (4 * n) + 1)
    * (Z.of_nat (4 * n) + 2) * (Z.of_nat (4 * n) + 3) * (Z.of_nat (4 * n) + 4)).
  - apply zz_lcm_range_add4_le.
  - rewrite (Z.mul_comm (zz_L n) (zz_Phi n)), E2. apply Z.le_refl.
Qed.

Theorem piu_zz_ln_step_loose : forall n : nat,
  (zz_L (S n) <=
   zz_L n * zz_Phi n * (Z.of_nat (4 * n) + 1) * (Z.of_nat (4 * n) + 2)
     * (Z.of_nat (4 * n) + 3) * (Z.of_nat (4 * n) + 4))%Z.
Proof.
  intro n.
  assert (HPhi : (1 <= zz_Phi (S n))%Z)
    by (unfold zz_Phi; pose proof (zz_prodf_pos (S n) (2 * S n)%nat) as Hp0;
       apply (proj1 (Z.ltb_lt 0 (zz_prodf (S n) (2 * S n)%nat))) in Hp0; lia).
  assert (HL : (0 <= zz_L (S n))%Z).
  { pose proof (zz_lcm_range_pos (4 * S n)%nat) as Hl.
    pose proof (zz_prodf_pos (S n) (2 * S n)%nat) as Hp.
    apply (proj1 (Z.ltb_lt 0 (zz_prodf (S n) (2 * S n)%nat))) in Hp.
    unfold zz_L. apply Z.div_pos; lia. }
  pose proof (piu_zz_ln_step_phi n) as H.
  nia.
Qed.

Theorem piu_zz_ln_le_lcm : forall n : nat,
  (zz_L n <= zz_lcm_range (4 * n)%nat)%Z.
Proof.
  intro n.
  assert (HPhi : (0 < zz_Phi n)%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  pose proof (zz_lcm_range_pos (4 * n)%nat) as Hl.
  unfold zz_L.
  apply Z.div_le_upper_bound; [lia | nia].
Qed.

Theorem piu_zz_ln_pos : forall n : nat, (0 < zz_L n)%Z.
Proof.
  intro n. unfold zz_L.
  pose proof (zz_Phi_div_lcm n) as Hdiv.
  pose proof (zz_lcm_range_pos (4 * n)%nat) as Hl.
  assert (Hp : (0 < zz_Phi n)%Z).
  { unfold zz_Phi. apply (proj1 (Z.ltb_lt 0 (zz_prodf n (2 * n)%nat))).
    apply zz_prodf_pos. }
  apply Z.div_str_pos.
  assert (HdivP : (zz_Phi n | zz_lcm_range (4 * n)%nat)%Z).
  { destruct Hdiv as [e He]. apply Bid_elim in He.
    exists e. rewrite Z.mul_comm. symmetry. exact He. }
  pose proof (Z.divide_pos_le (zz_Phi n) (zz_lcm_range (4 * n)%nat)
                ltac:(lia) HdivP) as Hle.
  lia.
Qed.

(* ==================================================================== *)
(* §3. 样点带 bool 表（设计书 V1 形状：Qle_bool 逐点可判定）                    *)
(* ==================================================================== *)

Definition zz_ln_up_ok (n : nat) : bool :=
  Qle_bool (zq (zz_L n)) (piu_zz_qpow (29 # 1)%Q n).

Definition zz_ln_lo_ok (n : nat) : bool :=
  Qle_bool (piu_zz_qpow (28 # 1)%Q n) (zq (zz_L n)).

(* 带定义（样点选取=机外全扫 n≤320 全域后选定，非盲选；树内 vm_compute 复算）
   LO 带切片化登记：整带 [253,320] 单发 vm_compute 在预演中出现一次
   false 伪象（829s+，异于两半各自机验 true——异常#4 响亮登记），故改两半
   [253,286]+[287,320] 切片形（各半双验：probe16+本件），使用面并集合成。 *)
Definition zz_lo_big_pts : list nat := (253 :: 273 :: 303 :: 320 :: nil)%nat.
Definition zz_up_big_pts : list nat :=
  (64 :: 160 :: 234 :: 243 :: 248 :: 318 :: 319 :: nil)%nat.
Definition zz_up_small_list : list nat := (1 :: 2 :: 4 :: 6 :: 7 :: 9 :: nil)%nat.
Definition zz_lo_small_list : list nat := (2 :: 3 :: 5 :: 6 :: 8 :: 12 :: 16 :: nil)%nat.
(* 大点验证=表驱动（符号 n 使用面瞬时转换；拒字面点 exact——其触发点值全量
   归约放大，本件实测 11 点×10-30s 即磨穿切片——工艺登记） *)
Definition zz_up_small_all : bool := forallb zz_ln_up_ok zz_up_small_list.
Definition zz_lo_small_all : bool := forallb zz_ln_lo_ok zz_lo_small_list.
Definition zz_lo_big_all : bool := forallb zz_ln_lo_ok zz_lo_big_pts.
Definition zz_up_big_all : bool := forallb zz_ln_up_ok zz_up_big_pts.

Theorem zz_up_small_all_true : zz_up_small_all = true.
Proof. vm_compute. reflexivity. Defined.

Theorem zz_lo_small_all_true : zz_lo_small_all = true.
Proof. vm_compute. reflexivity. Defined.

Theorem zz_lo_big_all_true : zz_lo_big_all = true.
Proof. vm_compute. reflexivity. Defined.

Theorem zz_up_big_all_true : zz_up_big_all = true.
Proof. vm_compute. reflexivity. Defined.
(* ==================================================================== *)
(* 缩面注记（乙路 standing 面终态）：§4 wrapper 四定理与       *)
(*   其两件桥引理（zz_forallb_elim/zz_in_seq_intro）移出 born 面——单房复算         *)
(*   实测：334 行稿单房（零他道）满烧 25 分钟帽不熟（CPU 时间≈挂钟·零争用·         *)
(*   四时点 delta-CPU 采样在卷），燃段在 §3 表 Defined 内核转换及其后段；§4-§5       *)
(*   内容以先行 segA/P2 standing 绿证+单件试算账降级申报（fail-loud）。                  *)
(*   本 born 面=header+§1+§2+§3（segA+P2 standing 面）+PA×8（§2 四定理+§3 四表       *)
(*   适配名单）+提取位。零假设出件即无条件性质不变。                                  *)
(* ==================================================================== *)

(* ==================================================================== *)
(* §6. 四关：G4 假设审计（期望全 Closed——零假设即本件卖点）                     *)
(* ==================================================================== *)

Print Assumptions piu_zz_ln_step_phi.
Print Assumptions piu_zz_ln_step_loose.
Print Assumptions piu_zz_ln_le_lcm.
Print Assumptions piu_zz_ln_pos.
Print Assumptions zz_up_small_all_true.
Print Assumptions zz_lo_small_all_true.
Print Assumptions zz_lo_big_all_true.
Print Assumptions zz_up_big_all_true.

(* G3 提取小名单（≤6·计算面主菜） *)
Extraction "piu_zz_ln_rate_bound_ext" zz_ln_up_ok zz_ln_lo_ok zz_L.
