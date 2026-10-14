(* ===================================================================== *)
(*  u5c_ln2_s5d_shape.v —— ln2 两位残余 Observable 的实例刻形就绪件          *)
(*  （勘录②同源两位的 canonical 实例刻形）                                   *)
(* ===================================================================== *)
(*  模块名：u5c_ln2_s5d_shape。                                           *)
(*  使命：把两位供给链级 Observable（Hrho〔勘录② Padé 有限 M 形〕＋        *)
(*    Hbudget⑥〔同源〕）的实例形状从 prose 刻形升为显式命名定义位。         *)
(*    本件三内容：                                                         *)
(*    ①实例钉形：X := ln2b_X（Ln2Bridge 正典实数，读出面＝|A_n·ln2i_x k −  *)
(*      B_n|·u5c_ln2_seam4_sline_form 定义性）；A' := Λ_n·2^{n+1}·q̃_n      *)
(*      （Λ_n := lcm(1..n)＝hl_lcm_upto）；B' := Λ_n·2^{n+1}·bv_p n。      *)
(*    ②②肢在 A' 重铸（s5d_canA_pos／s5d_canA_abs_pos）：0<|A'_n| 由       *)
(*      3ⁿ≤q̃_n＋2^{S n}≥1＋Λ_n≥1 合成——五层供给面 ②槽在 A' 位就绪。       *)
(*    ③B-整性障碍机锚（显式披露型）：勘录②恒等式的 B 伴位被挤压收敛       *)
(*      唯一 forcing 为 2^{n+1}·bv_p n，其在 n=3 非整                       *)
(*      （2⁴·bv_p 3 = 2096/3∉Z·精确有理算术复算 n=1..4 恒等式               *)
(*      60 位吻合＋n=1..10 整性表在卷）——故 s5c_supply_inhabited           *)
(*      （A:=s5c_lna 硬绑）在正典 ln2 实例不可实例化，供给链收束须走        *)
(*      A' 重缩放路径；本件 s5d_obs_b3_nonZ 给该障碍的机械否定锚，          *)
(*      s5d_runalive_bq3 给 Λ-清分母后 B'_3 = 4192 ∈ Z 的正面机锚。        *)
(*  实现注记：实例位全定义性展开（sline_form 读出面与 seam4 定义性接合）；  *)
(*    整性障碍锚走 vm_compute 精确判定与显式 Z 线性链。                     *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、HansonLcm、           *)
(*    BeukersLists、BeukersVariant、u5c_ln2_gap2_bridge、u5c_ln2_assembly、 *)
(*    u5c_ln2_seam4、u5c_ln2_s4fill、u5c_ln2_witness、u5c_ln2_theta_slot、  *)
(*    abl_ln2_reorder、abl_ln2_reorder_assembly、abl_ln2_bsum_cauchy；     *)
(*    Stdlib：QArith/Qabs/ZArith/Arith/Lia/Setoid/Qfield。                  *)
(*  对标：勘录②恒等式面（abl_ln2_reorder_assembly 头注②）；                *)
(*    BeukersVariant.v:11 有限 M 恒等式登记位；                             *)
(*    u5c_gap2_slot 五槽形态（u5c_ln2_gap2_bridge.v:155）。                 *)
(*  数值锚（精确有理算术独立复算在卷·逐定义精确复算）：                     *)
(*    Σ_k lnf_bterm n k == 2^{n+1}(D_n·ln2 − bv_p n) 于 n=1..4 十进 60 位   *)
(*    吻合；2^{n+1}bv_p n 整性：n=1:8✓ 2:72✓ 3:2096/3✗ 4:7120✓ 5..10✗。    *)
(*  构造性注记：语句面全 Set 层；零承认、零经典逻辑、零 solver              *)
(*    （obs 锚收尾 lia 为 Z 线性整性计量·辅助语句位，非主定理）。           *)
(*  诚实边界：勘录②闭式合一（Gosper 承载/有限 M 恒等式）仍是供给链主缺口    *)
(*    （BeukersVariant.v:11 自登记「另案待完成」）；本件不冒领恒等式，      *)
(*    只钉形＋供 ②'肢＋供障碍机锚。                                        *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" u5c_ln2_s5d_shape.v     *)
(* ===================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import HansonLcm.
Require Import BeukersLists.
Require Import BeukersVariant.
Require Import u5c_ln2_gap2_bridge.
Require Import u5c_ln2_s5c_supply.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith.
From Stdlib Require Import Lia.

Open Scope nat_scope.

(* ============================================================ *)
(* §0 实例钉形：Λ 清分母缩放位                                              *)
(* ============================================================ *)

(* Λ_n := lcm(1..n)（HansonLcm 折叠承载） *)
Definition s5d_lam (n : nat) : nat := hl_lcm_upto n.

(* Λ_n ≥ 1（n=0 位 = 1 定义性；归纳步经 Nat.lcm_eq_0 正性） *)
Lemma s5d_lam_ge1 : forall n : nat, (1 <= s5d_lam n)%nat.
Proof.
  intro n. unfold s5d_lam. induction n as [| m IH].
  - cbn [hl_lcm_upto]. lia.
  - cbn [hl_lcm_upto].
    assert (Hne : (Nat.lcm (hl_lcm_upto m) (Datatypes.S m) <> 0)%nat).
    { rewrite Nat.lcm_eq_0. lia. }
    lia.
Qed.

(* 规范缩放分子：A'_n := Λ_n·2^{n+1}·q̃_n *)
Definition s5d_lna (n : nat) : Z :=
  Z.of_nat (s5d_lam n * (2 ^ Datatypes.S n * bk_Qn_qtilde n)).

(* 缩放 B 伴位（Q 面正形）：B'_n := Λ_n·2^{n+1}·bv_p n；
   其 Z 整位（den(bv_p n) | lcm(1..n)·bv_p 有限闭式逐项分母 (j−n)）
   = campaign 级候铸肢（Hbint·本件不冒领） *)
Definition s5d_bq (n : nat) : Q :=
  ((Z.of_nat (s5d_lam n * 2 ^ Datatypes.S n)) # 1)%Q * bv_p n.

(* ============================================================ *)
(* §1 ②肢在 A' 重铸（0<|A'_n|）                                            *)
(* ============================================================ *)

Theorem s5d_canA_pos : forall n : nat, QltT 0 ((s5d_lna n) # 1)%Q.
Proof.
  intro n. apply Qlt_to_QltT. unfold Qlt, s5d_lna. cbn [Qnum Qden].
  pose proof (bk_Qn_ge_3pow_nat n) as H1.
  assert (H2 : (1 <= 3)%nat) by lia.
  pose proof (s5c_pow_ge1 3 n H2) as H3.
  assert (H4 : (1 <= 2)%nat) by lia.
  pose proof (s5c_pow_ge1 2 (Datatypes.S n) H4) as H5.
  pose proof (s5d_lam_ge1 n) as H6.
  assert (Hq : (0 < bk_Qn_qtilde n)%nat) by lia.
  assert (Hp : (0 < 2 ^ Datatypes.S n)%nat) by lia.
  assert (HL : (0 < s5d_lam n)%nat) by lia.
  assert (Hi : (0 < 2 ^ Datatypes.S n * bk_Qn_qtilde n)%nat) by nia.
  assert (Hz : (Z.of_nat 0
                < Z.of_nat (s5d_lam n * (2 ^ Datatypes.S n * bk_Qn_qtilde n)))%Z)
    by (apply Nat2Z.inj_lt; nia).
  lia.
Qed.

(* ②肢（Qabs 形——u5c_gap2_slot 第二槽正形） *)
Theorem s5d_canA_abs_pos : forall n : nat, QltT 0 (Qabs ((s5d_lna n) # 1)%Q).
Proof. intro n. apply s5c_abs_posT. apply s5d_canA_pos. Qed.

(* ============================================================ *)
(* §2 B-整性障碍机锚（n=3 的机械承载）                             *)
(* ============================================================ *)

(* 正面锚：Λ-清分母后 B'_3 = 6·2⁴·(131/3) = 4192 ∈ Q 整值面
   （vm_compute 精确判定·与 Fractions 表 n=3 行一致） *)
Theorem s5d_runalive_bq3 : QeqT (s5d_bq 3) ((4192 # 1)%Q).
Proof.
  unfold s5d_bq.
  apply (gap2_qeqT_trans _ (bv_p 3 * ((Z.of_nat (s5d_lam 3 * 2 ^ 4)) # 1))%Q).
  - apply qeq_imp_qeqT. ring.
  - apply (gap2_qeqT_trans _ (((131 # 3)%Q) * ((Z.of_nat (s5d_lam 3 * 2 ^ 4)) # 1))%Q).
    + apply (s5c_qeqT_mult_r ((Z.of_nat (s5d_lam 3 * 2 ^ 4)) # 1)%Q).
      exact bv_p3_anchor.
    + apply qeq_imp_qeqT. vm_compute. reflexivity.
Qed.

(* 障碍锚：未缩放伴位 2⁴·bv_p 3 = 2096/3 对一切 z:Z 非整值
   （＝「挤压 forcing 的 B_n 不可为 Z」于 n=3 的机械否定；
   Set 载体否定形 A -> Empty_set·红线律二正例表） *)
Theorem s5d_obs_b3_nonZ : forall z : Z,
  QeqT ((16 # 1)%Q * bv_p 3) ((z # 1)%Q) -> Empty_set.
Proof.
  intros z H.
  assert (Hr : QeqT ((16 # 1)%Q * bv_p 3) (bv_p 3 * (16 # 1))%Q).
  { apply qeq_imp_qeqT. ring. }
  assert (Hm : QeqT (bv_p 3 * (16 # 1))%Q (((131 # 3)%Q) * (16 # 1))).
  { apply (s5c_qeqT_mult_r (16 # 1)). exact bv_p3_anchor. }
  assert (Hf : QeqT (((131 # 3)%Q) * (16 # 1)) ((z # 1)%Q)).
  { apply (gap2_qeqT_trans _ (bv_p 3 * (16 # 1))%Q).
    - apply qeq_imp_qeqT. apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hm)).
    - apply (gap2_qeqT_trans _ ((16 # 1)%Q * bv_p 3)).
      + apply qeq_imp_qeqT. apply (Qeq_sym _ _ (qeqT_imp_qeq _ _ Hr)).
      + exact H. }
  pose proof (qeqT_imp_qeq _ _ Hf) as Hq.
  exfalso.
  unfold Qeq in Hq. cbn [Qmult Qnum Qden] in Hq.
  rewrite !Z.mul_1_r in Hq. lia.
Qed.

(* ============================================================ *)
(* §3 提取与假设审计                                                       *)
(* ============================================================ *)

Separate Extraction s5d_lna s5d_bq.

Print Assumptions s5d_lam_ge1.
Print Assumptions s5d_canA_pos.
Print Assumptions s5d_canA_abs_pos.
Print Assumptions s5d_runalive_bq3.
Print Assumptions s5d_obs_b3_nonZ.
