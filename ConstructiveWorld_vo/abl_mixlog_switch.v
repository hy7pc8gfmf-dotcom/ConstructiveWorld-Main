(* ==========================================================================)
   abl_mixlog_switch.v — vm_compute 数值档散布件的通用切换档泛化首件
   使命：把 UpReqMixLogE.v 的 91/22 锐化差距面（mixe_smoke_select_cert_91／
      mixe_smoke_true_min_22，L726-740）接入通用切换档定理 igr_k_enum_min
      （UpReqIterGeomRate.v:1576 现档；:1537 为四件之首 igr_k_enum_sound）：
      立「接受站计算器 msw_min_station＝igr_k_enum 泛型枚举 × mixe_qlt_bool
      真值测试」，交付健全／最小／无解三支正确性账、Q 层单调步进切换面
      （对 k 无上界全通过段）、族形状总件 msw_switch_tier，及 91/22 实例
      回核——22 档经通用接口重证、91 档接受面由 22 档＋切换面导出（非直算），
      仿射闭式档 91 本身化作枚举窗口（mixe_cf_select 直供 H）。
   依赖清单：Stdlib QArith/ZArith/Lia/Extraction；本库 UpReqIterGeomRate
      （igr_k_enum/sound/none/min 泛用切换档件，经 -Q 世界树使用）、
      UpReqMixLogE（mixe_qlt_bool/mixe_qpow/mixe_cf_select/mixe_qle_01 及序账
      传输件）。两层差异如实记录：igr 四件为 nat/bool/option 层（与 Q 无关的
      纯枚举形），mixe 面为 Q 层序谓词——桥由 msw_mix_test 一处承担（Q 层测试
      交由 nat 层枚举按 test : nat -> bool 接口调用）。
   对标行：UpReqMixLogE L722-740 坐标（mixe_cf_select／mixe_smoke_* 两实例）；
      UpReqIterGeomRate :1516/:1537/:1554/:1576 坐标（igr 切换档四件）。
   构造性注记：计算器面全 Set 型（bool/option/Fixpoint/Defined，可提取）；
      账面等式与 igr 族同形（Id bool）；Qlt/Qle 释读件与 mixe 族同层（stdlib
      Q 序谓词）。零承认词面、零经典逻辑、零新增公理；全件无否定记号词，
      前提一律 forall 显式。
   编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s
      65532 && nice -19 rocq c -native-compiler no -Q
      /Users/apple/Desktop/ConstructiveWorld/vo_local_world_unified_0930 ""
      abl_mixlog_switch.v（池内平铺，并发 1＝单进程串行）；验证＝EXIT=0＋
      Print Assumptions 全 Closed。
   查重登记：顶层名 28 枚全 msw_ 新前缀，与库内既占前缀零撞零别名转发；
      91/22 实例回核三 Example 一窗两站零重复。
   ========================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import UpReqIterGeomRate.
Require Import UpReqMixLogE.

Local Open Scope Q_scope.

(* ============================================================ *)
(* Part 1：泛型切换档计算器（Set 面：nat 层枚举 × Q 层真值测试）      *)
(*   枚举器直接使用 igr_k_enum（UpReqIterGeomRate.v:1516 现档），       *)
(*   测试为 mixe 真值面 (1-w)^k·tv0 < b0 的 bool 判定。计算器对        *)
(*   w/tv0/b0 全泛化——任意精度档的接受站计算器。                      *)
(* ============================================================ *)

Definition msw_mix_test (w tv0 b0 : Q) (k : nat) : bool :=
  mixe_qlt_bool (mixe_qpow (1 - w) k * tv0) b0.

Definition msw_min_station (w tv0 b0 : Q) (H : nat) : option nat :=
  igr_k_enum (msw_mix_test w tv0 b0) H.

(* 健全支：返回站必通过（直取使用 igr_k_enum_sound:1537） *)
Lemma msw_station_sound : forall (w tv0 b0 : Q) (H k : nat),
  msw_min_station w tv0 b0 H = Some k -> msw_mix_test w tv0 b0 k = true.
Proof.
  intros w tv0 b0 H k Hsel. unfold msw_min_station in Hsel.
  exact (igr_k_enum_sound (msw_mix_test w tv0 b0) H k Hsel).
Qed.

(* 最小支：返回站以下全不通过（直取使用 igr_k_enum_min:1576） *)
Lemma msw_station_min : forall (w tv0 b0 : Q) (H k j : nat),
  msw_min_station w tv0 b0 H = Some k -> (j < k)%nat ->
  msw_mix_test w tv0 b0 j = false.
Proof.
  intros w tv0 b0 H k j Hsel Hjk. unfold msw_min_station in Hsel.
  exact (igr_k_enum_min (msw_mix_test w tv0 b0) H k Hsel j Hjk).
Qed.

(* 无解支：窗内全不通过（直取使用 igr_k_enum_none:1554） *)
Lemma msw_station_none : forall (w tv0 b0 : Q) (H j : nat),
  msw_min_station w tv0 b0 H = None -> (j <= H)%nat ->
  msw_mix_test w tv0 b0 j = false.
Proof.
  intros w tv0 b0 H j Hnone Hj. unfold msw_min_station in Hnone.
  exact (igr_k_enum_none (msw_mix_test w tv0 b0) H Hnone j Hj).
Qed.

(* ============================================================ *)
(* Part 2：bool 账与 Q 序面的双桥（mixe 族同层释读件）                 *)
(* ============================================================ *)

Lemma msw_test_true_lt : forall (w tv0 b0 : Q) (k : nat),
  msw_mix_test w tv0 b0 k = true -> Qlt (mixe_qpow (1 - w) k * tv0) b0.
Proof.
  intros w tv0 b0 k Hk. unfold msw_mix_test in Hk.
  exact (mixe_qlt_bool_of_true _ _ Hk).
Qed.

(* totality 桥：stdlib Qlt_le_dec {x<y}+{y<=x} 右支即下界证书 *)
Lemma msw_test_false_ge : forall (w tv0 b0 : Q) (j : nat),
  msw_mix_test w tv0 b0 j = false -> Qle b0 (mixe_qpow (1 - w) j * tv0).

Proof.
  intros w tv0 b0 j Hj. unfold msw_mix_test, mixe_qlt_bool in Hj.
  destruct (Qlt_le_dec (mixe_qpow (1 - w) j * tv0) b0) as [Hd | Hd].
  - discriminate Hj.
  - exact Hd.
Qed.

(* ============================================================ *)
(* Part 3：单调步进与切换面（统一陈述的「∀k≥k* 段成立」支）            *)
(*   igr 接口自身不含单调输入；此支是接入 mixe 数值档的增量成本        *)
(*   （诚实边界注记）。                                                *)
(* ============================================================ *)

Lemma msw_qpow_step_le : forall (w tv0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  Qle (mixe_qpow (1 - w) (Datatypes.S k) * tv0) (mixe_qpow (1 - w) k * tv0).
Proof.
  intros w tv0 k Hw0 Hw1 Htv0.
  assert (Hbase : Qle 0 (1 - w)) by exact (mixe_sub_nonneg w Hw1).
  assert (Hlow : Qle (1 - w) 1) by exact (mixe_le_sub 1 w Hw0).
  assert (HP : Qle 0 (mixe_qpow (1 - w) k))
    by exact (mixe_qpow_nonneg (1 - w) k Hbase).
  cbn [mixe_qpow].
  apply (mixe_qle_eq_r ((1 - w) * mixe_qpow (1 - w) k * tv0)
           (1 * mixe_qpow (1 - w) k * tv0)
           (mixe_qpow (1 - w) k * tv0)).
  - apply (Qmult_le_compat_r ((1 - w) * mixe_qpow (1 - w) k)
             (1 * mixe_qpow (1 - w) k) tv0).
    + exact (Qmult_le_compat_r (1 - w) 1 (mixe_qpow (1 - w) k) Hlow HP).
    + exact Htv0.
  - rewrite (Qmult_1_l (mixe_qpow (1 - w) k)). reflexivity.
Qed.

Lemma msw_test_step : forall (w tv0 b0 : Q) (k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  msw_mix_test w tv0 b0 k = true -> msw_mix_test w tv0 b0 (Datatypes.S k) = true.
Proof.
  intros w tv0 b0 k Hw0 Hw1 Htv0 Hk.
  apply mixe_qlt_bool_true.
  apply (Qle_lt_trans (mixe_qpow (1 - w) (Datatypes.S k) * tv0)
           (mixe_qpow (1 - w) k * tv0) b0).
  - exact (msw_qpow_step_le w tv0 k Hw0 Hw1 Htv0).
  - exact (msw_test_true_lt w tv0 b0 k Hk).
Qed.

Lemma msw_test_add_d : forall (w tv0 b0 : Q) (d k : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  msw_mix_test w tv0 b0 k = true -> msw_mix_test w tv0 b0 (k + d) = true.
Proof.
  intros w tv0 b0 d. induction d as [| d IH]; intros k Hw0 Hw1 Htv0 Hk.
  - rewrite (Nat.add_0_r k). exact Hk.
  - replace ((k + Datatypes.S d)%nat) with ((Datatypes.S (k + d))%nat) by lia.
    apply msw_test_step.
    + exact Hw0.
    + exact Hw1.
    + exact Htv0.
    + exact (IH k Hw0 Hw1 Htv0 Hk).
Qed.

(* 切换面：返回站 k* 起、对 k 无上界全通过——切换档语义的完成支 *)
Theorem msw_station_switch : forall (w tv0 b0 : Q) (H k j : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  msw_min_station w tv0 b0 H = Some k -> (k <= j)%nat ->
  msw_mix_test w tv0 b0 j = true.
Proof.
  intros w tv0 b0 H k j Hw0 Hw1 Htv0 Hsel Hkj.
  replace j with ((k + (j - k))%nat) by lia.
  apply (msw_test_add_d w tv0 b0 (j - k)%nat k Hw0 Hw1 Htv0).
  exact (msw_station_sound w tv0 b0 H k Hsel).
Qed.

(* 族形状总件（统一陈述的落地形；三支全 Set 承载账面） *)
Theorem msw_switch_tier : forall (w tv0 b0 : Q) (H : nat),
  Qle 0 w -> Qle w 1 -> Qle 0 tv0 ->
  match msw_min_station w tv0 b0 H with
  | Some k => msw_mix_test w tv0 b0 k = true /\
              (forall j : nat, (j < k)%nat -> msw_mix_test w tv0 b0 j = false) /\
              (forall j : nat, (k <= j)%nat -> msw_mix_test w tv0 b0 j = true)
  | None => forall j : nat, (j <= H)%nat -> msw_mix_test w tv0 b0 j = false
  end.
Proof.
  intros w tv0 b0 H Hw0 Hw1 Htv0.
  destruct (msw_min_station w tv0 b0 H) as [k |] eqn:E.
  - split.
    + exact (msw_station_sound w tv0 b0 H k E).
    + split.
      * intros j Hjk. exact (msw_station_min w tv0 b0 H k j E Hjk).
      * intros j Hkj.
        exact (msw_station_switch w tv0 b0 H k j Hw0 Hw1 Htv0 E Hkj).
  - intros j Hj. exact (msw_station_none w tv0 b0 H j E Hj).
Qed.

(* ============================================================ *)
(* Part 4：枚举窗保 extends（窗只决定搜索上界，不改首过站）            *)
(* ============================================================ *)

Lemma msw_enum_succ_some : forall (test : nat -> bool) (t k : nat),
  igr_k_enum test t = Some k -> igr_k_enum test (Datatypes.S t) = Some k.
Proof.
  intros test t k H. cbn [igr_k_enum]. rewrite H. reflexivity.
Qed.

Lemma msw_enum_window_mono : forall (test : nat -> bool) (d t k : nat),
  igr_k_enum test t = Some k -> igr_k_enum test (t + d) = Some k.
Proof.
  intros test d. induction d as [| d IH]; intros t k H.
  - rewrite (Nat.add_0_r t). exact H.
  - replace ((t + Datatypes.S d)%nat) with ((Datatypes.S (t + d))%nat) by lia.
    apply msw_enum_succ_some. apply IH. exact H.
Qed.

(* ============================================================ *)
(* Part 5：91/22 实例回核（vm_compute 定装档位面 + 切换结构导出面）     *)
(*   实例参数：w = 1/10，tv0 = 1，b0 = 1/10（mixe L722-740 现档）。     *)
(* ============================================================ *)

Lemma msw_qle_tenth_pos : Qle 0 (1 # 10).
Proof. unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

Lemma msw_qle_tenth_le_one : Qle (1 # 10) 1.
Proof. unfold Qle. cbn [Qnum Qden Z.mul Pos.mul]. lia. Qed.

(* 窗口＝仿射闭式档本身：mixe_cf_select 直供 H（91 档化作搜索窗） *)
Example msw_smoke_station_in_affine_window :
  msw_min_station (1 # 10) 1 (1 # 10) (mixe_cf_select (1 # 10) (1 # 10) 1)
    = Some 22%nat.
Proof. vm_compute. reflexivity. Qed.

Example msw_smoke_station_tight_22 :
  msw_min_station (1 # 10) 1 (1 # 10) 22 = Some 22%nat.
Proof. vm_compute. reflexivity. Qed.

Example msw_smoke_window_21_none :
  msw_min_station (1 # 10) 1 (1 # 10) 21 = None.
Proof. vm_compute. reflexivity. Qed.

(* 任意窗 H ≥ 22 皆返回真最小站 22（窗口泛化件） *)
Theorem msw_station_22_any_window : forall H : nat,
  (22 <= H)%nat -> msw_min_station (1 # 10) 1 (1 # 10) H = Some 22%nat.
Proof.
  intros H Hge. unfold msw_min_station.
  replace H with ((22 + (H - 22))%nat) by lia.
  exact (msw_enum_window_mono (msw_mix_test (1 # 10) 1 (1 # 10))
           (H - 22)%nat 22 22 msw_smoke_station_tight_22).
Qed.

(* ---- (1 - 1/10) 与 9/10 的三项具体桥（vm_compute 定装，闭式形） ---- *)

Lemma msw_eq_21 :
  mixe_qpow (1 - (1 # 10)) 21 * 1 == mixe_qpow (9 # 10) 21 * 1.
Proof. vm_compute. reflexivity. Qed.

Lemma msw_eq_22 :
  mixe_qpow (1 - (1 # 10)) 22 * 1 == mixe_qpow (9 # 10) 22 * 1.
Proof. vm_compute. reflexivity. Qed.

Lemma msw_eq_91 :
  mixe_qpow (1 - (1 # 10)) 91 * 1 == mixe_qpow (9 # 10) 91 * 1.
Proof. vm_compute. reflexivity. Qed.

(* 22 档真值证书：经通用接口（枚举健全支）重证 mixe_smoke_true_min_22 语义 *)
Theorem msw_true_min_22 : Qlt (mixe_qpow (9 # 10) 22 * 1) (1 # 10).
Proof.
  apply (mixe_qlt_eq_l (mixe_qpow (9 # 10) 22 * 1)
           (mixe_qpow (1 - (1 # 10)) 22 * 1) (1 # 10)).
  - exact msw_eq_22.
  - apply (msw_test_true_lt (1 # 10) 1 (1 # 10) 22).
    exact (msw_station_sound (1 # 10) 1 (1 # 10)
             (mixe_cf_select (1 # 10) (1 # 10) 1) 22
             msw_smoke_station_in_affine_window).
Qed.

(* 21 档下界账：经通用接口（igr_k_enum_min 最小支）——锐化差距的反面证实 *)
Theorem msw_below_21_not_accept : Qle (1 # 10) (mixe_qpow (9 # 10) 21 * 1).
Proof.
  apply (mixe_qle_eq_r (1 # 10) (mixe_qpow (1 - (1 # 10)) 21 * 1)
           (mixe_qpow (9 # 10) 21 * 1)).
  - apply (msw_test_false_ge (1 # 10) 1 (1 # 10) 21).
    apply (msw_station_min (1 # 10) 1 (1 # 10)
             (mixe_cf_select (1 # 10) (1 # 10) 1) 22 21
             msw_smoke_station_in_affine_window).
    lia.
  - exact msw_eq_21.
Qed.

(* 21 窗无解账：None 支的使用面 *)
Theorem msw_below_21_all_fail : forall j : nat,
  (j <= 21)%nat -> msw_mix_test (1 # 10) 1 (1 # 10) j = false.
Proof.
  intros j Hj. apply (msw_station_none (1 # 10) 1 (1 # 10) 21 j).
  - exact msw_smoke_window_21_none.
  - exact Hj.
Qed.

(* 91 档接受证书：由 22 档＋切换面导出（station_switch），非对 91 直算 *)
Theorem msw_affine_cert_91 : Qlt (mixe_qpow (9 # 10) 91 * 1) (1 # 10).
Proof.
  apply (mixe_qlt_eq_l (mixe_qpow (9 # 10) 91 * 1)
           (mixe_qpow (1 - (1 # 10)) 91 * 1) (1 # 10)).
  - exact msw_eq_91.
  - apply (msw_test_true_lt (1 # 10) 1 (1 # 10) 91).
    apply (msw_station_switch (1 # 10) 1 (1 # 10)
             (mixe_cf_select (1 # 10) (1 # 10) 1) 22 91
             msw_qle_tenth_pos msw_qle_tenth_le_one mixe_qle_01
             msw_smoke_station_in_affine_window).
    lia.
Qed.

(* 91 档 bool 面（mixe_smoke_select_cert_91 同文）：切换导出重证版 *)
Example msw_select_cert_91_bool_switched :
  mixe_qlt_bool (mixe_qpow (9 # 10) 91 * 1) (1 # 10) = true.
Proof. apply mixe_qlt_bool_true. exact msw_affine_cert_91. Qed.

(* ============================================================ *)
(* 审计口（全 Closed 预期：零新增公理；并审计核心件 igr_k_enum_min）    *)
(* ============================================================ *)

Print Assumptions msw_station_sound.
Print Assumptions msw_station_min.
Print Assumptions msw_station_none.
Print Assumptions msw_test_true_lt.
Print Assumptions msw_test_false_ge.
Print Assumptions msw_qpow_step_le.
Print Assumptions msw_test_step.
Print Assumptions msw_test_add_d.
Print Assumptions msw_station_switch.
Print Assumptions msw_switch_tier.
Print Assumptions msw_enum_window_mono.
Print Assumptions msw_station_22_any_window.
Print Assumptions msw_true_min_22.
Print Assumptions msw_below_21_not_accept.
Print Assumptions msw_below_21_all_fail.
Print Assumptions msw_affine_cert_91.
Print Assumptions msw_select_cert_91_bool_switched.
Print Assumptions igr_k_enum_min.
Print Assumptions igr_k_enum_sound.
Print Assumptions igr_k_enum_none.

(* 提取面：计算器本体（可提取强证；Obj.magic 计数由壳层核对） *)
From Stdlib Require Extraction.
Separate Extraction msw_min_station.
