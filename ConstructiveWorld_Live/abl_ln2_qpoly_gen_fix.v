(* ===================================================================== *)
(*  abl_ln2_qpoly_gen_fix.v —— DC·提取 Obj.magic=1 消解件               *)
(*     （Set 载体 bool 判定器；CV 件 abl_ln2_qpoly_gen.v 增补段）           *)
(*                                                                        *)
(*  ①使命: 闭合 CV 件提取瑕疵——lng_den_ok 之 Qcompare 消去在 OCaml 侧       *)
(*     的 1 处 Obj.magic（match-型擦除伪影）。判定（probe1/probe2 在卷）:   *)
(*     上游 qpg_leadne0 系 Set 级异支 match 型（Eq→Empty_set/Lt/Gt→unit），  *)
(*     提取擦形为 __=Obj.t；凡活路径（Lt/Gt）运行时承载体必经一次 Obj.magic  *)
(*     宽化（路线① sumbool 判定器改写=搬移、路线② 单名 Inline=搬移、闭式    *)
(*     vm_compute 证书=同伪影，三路实证均不可就地归零）。故消解走路线③:     *)
(*     新立 Set 载体 bool 判定件 lng_den_ok_bool（纯 bool 函数，零 magic）， *)
(*     与原证书双向等价桥接（iff），引擎使用面以 projT1 定义性一致衔接；     *)
(*     提取面改走 bool 判定器——Separate Extraction Obj.magic=0。            *)
(*  ②依赖: abl_tmine04_pool/qpoly_fix/（独占自建；五件链拷入    *)
(*     同池，编译序 divmod→numer_int→divmod_gen→consume→gen→本件；          *)
(*     CV 件本体零改动——append-only 承诺由「新建使用件」履行）。            *)
(*  ③编译配方: source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&         *)
(*     ulimit -s 65532 && nice -19 rocq c -native-compiler no             *)
(*     -Q <vo_local_world_unified_0930> "" -Q . "" 本件;                   *)
(*     起编前道闸 ps rocq 计 ≤1（本池编译全程串行）。                       *)
(*  ④构造性: 零公理零承认零放弃零经典（Print Assumptions 全列取证，         *)
(*     逐条 Closed under the global context）；交付面:                      *)
(*     - 提取面（Obj.magic=0）: lng_zneg2 + lng_den_ok_bool（纯 bool）；    *)
(*     - PA 面: 双向桥 lng_den_ok_bool_true_ok / lng_den_ok_ok_bool      *)
(*       （宇宙墙下以方向定理对承载等价，不立单条 Prop iff）; 引擎使用件   *)
(*       lng_div_gen_bool 及其与原 lng_div_gen 的                          *)
(*       projT1 定义性一致（lng_div_gen_bool_agree / lng_pin_bool_w4）。    *)
(*  ⑤边界: 原 lng_den_ok（依赖 match 型证书）不在本件提取面——其 OCaml       *)
(*     伪影为结构必剩（见①判定），PA 面原样保留于 CV 件（本件 iff 双向     *)
(*     桥保其定理面不减）；lng_div_gen_bool 全件本体（sigT 含 QeqT 载荷）   *)
(*     为 PA 面不提取（提取即回染 magic，判定在卷）；CV 件 §6 诚实边界      *)
(*     （d_1==2^n·q̃_n 全形等）沿袭不动。                                   *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qfield.
From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Lia Extraction.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp PolyIntegral.
Require Import BeukersLists.
Require Import abl_qpoly_divmod abl_qpoly_divmod_gen.
Require Import abl_ln2_numer_int.
Require Import abl_ln2_qpoly_consume.
Require Import abl_ln2_qpoly_gen.

Open Scope Q_scope.

(* ============================================================ *)
(* §1 Set 载体判定件（路线③; 纯 bool 函数——提取零 magic 载体）      *)
(* ============================================================ *)

(* 度≥1（Nat.ltb bool 面）∧ 真首项≠0（Qeq_bool bool 面）的合取判定;
   与 qpg_divisor_ok 的两肢逐一对应（qpg_degge1=Id bool 面、
   qpg_leadne0=Qcompare match 面的 bool 判定像） *)
Definition lng_den_ok_bool (n : nat) : bool :=
  andb (Nat.ltb 0 (qpd_deg (lnc_bk_den n)))
       (negb (Qeq_bool (qpd_lead (lnc_bk_den n)) 0)).

(* ============================================================ *)
(* §2 载体桥三件（双向等价 + 总真）                                 *)
(* ============================================================ *)

(* 总真: 良态判定对全 n 恒真（度账 lng_den_deg + 首项账 lng_lead_den_ne0） *)
Theorem lng_den_ok_bool_total : forall n : nat, lng_den_ok_bool n = true.
Proof.
  intro n. unfold lng_den_ok_bool. apply andb_true_intro. split.
  - rewrite lng_den_deg. reflexivity.
  - destruct (Qeq_bool (qpd_lead (lnc_bk_den n)) 0) eqn:Eb.
    + exfalso. apply (lng_lead_den_ne0 n).
      apply (proj1 (Qeq_bool_iff (qpd_lead (lnc_bk_den n)) 0)). exact Eb.
    + reflexivity.
Qed.

(* 声音性: bool 判定真 → 原 Set 证书（度肢 Id 面 + 首项肢 match 面） *)
Theorem lng_den_ok_bool_true_ok : forall n : nat,
  lng_den_ok_bool n = true -> qpg_divisor_ok (lnc_bk_den n).
Proof.
  intros n Hb. unfold lng_den_ok_bool in Hb. apply andb_prop in Hb.
  destruct Hb as [Hd Hl]. unfold qpg_divisor_ok. split.
  - unfold qpg_degge1. rewrite Hd. exact id_refl.
  - unfold qpg_leadne0. destruct (Qcompare (qpd_lead (lnc_bk_den n)) 0) eqn:Ec.
    + exfalso.
      assert (Hz : qpd_lead (lnc_bk_den n) == 0)
        by (apply (proj2 (Qeq_alt (qpd_lead (lnc_bk_den n)) 0)); exact Ec).
      assert (Hb2 : Qeq_bool (qpd_lead (lnc_bk_den n)) 0 = true)
        by (apply (proj2 (Qeq_bool_iff _ _)); exact Hz).
      rewrite Hb2 in Hl. discriminate Hl.
    + exact tt.
    + exact tt.
Qed.

(* 完备性: 原 Set 证书 → bool 判定真（使用上游 _inv 两件） *)
Theorem lng_den_ok_ok_bool : forall n : nat,
  qpg_divisor_ok (lnc_bk_den n) -> lng_den_ok_bool n = true.
Proof.
  intros n Hok. unfold qpg_divisor_ok in Hok. destruct Hok as [Hd Hl].
  unfold lng_den_ok_bool. apply andb_true_intro. split.
  - exact (qpg_degge1_inv (lnc_bk_den n) Hd).
  - destruct (Qeq_bool (qpd_lead (lnc_bk_den n)) 0) eqn:Eb.
    + exfalso. apply (qpg_leadne0_inv (lnc_bk_den n) Hl).
      apply (proj1 (Qeq_bool_iff _ _)). exact Eb.
    + reflexivity.
Qed.

(* 双向等价（载体保真）: 由上两件方向定理对交付——bool→证书
   （lng_den_ok_bool_true_ok）与证书→bool（lng_den_ok_ok_bool）。
   不立单条 iff: qpg_divisor_ok 为 Set 面而 Prop 级 iff 容不下 Set 侧
   （宇宙墙，Cannot enforce Set <= Prop; CI 判例同族）——两方向定理
   对即等价的全部内容，PA 面不减凭证为两件各自 Closed。 *)

(* ============================================================ *)
(* §3 引擎使用面（bool 载体直驱 qpg 引擎; PA 面，不提取）            *)
(* ============================================================ *)

Definition lng_div_gen_bool (n : nat)
  : sigT (qpd_divmod_gen_pred (lnc_bk_num n) (lnc_bk_den n)) :=
  qpg_divmod_gen (lnc_bk_num n) (lnc_bk_den n)
    (lng_den_ok_bool_true_ok n (lng_den_ok_bool_total n)).

(* 一致性: qpg_divmod_gen 之 projT1（商余对）不依赖证书项——
   bool 载体驱车与原证书驱车得同一商余对（定义性） *)
Lemma lng_div_gen_bool_agree : forall n : nat,
  projT1 (lng_div_gen_bool n) = projT1 (lng_div_gen n).
Proof. intro n. reflexivity. Qed.

(* n=4 值级衔接: 与 CV 件 lng_w4 逐点同一 *)
Lemma lng_pin_bool_w4 : projT1 (lng_div_gen_bool 4) = lng_w4.
Proof. exact (lng_div_gen_bool_agree 4). Qed.

(* ============================================================ *)
(* §4 提取面（Obj.magic=0 交付面）+ PA 取证                         *)
(* ============================================================ *)

(* 载体判定器纯 bool 函数化——判定三路（①②闭式）均必剩 magic 而本面归零;
   对账: CV 件 abl_ln2_qpoly_gen.ml L21 Obj.magic=1 → 本件提取 0 *)
Separate Extraction lng_zneg2 lng_den_ok_bool.

Print Assumptions lng_den_ok_bool.
Print Assumptions lng_den_ok_bool_total.
Print Assumptions lng_den_ok_bool_true_ok.
Print Assumptions lng_den_ok_ok_bool.
Print Assumptions lng_div_gen_bool.
Print Assumptions lng_div_gen_bool_agree.
Print Assumptions lng_pin_bool_w4.
