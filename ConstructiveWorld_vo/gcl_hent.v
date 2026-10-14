(* ===================================================================== *)
(*  gcl_hent.v —— weld3 熵前提的有界窗消去件                                *)
(*  模块名：gcl_hent。                                                     *)
(*  使命：承 gcl_supply_sym_weld3（前提三_item={m≥3·Hanson 熵·④族界}），      *)
(*        铸 Hanson 熵前提的有界窗消去：                                     *)
(*          · gcl_hanson_win：m∈[3,8]（n=S m∈[4,9]）的                       *)
(*            hl_lcm_upto n ≤ 3^n 机内成立——n=4/6/8 走 Hanson3Pow 的          *)
(*            h3_lcm_double_divide（L(2k) | C(2k,k)·k! 整除→上界链），        *)
(*            n=5/7 走 h3_lcm_le_halfbinom（半程二项式桥），n=9 直算字面；      *)
(*          · gcl_hanson_win_t：同语句的 hl_le_t Set 面承载（红线②）；         *)
(*          · 主定理 gcl_supply_sym_weld3_win：weld3 窗内实例化——熵前提      *)
(*            逐字消去（前提三→二：窗界 3≤m≤8＋④族界），供给链 inhabited。    *)
(*  数学核（独立复算 37/37 全 PASS 在卷）：                                  *)
(*    · 窗锚：L(4..9)=12,60,60,420,840,2520 ≤ 3^n=81..19683；                *)
(*    · h3 链五点：L(4)≤C(4,2)·2!=12、L(5)≤C(6,3)·3!=120、L(6)≤120、          *)
(*      L(7)≤C(8,4)·4!=1680、L(8)≤1680（全 ≤ 3^n）；n=9 为 h3 链断点          *)
(*      （C(10,5)·5!=30240>19683）如实登记、该点直算；                        *)
(*    · weld3_win 使用例 (m,M)=(3,3)：d=L(4)=12、Isum^sym 闭式复算核对        *)
(*      冻结锚 6634961/3127445521200、五肢逐肢成立（d²I≈3.06e-7<1）。         *)
(*  诚实边界：                                                              *)
(*    - 全称形 Hanson 熵（∀n, lcm(1..n) ≤ 3^n）本件不铸——三条独立线索        *)
(*      一致：HansonLcm 件①（无素数面即无可达指数级界）、Hanson3Pow 范围注记  *)
(*      （更锐 L(2n)|C(2n,n)·L(n) 需素数 p-adic 赋值面·另案）、熵段 nat 化    *)
(*      工程件（Z3J/Z3JR）。池内量化（独立复算③段）：Chebyshev 常数帽        *)
(*      ln4=1.3863>ln3=1.0986（abl_Pr_erdos_theta 常数级不足）；fact 界≫3^n  *)
(*      （n=8 已 6.1×）；熵常数 Σ(ln a_i)/a_i≈1.08239<ln3（slack 1.5%·       *)
(*      Sylvester 谱系 a=2,3,7,43,...·地基段绿在池·余三段（Legendre/赋值桥/   *)
(*      熵不等式 nat 化）未入栈——全称形归档，复审条件随件文书在卷。           *)
(*    - 窗端 n≤9 的上界为内核一元安全界（Z3JR 判例 55440 层），非数学边界     *)
(*      （L(10)=2520≤59049 亦真·独立复算 n10_still_true_note 在卷）。         *)
(*    - ④族界（Isum^sym ≤ weight）维持在句前提。                            *)
(*  构造性注记：全件 Qed/Defined，零 Axiom/Parameter、零承认、零 Abort、零    *)
(*        全局假设、零经典逻辑；主定理值域 gcl_supply_sym（sigT·Set）与       *)
(*        gcl_hanson_win_t（hl_le_t·Set）皆 Set 承载；gcl_hanson_win 及      *)
(*        各窗锚为 nat 层 Prop 面推理脚手架（HansonLcm/Hanson3Pow 先例）；    *)
(*        非平凡：h3 整除→上界桥（h3_divide_le 三前提）＋逐点字面判据＋      *)
(*        weld3 逐字使用焊接；Separate Extraction 双 Set 实体零失名；        *)
(*        文末 Print Assumptions。                                          *)
(*  依赖：Stdlib Arith/Lia；HansonLcm；Hanson3Pow；GCL 冻结四件              *)
(*        （gcl_coefficient/gcl_famsym/gcl_isumsym/gcl_cert）。              *)
(*  编译配方：rocq c -native-compiler no -q -Q . "" gcl_hent.v              *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia.
Require Import HansonLcm Hanson3Pow.
Require Import S02_CauchyComplete.
Require Import gcl_coefficient gcl_famsym gcl_isumsym gcl_cert.

(* ============================================================ *)
(* §A h3 整除→上界桥（偶数点·免 S(n/2) 步浪费）                                *)
(* ============================================================ *)

(* 偶点半程上界：L(2k) ≤ C(2k,k)·k!（由 h3_lcm_double_divide 整除＋双正性） *)
Lemma gcl_h3_even_le : forall k : nat,
  hl_lcm_upto (2 * k) <= hl_binom (2 * k) k * fact k.
Proof.
  intro k. apply h3_divide_le.
  - apply h3_lcm_double_divide.
  - apply h3_lcm_pos.
  - apply Nat.mul_pos_pos.
    + apply h3_binom_ge1. lia.
    + apply h3_fact_pos.
Qed.

(* ============================================================ *)
(* §B 窗锚六点（n=S m∈[4,9]）                                                  *)
(*    五点走 h3 链（独立复算 h3chain_* 全 PASS）＋n=9 直算（h3 断点如实登记）        *)
(* ============================================================ *)

Lemma gcl_hanson_win_4 : (hl_lcm_upto 4 <= 3 ^ 4)%nat.
Proof.
  pose proof (gcl_h3_even_le 2) as H.
  apply (Nat.le_trans _ _ _ H).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma gcl_hanson_win_5 : (hl_lcm_upto 5 <= 3 ^ 5)%nat.
Proof.
  pose proof (h3_lcm_le_halfbinom 5) as H.
  apply (Nat.le_trans _ _ _ H).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma gcl_hanson_win_6 : (hl_lcm_upto 6 <= 3 ^ 6)%nat.
Proof.
  pose proof (gcl_h3_even_le 3) as H.
  apply (Nat.le_trans _ _ _ H).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma gcl_hanson_win_7 : (hl_lcm_upto 7 <= 3 ^ 7)%nat.
Proof.
  pose proof (h3_lcm_le_halfbinom 7) as H.
  apply (Nat.le_trans _ _ _ H).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma gcl_hanson_win_8 : (hl_lcm_upto 8 <= 3 ^ 8)%nat.
Proof.
  pose proof (gcl_h3_even_le 4) as H.
  apply (Nat.le_trans _ _ _ H).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(* n=9：h3 链断点（半程界 30240>19683·独立复算 h3_breaks_at_9 在卷）——直算点。
   一元字面 2520/19683 全在 Z3JR 内核安全界（55440 层）内。 *)
Lemma gcl_hanson_win_9 : (hl_lcm_upto 9 <= 3 ^ 9)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

(* ============================================================ *)
(* §C 主定理 I【窗熵件】：Hanson 熵前提的窗内消去（m∈[3,8]）                       *)
(* ============================================================ *)

Theorem gcl_hanson_win : forall m : nat, (3 <= m)%nat -> (m <= 8)%nat ->
  (hl_lcm_upto (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat.
Proof.
  intros m H3 H8.
  destruct m as [|[|[|[|[|[|[|[|[|g]]]]]]]]]; try lia.
  - exact gcl_hanson_win_4.
  - exact gcl_hanson_win_5.
  - exact gcl_hanson_win_6.
  - exact gcl_hanson_win_7.
  - exact gcl_hanson_win_8.
  - exact gcl_hanson_win_9.
Qed.

(* Set 面承载（红线②·hl_le_t 同构件） *)
Theorem gcl_hanson_win_t : forall m : nat, (3 <= m)%nat -> (m <= 8)%nat ->
  hl_le_t (hl_lcm_upto (Datatypes.S m)) (3 ^ (Datatypes.S m))%nat.
Proof.
  intros m H3 H8. apply hl_le_to_le_t.
  exact (gcl_hanson_win m H3 H8).
Qed.

(* ============================================================ *)
(* §D 主定理 II【weld3 窗内实例】：熵前提逐字消去（前提三→二）                      *)
(*    前提：窗界 3≤m≤8＋④族界 ⟹ 供给链 inhabited（sigT 见证 d:=gcl_dmod m）    *)
(* ============================================================ *)

Theorem gcl_supply_sym_weld3_win : forall (m M : nat),
  (3 <= m)%nat -> (m <= 8)%nat ->
  QleT' (gcl_Isum_sym m M) (gcl_weight_G m) ->
  gcl_supply_sym m M.
Proof.
  intros m M H3 H8 HI1.
  exact (gcl_supply_sym_weld3 m M H3 (gcl_hanson_win m H3 H8) HI1).
Qed.

(* ============================================================ *)
(* §E 审计面                                                                  *)
(* ============================================================ *)

Print Assumptions gcl_hanson_win.
Print Assumptions gcl_hanson_win_t.
Print Assumptions gcl_supply_sym_weld3_win.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log".
Separate Extraction gcl_hanson_win_t gcl_supply_sym_weld3_win.
