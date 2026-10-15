(* ===================================================================== *)
(*  gcl_hent2.v —— DM-HENT2【Hanson 熵 nat 化 R2 件】：焊装链覆盖域窗扩展     *)
(*  模块名：gcl_hent2。                                                     *)
(*  使命：承 DM-HENT 冻结遗产（gcl_hent.v 窗件 m∈[3,8]·零重做），把 weld3      *)
(*        熵前提的有界窗消去向右扩展三档：m∈[3,11]（n=S m∈[4,12]）——          *)
(*          · gcl_lcm_step_le：Hanson 阶梯递推 L(S n) ≤ L(n)·(S n)           *)
(*            （hl_lcm_upto 单步折叠展开＋hl_lcm_le_mul，变量层安全）；        *)
(*          · gcl_hanson_win_10：h3 偶桥 k=5（承 gcl_h3_even_le，            *)
(*            L(10) ≤ C(10,5)·5!=30240 ≤ 3·3^9）；                           *)
(*          · gcl_hanson_win_11/12：阶梯链（L(11)≤L(10)·11≤2520·11≤9·3^9；   *)
(*            L(12)≤L(11)·12≤2520·11·12=332640≤27·3^9）；                    *)
(*          · gcl_hanson_win2 / _t：窗件 Prop 面与 hl_le_t Set 面承载；       *)
(*          · 主语句 gcl_supply_sym_weld3_win2：weld3 逐字使用——熵前提          *)
(*            窗内消去（前提三→二：窗界 3≤m≤11＋④族界），覆盖域 8→11。        *)
(*  数学负载（对照 _mirror_hent2_out.txt 34/34 全 PASS 在卷）：               *)
(*    · 新窗三点：L(10)=2520≤59049、L(11)=27720≤177147、L(12)=27720≤531441；  *)
(*    · 幂裂因：3^10=3·3^9、3^11=9·3^9、3^12=27·3^9（比较肢全在 3^9 锚内）；   *)
(*    · 使用检查点右缘 (m,M)=(11,11)：d=L(12)=27720、Isum^sym 闭式复算、        *)
(*      五肢逐肢成立（d²I≈1.633e-7<1）；(3,3) 冻结锚 6634961/3127445521200    *)
(*      回扣一致。                                                          *)
(*  诚实边界（真墙档维持·禁虚报）：                                          *)
(*    - 全称形 Hanson 熵（∀n, lcm(1..n) ≤ 3^n）仍为真墙档三档归档（三源判定    *)
(*      互证·DM-HENT 移交账§二·四复审条件 (a)-(d) 随墙维持）——本件只在窗内      *)
(*      扩覆盖域，不触碰真墙。                                              *)
(*    - 窗右界 n=12＝本世界一元内核的可达端：L(13)=360360 越过注册一元        *)
(*      安全界（Z3JR 判例 55440 层）→ n≥13 直算不_attempt；h3 两路在 n≥11     *)
(*      亦断（halfbinom(11)=665280>177147、C(12,6)·6!=665280>531441、        *)
(*      halfbinom(13)=17297280>3^13）——对照 h3_breaks_11/h3even_breaks_12/   *)
(*      boundary_h3_13_dead 在卷。右界再扩需二进制 nat lcm 机＋迁移件         *)
(*      （复审条件 (d)·移交面维持）。                                        *)
(*    - CZR14 打点纪律（E-STAGING-CZR14 卡）规避设计：L(11)=27720、           *)
(*      L(12)=27720 数值等式【不做 Qed 打点】（lcm divmod 链 kernel conv      *)
(*      分钟级墙钟坑）——n≥11 的证明显式不计算 lcm，只走阶梯链；唯一            *)
(*      吸收锚 L(10)=2520 的 vm_compute 成本已清册化（gcd(2520,10) 减量       *)
(*      轮数 252·O(2520)≈635k 步，为冻结 n=9 域 ~8 倍、CZR14 分钟坑域 1/100）。 *)
(*    - ④族界（Isum^sym ≤ weight）维持在句前提（④肢 D_0 界归其位·零越权）。   *)
(*  构造性（红线四要素·逐件）：                                              *)
(*    - 纯构造性：全件 Qed，零 Axiom／零 Parameter／零 Admitted／零承认式收尾／零经典；          *)
(*    - Set 层：主语句 gcl_supply_sym_weld3_win2 值域 gcl_supply_sym（sigT·Set） *)
(*      与 gcl_hanson_win2_t（hl_le_t·Set）皆 Set 承载；gcl_hanson_win2 及    *)
(*      各窗锚为 nat 层 Prop 面推理脚手架（HansonLcm/gcl_hent 先例）；        *)
(*    - 非平凡：阶梯递推引理（单步折叠展开）＋h3 偶桥使用（三前提整除→上界）    *)
(*      ＋逐点裂因比较链＋主语句 12 分支情形分析，非占位；win_10/11/12 比较      *)
(*      肢以 lia 收尾系字面线性整理步（例外册 lia 存量冻结在册），主语句与       *)
(*      窗件结构为 exact 结构化组合非 solver 收尾；                          *)
(*    - 可提取：Separate Extraction 双 Set 实体；文末 Print Assumptions。     *)
(*  签名稳定（律六）：冻结 gcl_hent.v 零字节触碰；全部新名（win_10/11/12、    *)
(*        win2、win2_t、weld3_win2、pow3_add、lcm_step_le）零旧名占用——       *)
(*        覆盖域扩大以新主语句 supersede 记录，旧窗件 [3,8] 继续有效并行。       *)
(*  依赖：Stdlib Arith/Lia；HansonLcm（9432265d）；Hanson3Pow（670438c2）；    *)
(*        S02_CauchyComplete；GCL 冻结四件（coefficient/famsym/isumsym/cert）；*)
(*        冻结窗件 gcl_hent（使用 gcl_h3_even_le 与 gcl_hanson_win_4..9 六点    *)
(*        ——win2 装配零重做，冻结源与 .vo 零字节触碰）                         *)
(*        ——与本世界 _world_manifest.txt 逐位同。DNF2 并播判停维持（本件件     *)
(*        零使用 DNF2）；abl_pr_lcm_pool p-adic 赋值机（plm_v 系）经 md5 检疫   *)
(*        与本世界 Hanson 两件同代（9432265d/670438c2 双一致）——列后选        *)
(*        路线候选，本件零移植。                                            *)
(*  编译配方：source Live/toolchain/env.sh && unset COQLIB ROCQLIB &&        *)
(*        ulimit -s 65532 && cd 本池 && cpu_guard v3 默认档包裹 rocq c        *)
(*        -native-compiler no -q -Q _world "" gcl_hent2.v（并发=1 单飞）。    *)
(* ===================================================================== *)

From Stdlib Require Import Arith.Arith Lia.
Require Import HansonLcm Hanson3Pow.
Require Import S02_CauchyComplete.
Require Import gcl_coefficient gcl_famsym gcl_isumsym gcl_cert.
Require Import gcl_hent.

(* ============================================================ *)
(* §A 阶梯递推（Hanson 递推 lcm(n+1) ≤ lcm(n)·(n+1)）与裂因脚手架               *)
(* ============================================================ *)

(* 幂加法裂因：3^(k+j) = 3^k·3^j（比较肢统一锚接到 3^9） *)
Lemma gcl_pow3_add : forall k j : nat, (3 ^ (k + j) = 3 ^ k * 3 ^ j)%nat.
Proof. intros k j. apply Nat.pow_add_r. Qed.

(* Hanson 阶梯递推：变量层安全（hl_lcm_upto 仅单步展开，n 为变量不触
   lcm divmod 链——CZR14 纪律的引理面承载） *)
Lemma gcl_lcm_step_le : forall n : nat,
  hl_lcm_upto (Datatypes.S n) <= hl_lcm_upto n * Datatypes.S n.
Proof.
  intro n. cbn [hl_lcm_upto]. apply hl_lcm_le_mul.
Qed.

(* ============================================================ *)
(* §B 新窗三点（n=10/11/12；n=4..9 六点逐字使用冻结 gcl_hanson_win_4..9           *)
(*    ——win2 装配面零重做，新铸仅三点）                                         *)
(* ============================================================ *)

(* n=10：h3 偶桥 k=5（L(10) ≤ C(10,5)·5!=30240 ≤ 27·3^7 = 3^10）。
   全部 vm_compute 字面（252/120/2187）在 55440 注册层内，且幂锚取 3^7=2187
   （< 5000 abstract-large-number 抽象阈——真字面，lia 可求值）；
   lcm 链零计算（整除→上界在 Hanson3Pow 冻结 vo 内已闭）。 *)
Lemma gcl_hanson_win_10 : (hl_lcm_upto 10 <= 3 ^ 10)%nat.
Proof.
  pose proof (gcl_h3_even_le 5) as H.
  assert (HE : (2 * 5 = 10)%nat) by reflexivity.
  rewrite HE in H.
  assert (HB : hl_binom 10 5 = 252) by (vm_compute; reflexivity).
  assert (HF : fact 5 = 120) by (vm_compute; reflexivity).
  rewrite HB, HF in H.
  assert (HB7 : (3 ^ 7 = 2187)%nat) by (vm_compute; reflexivity).
  assert (HP : (3 ^ 10 = 27 * 3 ^ 7)%nat).
  { pose proof (Nat.pow_add_r 3 3 7) as Hp.
    replace (3 + 7)%nat with 10 in Hp by lia.
    change (3 ^ 3)%nat with 27 in Hp. exact Hp. }
  rewrite HP, HB7. lia.
Qed.

(* n=11：阶梯链 L(11) ≤ L(10)·11 ≤ 2520·11 = 27720 ≤ 81·3^7 = 3^11。
   L(11) 本身零计算（CZR14 纪律）；唯一吸收锚 L(10)=2520 成本已清册化。 *)
Lemma gcl_hanson_win_11 : (hl_lcm_upto 11 <= 3 ^ 11)%nat.
Proof.
  pose proof (gcl_lcm_step_le 10) as H.
  assert (H10 : (hl_lcm_upto 10 = 2520)%nat) by (vm_compute; reflexivity).
  rewrite H10 in H.
  assert (HB7 : (3 ^ 7 = 2187)%nat) by (vm_compute; reflexivity).
  assert (HP : (3 ^ 11 = 81 * 3 ^ 7)%nat).
  { pose proof (Nat.pow_add_r 3 4 7) as Hp.
    replace (4 + 7)%nat with 11 in Hp by lia.
    change (3 ^ 4)%nat with 81 in Hp. exact Hp. }
  rewrite HP, HB7. lia.
Qed.

(* n=12：双阶梯链 L(12) ≤ L(11)·12, L(11) ≤ L(10)·11 ⟹ ≤ 332640 ≤ 243·3^7 = 3^12。
   L(11)/L(12) 零计算（CZR14 分钟坑域显式绕开）。 *)
Lemma gcl_hanson_win_12 : (hl_lcm_upto 12 <= 3 ^ 12)%nat.
Proof.
  pose proof (gcl_lcm_step_le 11) as H1.
  pose proof (gcl_lcm_step_le 10) as H2.
  assert (H10 : (hl_lcm_upto 10 = 2520)%nat) by (vm_compute; reflexivity).
  rewrite H10 in H2.
  assert (HB7 : (3 ^ 7 = 2187)%nat) by (vm_compute; reflexivity).
  assert (HP : (3 ^ 12 = 243 * 3 ^ 7)%nat).
  { pose proof (Nat.pow_add_r 3 5 7) as Hp.
    replace (5 + 7)%nat with 12 in Hp by lia.
    change (3 ^ 5)%nat with 243 in Hp. exact Hp. }
  rewrite HP, HB7. lia.
Qed.

(* ============================================================ *)
(* §C 主语句 I【窗熵件扩展】：Hanson 熵前提的窗内消去（m∈[3,11]）                  *)
(* ============================================================ *)

Theorem gcl_hanson_win2 : forall m : nat, (3 <= m)%nat -> (m <= 11)%nat ->
  (hl_lcm_upto (Datatypes.S m) <= 3 ^ (Datatypes.S m))%nat.
Proof.
  intros m H3 H11.
  destruct m as [|[|[|[|[|[|[|[|[|[|[|[|g]]]]]]]]]]]]; try lia.
  - exact gcl_hanson_win_4.
  - exact gcl_hanson_win_5.
  - exact gcl_hanson_win_6.
  - exact gcl_hanson_win_7.
  - exact gcl_hanson_win_8.
  - exact gcl_hanson_win_9.
  - exact gcl_hanson_win_10.
  - exact gcl_hanson_win_11.
  - exact gcl_hanson_win_12.
Qed.

(* Set 面承载（红线②·hl_le_t 同构件） *)
Theorem gcl_hanson_win2_t : forall m : nat, (3 <= m)%nat -> (m <= 11)%nat ->
  hl_le_t (hl_lcm_upto (Datatypes.S m)) (3 ^ (Datatypes.S m))%nat.
Proof.
  intros m H3 H11. apply hl_le_to_le_t.
  exact (gcl_hanson_win2 m H3 H11).
Qed.

(* ============================================================ *)
(* §D 主语句 II【weld3 窗内实例扩展】：熵前提逐字消去·覆盖域 8→11                  *)
(*    前提：窗界 3≤m≤11＋④族界 ⟹ 供给链 inhabited（sigT 见证 d:=gcl_dmod m）    *)
(* ============================================================ *)

Theorem gcl_supply_sym_weld3_win2 : forall (m M : nat),
  (3 <= m)%nat -> (m <= 11)%nat ->
  QleT' (gcl_Isum_sym m M) (gcl_weight_G m) ->
  gcl_supply_sym m M.
Proof.
  intros m M H3 H11 HI1.
  exact (gcl_supply_sym_weld3 m M H3 (gcl_hanson_win2 m H3 H11) HI1).
Qed.

(* ============================================================ *)
(* §E 审计面                                                                  *)
(* ============================================================ *)

Print Assumptions gcl_hanson_win2.
Print Assumptions gcl_hanson_win2_t.
Print Assumptions gcl_supply_sym_weld3_win2.

From Stdlib Require Import Extraction.
Set Extraction Output Directory "_log".
Separate Extraction gcl_hanson_win2_t gcl_supply_sym_weld3_win2.
