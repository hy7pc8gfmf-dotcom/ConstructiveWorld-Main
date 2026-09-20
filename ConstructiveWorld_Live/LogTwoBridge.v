(* ============================================================ *)
(* LogTwoBridge.v —— 席位 CZB12（批次 E-STAGING-CZB12）             *)
(* T61b 尾工 C2：UpReqConstEnvelope.v:22「对接 real_log 2 需 log_seq  *)
(* 桥，独立工程，挂账」之 dyadic 装载件（轻–中档）。                   *)
(*                                                               *)
(* 挂账原文（UpReqConstEnvelope.v:20-22 逐字）：                       *)
(*   「③ ln2：G05_LogSmall.v:976 logd_log_two_pos_real——正性假设面，    *)
(*   本席 ln2 子件自建交错调和柯西实数与之独立并存（对接                *)
(*   real_log 2 需 log_seq 桥，独立工程，挂账）。」                    *)
(*                                                               *)
(* 装载路线（消费 UpReqDyadicLog #291 的 ln 包络层，零新解析机器）：     *)
(*   二进制有理点 1/2 = 2^(−1)：dyd_axis_neg 0 := 1·(−ln2) 即 ln(1/2)  *)
(*   面；其上/下有理包络（dyd_ln_env_neg 0 n，宽 2·t2 n = 1/(n+1)）    *)
(*   取反翻转（dyd_le_b_opp_flip + dyd_opp_const_eq 归一）即装载        *)
(*   log 2 = −log(1/2) 的闭式双边夹逼。                                *)
(*                                                               *)
(* 交付四件：                                                          *)
(*   ltb_log_two_eq_ln2        —— log 2 载体 ≡ 既有 inline 常数面       *)
(*   （UpReqConstEnvelope c3e_ln2_real）相容性（real_eq 点态 ring）；    *)
(*   ltb_log_two_env           —— log 2 闭式双边包络（宽 QeqT 2·t2 n，   *)
(*   real 层 sigT/And := A*B 面）；                                    *)
(*   ltb_log_two_rate          —— 包络宽构造性收敛速率（c3e_env_rate_ln2 *)
(*   逐字实例，Q 层）；                                                 *)
(*   ltb_log_two_machine_bounds —— 机面 real_log 2 闭式夹逼 [1/2,1]     *)
(*   （evd_log_ge_inv_one_B 下 × real_log_le_linear_B 上；端点经        *)
(*   dyd_const_inv_proj / 点态 ring 归一为闭式有理数）。                *)
(*                                                               *)
(* 诚实账（不虚报）：机面 real_log 2 与常数面 ltb_log_two 的 real_eq    *)
(*   全合龙仍缺 exp(交错调和极限)==2 的分析恒等式（log_seq 桥收口      *)
(*   主体），本件装载至「双面各自闭式夹逼 + 常数面相容性」，桥体剩余    *)
(*   部分如实挂账留续。机面正性位 = G05 logd_log_two_pos_real（引文，   *)
(*   其点为 real_plus real_one real_one 面）。                          *)
(*                                                               *)
(* 红线：纯构造性（全 exact/实例化/点态 ring，零归纳零经典公理）；       *)
(*   语句面全 Set 层（real_le_b / sigT / And := A*B / QeqT / Qlt）；     *)
(*   零 承认件 零 公理；前缀 ltb_ 全库防撞已核（grep 零命中）；       *)
(*   既有文件零改；自建 .vo 只留 /tmp 不入共享树。                       *)
(*                                                               *)
(* CZJ14 战术-环境漂移适配登记（T98，20260919）：ltb_log_two_eq_ln2      *)
(*   原 §2 代换链 repeat rewrite real_opp_proj / real_mult_proj /        *)
(*   real_const_proj 在现行投影引理面（S02:1310/1316/1322，实形与稿面    *)
(*   预期同形逐字）下失一步——real_mult_proj 先行展开后新暴露的内层       *)
(*   projT1 (real_opp dyd_ln2) n 位，而 real_opp_proj 的 repeat 已过，   *)
(*   ring 残原子（T89 §3.4 定格行 62）。适配＝显式代换链补一段二次       *)
(*   投影：mult/const 展开后再 repeat rewrite real_opp_proj 一次（仅     *)
(*   重写新暴露位），Hz1 与 ring 收尾零改动。§3 宽腿同型适配：现行        *)
(*   dyd_ln_env_neg 宽面实形为 2·(1·t2 n)（Z.of_nat (Nat.succ 0) # 1     *)
(*   因子在位，源 UpReqDyadicLog.v:243 逐字），而定理面直为 2·t2 n——     *)
(*   原 setoid_replace（旧基座反向查找形）报 Nothing to rewrite，改      *)
(*   rewrite Hw + Hz1 代换 + ring 归一（Qeq_trans 桥等价，explicit       *)
(*   链）。§5 Hnorm_lo 同型适配：dyd_const_inv_proj 展开后新暴露的        *)
(*   projT1 (real_const (1#2)) n 位原链无 real_const_proj 段，补          *)
(*   repeat rewrite real_const_proj. 一段（Hz1/Hhalf/ring 收尾零改动）。  *)
(*   §5 主件收口 split 对 sigT 双层存在型无法猜见证（原稿未验证位，      *)
(*   T89 墙前置行 62 故未达）——改显式见证 exists (1#2)%Q; exists          *)
(*   (1#1)%Q; split（见证 = 语句面 QeqT 宽项端点逐字同源）， bullets      *)
(*   零改动。ltb_ 四定理语句面逐字零改动，零改弱。                        *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB UpReqEnvelopeDual UpReqConstEnvelope UpReqDyadicLog.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.PeanoNat Lia.

(* ============================================================ *)
(* §1 log 2 载体：−log(1/2) = −(1·(−ln2))，二进制有理点 1/2 轴的取反    *)
(* ============================================================ *)
Definition ltb_log_two : Real := real_opp (dyd_axis_neg 0).

(* ============================================================ *)
(* §2 相容性：与既有 inline 常数面（c3e_ln2_real，交错调和柯西实数）      *)
(*    逐点同一（real_eq），即 dyd_ln2 的取反翻转让两面相容。              *)
(* ============================================================ *)
Theorem ltb_log_two_eq_ln2 : real_eq ltb_log_two dyd_ln2.
Proof.
  apply real_eq_of_zero_diff. intro n.
  unfold ltb_log_two, dyd_axis_neg.
  repeat rewrite real_opp_proj.
  repeat rewrite real_mult_proj.
  repeat rewrite real_const_proj.
  repeat rewrite real_opp_proj.
  assert (Hz1 : (Z.of_nat (Nat.succ 0) # 1) == (1#1)%Q) by reflexivity.
  rewrite Hz1.
  ring.
Qed.

(* ============================================================ *)
(* §3 log 2 闭式双边包络（ln(1/2) 上/下包络取反翻转装载；宽 2·t2 n）      *)
(* ============================================================ *)
Theorem ltb_log_two_env : forall n : nat,
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo) ltb_log_two)
        (And (real_le_b ltb_log_two (real_const hi))
             (QeqT (hi - lo) (2 * t2 n))))).
Proof.
  intro n.
  destruct (dyd_ln_env_neg 0 n) as [lo0 [hi0 [Hlo [Hhi Hw]]]].
  exists ((- hi0)%Q). exists ((- lo0)%Q).
  unfold ltb_log_two.
  split.
  - (* 下端 −hi0：Hhi 取反翻转 + const 负号归一 *)
    apply (dyd_le_b_eq_l _ _ _
             (dyd_le_b_opp_flip _ _ Hhi)
             (real_eq_sym _ _ (dyd_opp_const_eq hi0))).
  - split.
    + (* 上端 −lo0：Hlo 取反翻转 + const 负号归一 *)
      apply (dyd_le_b_eq_r _ _ _
               (dyd_le_b_opp_flip _ _ Hlo)
               (dyd_opp_const_eq lo0)).
    + (* 宽：(−lo0)−(−hi0) == hi0−lo0 == 2·(1·t2 n) == 2·t2 n *)
      apply qeq_imp_qeqT. apply qeqT_imp_qeq in Hw.
      setoid_replace ((- lo0) - (- hi0))%Q with (hi0 - lo0)%Q by ring.
      rewrite Hw.
      assert (Hz1 : (Z.of_nat (Nat.succ 0) # 1) == (1#1)%Q) by reflexivity.
      rewrite Hz1. ring.
Qed.

(* ============================================================ *)
(* §4 Q 层速率：包络宽 2·t2 n = 1/(n+1) 构造性收敛（c3e_env_rate_ln2      *)
(*    逐字实例；t2 为定义性同项）。                                       *)
(* ============================================================ *)
Theorem ltb_log_two_rate : forall eps : Q, Qlt 0 eps ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    Qlt (2 * t2 n) eps).
Proof. intros eps Heps. exact (c3e_env_rate_ln2 eps Heps). Qed.

(* ============================================================ *)
(* §5 机面：real_log 2（dyd_const_pos 正性见证位）闭式夹逼 [1/2, 1]。      *)
(*    下件 = evd_log_ge_inv_one_B（1 − 1/m 形，端点经 real_inv_pos        *)
(*    常数投影归一）；上件 = real_log_le_linear_B（m − 1 形）。            *)
(* ============================================================ *)
Lemma ltb_two_Qpos : Qlt 0 (2#1)%Q.
Proof. unfold Qlt, Qlt_bool. reflexivity. Qed.

Theorem ltb_log_two_machine_bounds :
  sigT (fun lo : Q => sigT (fun hi : Q =>
    And (real_le_b (real_const lo)
                    (real_log (real_const (2#1)%Q)
                              (dyd_const_pos (2#1)%Q ltb_two_Qpos)))
        (And (real_le_b (real_log (real_const (2#1)%Q)
                                   (dyd_const_pos (2#1)%Q ltb_two_Qpos))
                        (real_const hi))
             (QeqT (hi - lo) ((1#1)%Q - (1#2)%Q))))).
Proof.
  assert (Hnorm_lo :
    real_eq (real_plus real_one
               (real_opp (real_inv_pos (real_const (2#1)%Q)
                          (dyd_const_pos (2#1)%Q ltb_two_Qpos))))
            (real_const (1#2)%Q)).
  { apply real_eq_of_zero_diff. intro n.
    repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj.
    rewrite dyd_one_proj.
    rewrite (dyd_const_inv_proj (2#1)%Q ltb_two_Qpos n).
    repeat rewrite real_const_proj.
    assert (Hhalf : (1 / (2#1)%Q) == (1#2)%Q) by reflexivity.
    rewrite Hhalf. ring. }
  assert (Hnorm_hi :
    real_eq (real_plus (real_const (2#1)%Q) (real_opp real_one))
            (real_const (1#1)%Q)).
  { apply real_eq_of_zero_diff. intro n.
    repeat rewrite real_plus_proj.
    repeat rewrite real_opp_proj.
    repeat rewrite real_const_proj.
    rewrite dyd_one_proj. ring. }
  exists ((1#2)%Q). exists ((1#1)%Q). split.
  - (* 下：1 − 1/2 = 1/2 *)
    apply (dyd_le_b_eq_l _ _ _
             (evd_log_ge_inv_one_B (real_const (2#1)%Q)
                (dyd_const_pos (2#1)%Q ltb_two_Qpos))
             Hnorm_lo).
  - split.
    + (* 上：2 − 1 = 1 *)
      apply (dyd_le_b_eq_r _ _ _
               (real_log_le_linear_B (real_const (2#1)%Q)
                  (dyd_const_pos (2#1)%Q ltb_two_Qpos))
               Hnorm_hi).
    + (* 宽：1 − 1/2 自证 *)
      apply qeq_imp_qeqT. apply Qeq_refl.
Qed.

(* ============================================================ *)
(* §6 公理面留痕（Print Assumptions 全主件核验 Closed）                    *)
(* ============================================================ *)
Print Assumptions ltb_log_two_eq_ln2.
Print Assumptions ltb_log_two_env.
Print Assumptions ltb_log_two_rate.
Print Assumptions ltb_log_two_machine_bounds.
Print Assumptions ltb_two_Qpos.
