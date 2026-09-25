(* ===================================================================== *)
(* 形态：批C 宣言件——本文件纯注记 + 引用性定理（全 exact/实例化转发，     *)
(*   零新数学内容）；dpc_ 前缀全库防撞。宿主 UpReqPadeSign.v 零改动。      *)
(* ===================================================================== *)
(*   引「120-121」、CWD5 卡引「120-133」系旧版行号漂移，注记块内容同一）：  *)
(*   「显式假设登记（通用 n 版 den_pos，禁硬凑）：通用 n 的 den_pos 接线图  *)
(*   （下一批，30 分钟预算内诚实显式假设）：den(x) := altsum (fun k =>     *)
(*   pade_coeff n k * q_pow x k) (n+1)（PC2 引擎出口，UpReqAltSumPos.v）；  *)
(*   逐项非负（pade_coeff_pos）+ 相邻递减 QleT (c_{k+1} x^{k+1}) (c_k x^k) *)
(*   （0<=x 段）喂 altsum_nonneg（QleT 假设面）/ altsum_nonneg_leT（QleT'  *)
(*   面）得 QleT' 0 (den x)；首对严格 + 项数 >= 2 时经 altsum_pos_strict   *)
(*   升 QltT 0（本件 n=1 即其手工实例）；le_head 备 <= c_0 用。依赖缺口：  *)
(*   相邻递减需 c_k x^k 单调面（x^k/x^{k+1} 比式 + 系数比                 *)
(*   (k+1)(2n-k)/(2(k+1)(n-k)) 型），库内尚无现成件，下一批建。           *)
(*   本件三引理即 n=0/n=1 手工实例，可作通用件回来核对的哨兵。」           *)
(*                                                                       *)
(* 【四来源覆盖判定】（语句面 × 结论域 × 严格度 三元组逐位）               *)
(*                                                                       *)
(*  来源① 正册 PadeDenPosB12.v（pdpb_）——非负档全域：                    *)
(*    · pdpb_den_pos_le2@141：一般 n，QleT' 0 x -> QleT' x 2 ->           *)
(*      QleT' 0 (pade_den n x)——[0,2] 全段非负，挂账「0<=x 段非负档」    *)
(*      的严格超集（含端点 x=2）；                                        *)
(*    · pdpb_den_pos_le2_T@161：QleT/QleT Or 形前提适配（挂账             *)
(*      altsum_nonneg 假设面同构）；                                      *)
(*    · pdpb_den_pos_b12@172：QltT 1 x -> QleT x 2 -> QleT' 0——(1,2]     *)
(*    · pdpb_R_ge_2@50：0≤k<n ⟹ 2≤pdp_R n k——挂账「依赖缺口比式」高段。 *)
(*                                                                       *)
(*  来源② 库内 UpReqPadeDenPos12.v（pdq_）——(1,2) 段：                   *)
(*    · pdq_den_pos_12@157：一般 n，QltT 1 x -> QltT x 2 -> QleT' 0；    *)
(*    · pdq_R_ge_2@69：比式件（(1,2) 段路线）；                          *)
(*    · pdq_den_pos_12_strict@249：QltT 1 x -> QltT x 2 -> QltT 0——      *)
(*      严格档但域限 x∈(1,2)（低段 [0,1] 不在其域）。                    *)
(*                                                                       *)
(*  来源③ 库内 UpReqPadeDenPos.v（pdp_）——低段非负 + 挂账全部依赖件：    *)
(*    · pdp_den_pos@493：一般 n，QleT 0 x -> QleT x 1 -> QleT' 0——       *)
(*      挂账主句 0≤x≤1 非负档精确同域；                                  *)
(*    · 接线图三件全在库：pdp_den_altsum@467（den(x)==altsum 形）、      *)
(*      pdp_coeff_ratio@386（c_k==c_{S k}·pdp_R n k 比式恒等式）、       *)
(*      pdp_term_decay@422（相邻递减 0≤x≤1）；逐项非负                   *)
(*      pade_coeff_pos@UpReqPadeExp.v:109；引擎出口 altsum_nonneg@475 /  *)
(*      altsum_nonneg_leT@UpReqAltSumPos.v:464 / altsum_pos_strict@599 / *)
(*      altsum_le_head@547（挂账「le_head 备 <= c_0 用」备件）。          *)
(*    ⟹ 挂账「库内尚无现成件，下一批建」的依赖缺口已全部建成，注记陈旧。  *)
(*                                                                       *)
(*    · pdpa_den_pos_strict@318：一般 n 全体（含 n=0 特例                *)
(*      pdpa_den0_one@305 直收），QleT 0 x -> QltT x 2 -> QltT 0         *)
(*      (pade_den n x)——[0,2) 半开段严格档，正是挂账「首对严格 +         *)
(*      altsum_pos_strict 升 QltT」路线的通用 n 闭合（首对件             *)
(*      pdpa_g1_lt_g0@240 前提仅 x<2，比 12:195 pdq_g1_lt_g0 的          *)
(*      QltT 1 x 更强）；依赖比式 pdpa_R_ge_2@153 / pdpa_term_decay@201。*)
(*      由其独立闭合。                                                   *)
(*                                                                       *)
(*    双保险：dpg_den_pos_strict@67（n≥1，QleT' 0 x -> QltT x 2 ->       *)
(*    QltT 0）/ dpg_den_pos_strict_T@91（QleT Or 形前提）/               *)
(*    dpg_den_pos_strict_le1@104（0≤x≤1 档）；与来源④同档互证。          *)
(*                                                                       *)
(*    · 非负档（QleT' 0，一般 n）：0≤x≤1 ← 来源③:493；(1,2]/(1,2) ←     *)
(*      来源②:157/来源①:172；[0,2] 全段 ← 来源①:141（超集）。           *)
(*    · 严格档（QltT 0，一般 n）：[0,2) ← 来源④:318（n=0 含）；(1,2) ←  *)
(*      来源②:249；n≥1 [0,2) ← 补充源⑤:67/91。                          *)
(*    · 接线图五备件（den 形/逐项非负/比式/le_head/引擎出口）：来源③+    *)
(*      UpReqAltSumPos 全在库。                                          *)
(*    · 挂账哨兵条款兑现：本件 n=1 手工实例 pds_den1_pos@106 的语句面     *)
(*      由引用性哨兵件 dpc_pds_den1_pos_sentinel（下）自通用件直接实例    *)
(*      覆盖，哨兵核对通过。                                             *)
(*    · 注：x=2 端点严格档不可证系数学必然（n=1 分母 1−x/2 在 x=2 为零，  *)
(*      R_{n,0}=2 在 k=0 取等首对非严格），两档语句面在端点分岔非缺口。   *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqPadeExp UpReqAltSumPos UpReqPadeDenPos.
Require Import PadeDenPosA DenPosGeneral.
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

(* 引用性主件：严格档统一闭合形——语句面与 pdpa_den_pos_strict 逐字同构，  *)
(* 全参 exact 转发，零新证（来源④坐标的定理面落章）。                    *)
Theorem dpc_den_pos_close : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof. exact pdpa_den_pos_strict. Qed.

(* 引用性互证件：同一语句面经补充源⑤（dpg_，n=0 走 pdpa_den0_one）      *)
(* 独立可达——严格档库内双路线实证。                                      *)
Theorem dpc_den_pos_close_alt : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x (2#1) -> QltT 0 (pade_den n x).
Proof.
  intros n x Hx H2.
  destruct n as [| m].
  - apply (qeq_ltT 1%Q (pade_den 0%nat x)).
    + apply Qeq_sym. apply pdpa_den0_one.
    + apply qltT_0_1.
  - apply (dpg_den_pos_strict_T (Datatypes.S m) x).
    + lia.
    + exact Hx.
    + exact H2.
Qed.

(* 挂账哨兵核对件：宿主 n=1 手工实例 pds_den1_pos@UpReqPadeSign.v:106    *)
(* 语句面（QltT 0 x -> QltT x 2 -> QltT 0 (pade_den 1 x)）由通用严格档    *)
(* 直接实例——通用件回场核对哨兵，条款兑现。                              *)
Theorem dpc_pds_den1_pos_sentinel : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1%nat x).
Proof.
  intros x H0 H2.
  apply (dpc_den_pos_close 1%nat x).
  - left. exact H0.
  - exact H2.
Qed.

(* ===== G1 证据：引用链全库内 Closed 件 ===== *)
Print Assumptions dpc_den_pos_close.
Print Assumptions dpc_den_pos_close_alt.
Print Assumptions dpc_pds_den1_pos_sentinel.
