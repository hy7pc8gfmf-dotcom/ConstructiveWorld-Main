(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   uabd1s2_dpo_log_inv_exp_neg_req（原 L45，结构性重演／显式见证直取）          *)
(*   uabd1s2_dpo_log_req_compat（原 L36，结构性重演／显式见证直取）               *)
(* ============================================================ *)

(* ============================================================ *)
(* UpAblD1S2_reqlog_UpReqDpoLoss.v —— FA-D1 批 D1-④ E403 log 桥批       *)
(*   req 载体层 log 相容／log_inv 复原双槽·引用性消融件                  *)
(*                                                              *)
(*   槽1 UpReqDpoLoss.v L64 rdl_log_req_compat（桥假设位自持；批 1       *)
(*       ReqLogBridge 接口缺口桥同位；req 载体层，三行语句逐字）         *)
(*   槽2 UpReqDpoLoss.v L67 rdl_log_inv_exp_neg_req（同位；req 载体层，  *)
(*       语句逐字）                                                      *)
(*                                                              *)
(*   G05_LogSmall 头注 B1/B4 证明族自述含 rdl_log_req_compat／           *)
(*   rdl_log_inv_exp_neg_req 本位（=本件两槽之命名源），喂法即本位。     *)
(*                                                              *)
(*   槽1：logd_log_compat_real@G05_LogSmall.v:302（零前提 Real 层槽形）。*)
(*   槽2：logd_log_inv_exp_neg_real@G05_LogSmall.v:342（B4 组装件）。    *)
(*                                                              *)
(* 载体分层（诚实降级，T2a 同款）：R 换实例位 Real、RIS 取典范实例       *)
(*   RealEnhancedReal（@S07:8559）——抽象 R 上不消解，典范实例上成立。    *)
(*                                                              *)
(* 依赖（全部只读使用，原树零改）：CW_ConstructiveWorld_219、            *)
(*   G05_LogSmall。                                                      *)
(* 纪律：语句面全集合层；零新增未证假设位；逐槽一条引用性消融定理；      *)
(*   文尾逐件假设面打印收尾。                                            *)
(*   四关留痕：Live_X/attn/logs/g{1..4}-UpAblD1S2_reqlog_UpReqDpoLoss.* *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ---- 槽1 ←UpReqDpoLoss.v L64 rdl_log_req_compat（逐字，R:=Real） ---- *)
Theorem uabd1s2_dpo_log_req_compat :
  forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
    req x y -> req (log x Hx) (log y Hy).
Proof.
  intros x y Hx Hy Hxy.
  apply (@RealInterfaceEnhancedMod.le_antisym Real RealInterfaceEnhancedMod.RealEnhancedReal (log x Hx) (log y Hy)).
  apply (real_log_le_mono x y Hx Hy).
  right; exact Hxy.
  apply (real_log_le_mono y x Hy Hx).
  right; exact (req_sym _ _ Hxy).
Qed.

(* ---- 槽2 ←UpReqDpoLoss.v L67 rdl_log_inv_exp_neg_req（逐字，R:=Real） ---- *)
Theorem uabd1s2_dpo_log_inv_exp_neg_req :
  forall x : Real, req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  intro x.
  exact (logd_log_inv_exp_neg_real x).
Qed.

(* ---- 收尾：文尾逐件假设面打印（G2 留痕） ---- *)
Print Assumptions uabd1s2_dpo_log_req_compat.
Print Assumptions uabd1s2_dpo_log_inv_exp_neg_req.
