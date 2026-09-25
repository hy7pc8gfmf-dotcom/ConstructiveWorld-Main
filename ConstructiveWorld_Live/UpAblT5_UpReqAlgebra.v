(* ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   abl_UpReqAlgebra_log_inv_exp_neg_req（原 L37，1 句玩具证）           *)
(*   abl_UpReqAlgebra_log_req_compat（原 L30，1 句玩具证）                *)
(* ============================================================ *)
(* ============================================================ *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，经 *)
(* 恒等守恒——清单所列 2 参数位证明体与 Main 现版原件逐字同文（刀体＝原体， *)
(* ============================================================ *)

(* ============================================================ *)
(* 母本：UpReqAlgebra.v（原树零改，只读依存）                                   *)
(*                                                              *)
(*   ① L1498 log_req_compat —— Setoid 接口具体实例供给（N3）            *)
(*      母本节 Section ReqLogBridge（L1495 起，Context {R}{RIS}）；实例供给        *)
(*      R:=Real、RIS:=RealEnhancedReal（S07:8566）。                           *)
(*      实例化消解件：logd_log_compat_real@G05_LogSmall.v:302（E403 B1 结论：            *)
(*      Real 层闭合喂位；其构体=mono 链形，底细 real_log_le_mono）               *)
(*      依存位：UpReqAlgebra:1538                                            *)
(*   ② L1502 log_inv_exp_neg_req —— 同上（N3）                        *)
(*      实例化消解件：logd_log_inv_exp_neg_real@G05_LogSmall.v:344（E403 B4 结论：        *)
(*      证明族 log_inv_exp_neg_req(5) 参数位名点名）                          *)
(*      依存位：UpReqAlgebra:1521                                            *)
(*                                                              *)
(* 纪律：纯构造性 / 语句面全 Set 层 / 公理面零新增 / 原树零改 /          *)
(*       独立伴生件不并入原模块 / 前缀 abl_ 本件内防撞。               *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import G05_LogSmall.
Import RealInterfaceEnhancedMod.

(* ################ ① log_req_compat（母本 L1498-1500 逐字参数形，实例供给） ########### *)
(* 母本节参 {R}{RIS} 出节后取具体实例 R:=Real、RIS:=RealEnhancedReal：                *)
(* 语句各名字（lt/req/log/zero）经 RealInterfaceEnhancedMod 隔离名空间解析，          *)
(* 与 G05:302 logd_log_compat_real 同一 elaboration。                             *)
Theorem abl_UpReqAlgebra_log_req_compat : forall (x y : Real) (Hx : lt zero x) (Hy : lt zero y),
  req x y -> req (log x Hx) (log y Hy).
Proof.
  exact logd_log_compat_real.
Qed.

(* ################ ② log_inv_exp_neg_req（母本 L1502-1503 逐字参数形，实例供给）####### *)
Theorem abl_UpReqAlgebra_log_inv_exp_neg_req : forall x : Real,
  req (log_inv (exp_neg x) (exp_neg_pos x)) x.
Proof.
  exact logd_log_inv_exp_neg_real.
Qed.

(* ---- PA 自检段（文尾逐件留痕） ---- *)
Print Assumptions abl_UpReqAlgebra_log_req_compat.
Print Assumptions abl_UpReqAlgebra_log_inv_exp_neg_req.
