(* ============================================================ *)
(* UpAblT9_UpReqFEPAttn.v —— T9 批 Context 实例束·UpReqFEPAttn 辖区         *)
(*   （log 三面=T2a 已毕，本件只收三节 Context 束三位，零重叠）             *)
(* 被消融位（普查表 §2 UpReqFEPAttn 行）：                                 *)
(*   位1 UpReqFEPAttn.v:71   Context（Section ReqFEPAttn）                 *)
(*   位2 UpReqFEPAttn.v:259  Context（Section ReqRowView）                 *)
(*   位3 UpReqFEPAttn.v:331  Context（Section ReqFEPLogZ）                 *)
(* 代表定理（各节正性件，出节签名逐字实测自 _tt9a_sig 检验）：              *)
(*   位1 ←Zf_pos@:121（sum_pos 接口位出节显式前提参）                      *)
(*   位2 ←req_Zrow_pos@:280（sum_pos+expf_pos 双前提参）                   *)
(*   位3 ←lz_Zf_pos@:366（sum_pos 前提参）                                 *)
(* 分级：三位全 N1（库内件直连；接口位前提为显式供给参=T1b D1 同形，        *)
(*   Context 位材料化独立于其供给面，不降档不隐藏）。                       *)
(* 依赖（只读使用，原树零改）：CW_ConstructiveWorld_219、UpReqFEPAttn。     *)
(* ============================================================ *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqFEPAttn.
Import RealInterfaceEnhancedMod.

(* 位1 ←:71（rep@:121；R/RIS 实例位材料化） *)
Theorem uabT9_fep_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : lt zero T),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    lt zero (Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@Zf_pos Real RealEnhancedReal S sumf Hsum z T T_pos).
Qed.

(* 位2 ←:259（rep@:280；R/RIS 实例位材料化） *)
Theorem uabT9_row_ctx_Zrow_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real)
         (temp : Real) (temp_pos : lt zero temp)
         (z2 : S -> S -> Real) (expf : Real -> Real),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    (forall x : Real, lt zero (expf x)) ->
    forall s : S, lt zero (req_Zrow S sumf temp temp_pos z2 expf s).
Proof.
  intros S sumf temp temp_pos z2 expf Hsum Hexpf s.
  exact (@req_Zrow_pos Real RealEnhancedReal S sumf Hsum temp temp_pos z2 expf Hexpf s).
Qed.

(* 位3 ←:331（rep@:366；R/RIS 实例位材料化） *)
Theorem uabT9_lz_ctx_Zf_pos :
  forall (S : Set) (sumf : (S -> Real) -> Real) (z : S -> Real) (T : Real)
         (T_pos : lt zero T),
    (forall f : S -> Real,
      (forall s : S, lt zero (f s)) -> lt zero (sumf f)) ->
    lt zero (lz_Zf S sumf z T T_pos).
Proof.
  intros S sumf z T T_pos Hsum.
  exact (@lz_Zf_pos Real RealEnhancedReal S sumf Hsum z T T_pos).
Qed.

(* ---- PA 收尾 ---- *)
Print Assumptions uabT9_fep_ctx_Zf_pos.
Print Assumptions uabT9_row_ctx_Zrow_pos.
Print Assumptions uabT9_lz_ctx_Zf_pos.
