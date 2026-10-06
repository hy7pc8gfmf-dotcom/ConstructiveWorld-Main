(* ==========================================================================
   uabd_supply_UpReqDist_group_size_pos.v
   模块名：uabd_supply_UpReqDist_group_size_pos
   数学使命：UpReqDist 的 ReqGRPO 节以 reqd_of_nat（nat 到抽象有序域 R 的
     构造性计数嵌入，0 映 zero、S n 映 1 + of_nat n）与
     reqd_group_size := length group_enum 承载组规模；其正性槽
     「lt zero (reqd_of_nat (length enum))」在枚举含元素之 InT 见证下恒成立。
     本件供给两件定理：
     ① uabd_reqd_nat_S_pos：S k 形嵌入严格正（对 k 归纳：基座经加零换形
        回 one 后用 one_pos；步进经 plus_positive 双正合成）；
     ② uabd_reqd_len_pos_cover：覆盖见证形——对 InT 推导归纳，两构造子
        皆 cons 形，长度即 S 形，归①。
   依赖：S01_BaseRing（InT）、S07_RealSetoidExpLog（RealInterfaceEnhancedSetoid
     类）、UpReqDist（reqd_of_nat 常数面）、Stdlib List。
   对标行：EpsOptimalReach reqd_of_nat_pos（Not(Id l nil) 否定前件形）与
     NatLenPos nlp_len_pos_cover（real_of_nat 域覆盖见证形）——本件为
     req 域常数面之 InT 见证形独立槽形，与上述在库件语义地位独立并存。
   构造性注记：全件 Qed 真构造；语句面全 Set 形（lt/le/req 为接口 Set 值
     谓词，InT 为 Set 层归纳关系）；零 Axiom/Admitted/经典逻辑；文件尾
     逐件 Print Assumptions 取 Closed 判据。
   编译配方：coqc -q -Q <主vo树> "" -Q . "" uabd_supply_UpReqDist_group_size_pos.v
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import UpReqDist.
From Stdlib Require Import List.
Import ListNotations.
Import RealInterfaceEnhancedMod.

Section uabdReqGrpSupply.

Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.

(* ①：S k 形嵌入严格正（对 k 归纳） *)
Lemma uabd_reqd_nat_S_pos :
  forall k : nat, lt zero (@UpReqDist.reqd_of_nat R RIS (Datatypes.S k)).
Proof.
  intro k. induction k as [| k IH].
  - (* 基座：reqd_of_nat 1 约化为 1 + 0，换形回 one 后用 one_pos *)
    apply (lt_id_r zero one (@UpReqDist.reqd_of_nat R RIS 1)).
    + apply (req_trans one (plus one zero) (@UpReqDist.reqd_of_nat R RIS 1)).
      * apply (req_sym (plus one zero) one). apply plus_zero.
      * apply req_refl.
    + exact one_pos.
  - (* 步进：reqd_of_nat (S (S k)) 约化为 1 + reqd_of_nat (S k)，双正合成 *)
    apply (lt_id_r zero (plus one (@UpReqDist.reqd_of_nat R RIS (Datatypes.S k)))
                      (@UpReqDist.reqd_of_nat R RIS (Datatypes.S (Datatypes.S k)))).
    + apply req_refl.
    + apply plus_positive.
      * exact one_pos.
      * exact IH.
Qed.

(* ②：覆盖见证形——对 InT 推导归纳（两构造子皆 cons 形，规避空匹配） *)
Theorem uabd_reqd_len_pos_cover :
  forall (G : Set) (enum : list G),
    (forall i : G, InT i enum) ->
    forall g0 : G,
      lt zero (@UpReqDist.reqd_of_nat R RIS (Datatypes.length enum)).
Proof.
  intros G enum cover g0.
  induction (cover g0) as [l0 | y l0 Hin IH].
  - exact (uabd_reqd_nat_S_pos (Datatypes.length l0)).
  - exact (uabd_reqd_nat_S_pos (Datatypes.length l0)).
Qed.

End uabdReqGrpSupply.

Print Assumptions uabd_reqd_nat_S_pos.
Print Assumptions uabd_reqd_len_pos_cover.
