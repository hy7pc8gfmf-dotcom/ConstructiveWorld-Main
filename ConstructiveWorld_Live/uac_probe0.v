(* uac_probe0.v — UpReqU2 接口签名检验件。
   使命: 以类型检查核对反向 KL 步与策略单调改进两接口签名在位，零新数学内容。
   依赖: CW_ConstructiveWorld_219、UpReqAlgebra、UpReqAlign、UpReqAlign2、UpReqAlign3、UpReqU2。
   对标: req2_backward_kl_step、r2_policy_improvement_mono。
   构造性注记: 只含 Require 与 Check 语句，无新定义与证明，零公理引入。
   编译配方: coqc -Q . "" ConstructiveWorld_Live/uac_probe0.v。 *)
Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqAlign.
Require Import UpReqAlign2.
Require Import UpReqAlign3.
Require UpReqU2.
Check @req2_backward_kl_step.
Check @r2_policy_improvement_mono.
