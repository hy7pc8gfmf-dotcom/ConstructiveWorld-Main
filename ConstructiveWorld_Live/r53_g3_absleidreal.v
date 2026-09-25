(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* r53_g3_absleidreal.v — G3 提取检验（B）：AbsLeIdReal53 Real 层主件提取面
   编译 stdout 即 g3 日志，grep Obj.magic 计数须为 0。
   纪律：文件式 Extraction 前置显式 Require Extraction（E375/E368 定式）；
   只提 Real 层主定理，不搞全量依赖闭包；检验尾补 PA
   （CZB8 卡：裸检验吃 G1 扫描器 PA≥1 口径判 FAIL）。 *)
From Stdlib Require Import Extraction.
Require Import AbsLeIdReal53.

Recursive Extraction r53_real_abs_ge_zero_id.
Print Assumptions r53_real_abs_ge_zero_id.
