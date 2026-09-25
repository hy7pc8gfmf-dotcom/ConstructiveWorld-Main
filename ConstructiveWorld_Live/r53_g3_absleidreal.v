(* r53_g3_absleidreal.v — G3 提取检验（T53B）：AbsLeIdReal53 Real 层主件提取面
   编译 stdout 即 g3 日志，grep Obj.magic 计数须为 0。
   纪律：文件式 Extraction 前置显式 Require Extraction（E375/E368 定式）；
   只提 Real 层主定理，不搞全量依赖闭包；检验尾补 PA
   （CZB8 卡：裸检验吃 G1 扫描器 PA≥1 口径判 FAIL）。 *)
From Stdlib Require Import Extraction.
Require Import AbsLeIdReal53.

Recursive Extraction r53_real_abs_ge_zero_id.
Print Assumptions r53_real_abs_ge_zero_id.
