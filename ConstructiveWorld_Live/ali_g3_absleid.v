(* ali_g3_absleid.v — G3 提取探针（CYB6）：AbsLeId 旗舰件抽象主证提取面
   编译 stdout 即 g3 日志，grep Obj.magic 计数须为 0。
   纪律：文件式 Extraction 前置显式 Require Extraction（E375/E368 定式）；
   只提主定理，不搞全量 Recursive Extraction（依赖闭包大）。 *)
From Stdlib Require Import Extraction.
Require Import AbsLeId.

Recursive Extraction ali_abs_ge_zero_id.
