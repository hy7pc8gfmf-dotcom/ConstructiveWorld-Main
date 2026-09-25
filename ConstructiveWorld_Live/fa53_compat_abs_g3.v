(* ============================================================ *)
(* fa53_compat_abs_g3.v —— fa53_compat_abs 序判面可提取性检验件 *)
(* 使命：本件以 Separate Extraction 抽取 fa53_compat_abs 的两个序判 *)
(*   见证——fa53_lt_dec（R 上三分 Or (lt a b) (Or (Id a b) (lt b a)) 的 *)
(*   显式判定）与 fa53_not_le_lt（Not (le a b) 输入下给出换序 lt b a）—— *)
(*   验证该兼容层的决策面可编译为计算码。 *)
(* 依赖：fa53_compat_abs；Stdlib Extraction。 *)
(* 对标行：fa53_compat_abs（lt_dec/not_le_lt 投影别名，防与 Stdlib *)
(*   Compare_dec.lt_dec 同名遮蔽）。 *)
(* 构造性注记：本件零新增语句，仅提取命令；被抽见证均为构造体。 *)
(* 编译配方：Rocq 9.1 coqc 直调，-native-compiler no -Q . ""， *)
(*   先 COQLIB/ROCQLIB 同源双 export。 *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Require Import fa53_compat_abs.
Separate Extraction fa53_lt_dec fa53_not_le_lt.
