(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
From Stdlib Require Import Extraction.
Require Import FepIdConsume.
(* G3 ext 检验：via_id 链与实例面——magic 计数分层如实登记（P6A 卡坑5：
   fic_id_bridge/tsi_rie_setoid/RealEnhancedReal 不被提取器 δ 的装箱强制
   转换，req:=Id 等可转换类型间运行时恒等、零逻辑内容） *)
Separate Extraction fic2_attention_is_gibbs_temp_id_consume.
Separate Extraction fic2_real_instance_gibbs_consume.
