(* piu_zz_tau_enclosure_bank3.v — piu_zz_tau_enclosure 模块分解第 3 段（共四段）。
   使命：zz_in_Pn 逐点判定表第 1537–2048 条（piu_zz_inPn_1024_1025 … piu_zz_inPn_1024_1536），供 zz_Phi 字面值链
   逐点引用；每条引理由 unfold 后单点计算或最小素因子试除见证自证。
   依赖：piu_zz_tau_enclosure_bank2（前置链）、piu_zz_poincare_engine
   （zz_in_Pn/zz_primeb）、piu_zz_padic_clearing、
   Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure 原单件（ 六 片 split, statements byte-equivalent).
   构造性：全部语句为 bool 等式，闭式自证，零假设、零公理。
   编译配方: coqc -native-compiler no -q -Q . "" piu_zz_tau_enclosure_bank3.v *)
Require Export piu_zz_tau_enclosure_bank2.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
Lemma piu_zz_inPn_1024_1025 : zz_in_Pn 1024 1025 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1025)) (2 * 1025)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1026 : zz_in_Pn 1024 1026 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1026)) (2 * 1026)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1027 : zz_in_Pn 1024 1027 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1027)) (2 * 1027)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1028 : zz_in_Pn 1024 1028 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1028)) (2 * 1028)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1029 : zz_in_Pn 1024 1029 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1029)) (2 * 1029)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1030 : zz_in_Pn 1024 1030 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1030)) (2 * 1030)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1031 : zz_in_Pn 1024 1031 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1031)) (2 * 1031)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1032 : zz_in_Pn 1024 1032 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1032)) (2 * 1032)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1033 : zz_in_Pn 1024 1033 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1033)) (2 * 1033)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1034 : zz_in_Pn 1024 1034 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1034)) (2 * 1034)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1035 : zz_in_Pn 1024 1035 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1035)) (2 * 1035)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1036 : zz_in_Pn 1024 1036 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1036)) (2 * 1036)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1037 : zz_in_Pn 1024 1037 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1037)) (2 * 1037)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1038 : zz_in_Pn 1024 1038 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1038)) (2 * 1038)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1039 : zz_in_Pn 1024 1039 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1039)) (2 * 1039)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1040 : zz_in_Pn 1024 1040 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1040)) (2 * 1040)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1041 : zz_in_Pn 1024 1041 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1041)) (2 * 1041)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1042 : zz_in_Pn 1024 1042 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1042)) (2 * 1042)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1043 : zz_in_Pn 1024 1043 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1043)) (2 * 1043)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1044 : zz_in_Pn 1024 1044 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1044)) (2 * 1044)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1045 : zz_in_Pn 1024 1045 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1045)) (2 * 1045)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1046 : zz_in_Pn 1024 1046 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1046)) (2 * 1046)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1047 : zz_in_Pn 1024 1047 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1047)) (2 * 1047)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1048 : zz_in_Pn 1024 1048 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1048)) (2 * 1048)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1049 : zz_in_Pn 1024 1049 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1049)) (2 * 1049)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1050 : zz_in_Pn 1024 1050 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1050)) (2 * 1050)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1051 : zz_in_Pn 1024 1051 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1051)) (2 * 1051)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1052 : zz_in_Pn 1024 1052 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1052)) (2 * 1052)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1053 : zz_in_Pn 1024 1053 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1053)) (2 * 1053)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1054 : zz_in_Pn 1024 1054 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1054)) (2 * 1054)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1055 : zz_in_Pn 1024 1055 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1055)) (2 * 1055)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1056 : zz_in_Pn 1024 1056 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1056)) (2 * 1056)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1057 : zz_in_Pn 1024 1057 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1057)) (2 * 1057)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1058 : zz_in_Pn 1024 1058 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1058)) (2 * 1058)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1059 : zz_in_Pn 1024 1059 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1059)) (2 * 1059)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1060 : zz_in_Pn 1024 1060 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1060)) (2 * 1060)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1061 : zz_in_Pn 1024 1061 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1061)) (2 * 1061)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1062 : zz_in_Pn 1024 1062 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1062)) (2 * 1062)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1063 : zz_in_Pn 1024 1063 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1063)) (2 * 1063)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1064 : zz_in_Pn 1024 1064 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1064)) (2 * 1064)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1065 : zz_in_Pn 1024 1065 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1065)) (2 * 1065)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1066 : zz_in_Pn 1024 1066 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1066)) (2 * 1066)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1067 : zz_in_Pn 1024 1067 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1067)) (2 * 1067)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1068 : zz_in_Pn 1024 1068 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1068)) (2 * 1068)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1069 : zz_in_Pn 1024 1069 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1069)) (2 * 1069)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1070 : zz_in_Pn 1024 1070 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1070)) (2 * 1070)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1071 : zz_in_Pn 1024 1071 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1071)) (2 * 1071)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1072 : zz_in_Pn 1024 1072 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1072)) (2 * 1072)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1073 : zz_in_Pn 1024 1073 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1073)) (2 * 1073)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1074 : zz_in_Pn 1024 1074 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1074)) (2 * 1074)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1075 : zz_in_Pn 1024 1075 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1075)) (2 * 1075)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1076 : zz_in_Pn 1024 1076 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1076)) (2 * 1076)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1077 : zz_in_Pn 1024 1077 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1077)) (2 * 1077)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1078 : zz_in_Pn 1024 1078 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1078)) (2 * 1078)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1079 : zz_in_Pn 1024 1079 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1079)) (2 * 1079)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1080 : zz_in_Pn 1024 1080 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1080)) (2 * 1080)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1081 : zz_in_Pn 1024 1081 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1081)) (2 * 1081)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1082 : zz_in_Pn 1024 1082 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1082)) (2 * 1082)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1083 : zz_in_Pn 1024 1083 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1083)) (2 * 1083)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1084 : zz_in_Pn 1024 1084 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1084)) (2 * 1084)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1085 : zz_in_Pn 1024 1085 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1085)) (2 * 1085)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1086 : zz_in_Pn 1024 1086 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1086)) (2 * 1086)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1087 : zz_in_Pn 1024 1087 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1087)) (2 * 1087)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1088 : zz_in_Pn 1024 1088 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1088)) (2 * 1088)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1089 : zz_in_Pn 1024 1089 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1089)) (2 * 1089)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1090 : zz_in_Pn 1024 1090 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1090)) (2 * 1090)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1091 : zz_in_Pn 1024 1091 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1091)) (2 * 1091)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1092 : zz_in_Pn 1024 1092 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1092)) (2 * 1092)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1093 : zz_in_Pn 1024 1093 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1093)) (2 * 1093)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1094 : zz_in_Pn 1024 1094 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1094)) (2 * 1094)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1095 : zz_in_Pn 1024 1095 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1095)) (2 * 1095)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1096 : zz_in_Pn 1024 1096 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1096)) (2 * 1096)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1097 : zz_in_Pn 1024 1097 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1097)) (2 * 1097)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1098 : zz_in_Pn 1024 1098 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1098)) (2 * 1098)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1099 : zz_in_Pn 1024 1099 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1099)) (2 * 1099)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1100 : zz_in_Pn 1024 1100 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1100)) (2 * 1100)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1101 : zz_in_Pn 1024 1101 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1101)) (2 * 1101)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1102 : zz_in_Pn 1024 1102 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1102)) (2 * 1102)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1103 : zz_in_Pn 1024 1103 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1103)) (2 * 1103)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1104 : zz_in_Pn 1024 1104 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1104)) (2 * 1104)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1105 : zz_in_Pn 1024 1105 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1105)) (2 * 1105)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1106 : zz_in_Pn 1024 1106 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1106)) (2 * 1106)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1107 : zz_in_Pn 1024 1107 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1107)) (2 * 1107)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1108 : zz_in_Pn 1024 1108 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1108)) (2 * 1108)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1109 : zz_in_Pn 1024 1109 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1109)) (2 * 1109)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1110 : zz_in_Pn 1024 1110 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1110)) (2 * 1110)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1111 : zz_in_Pn 1024 1111 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1111)) (2 * 1111)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1112 : zz_in_Pn 1024 1112 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1112)) (2 * 1112)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1113 : zz_in_Pn 1024 1113 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1113)) (2 * 1113)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1114 : zz_in_Pn 1024 1114 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1114)) (2 * 1114)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1115 : zz_in_Pn 1024 1115 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1115)) (2 * 1115)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1116 : zz_in_Pn 1024 1116 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1116)) (2 * 1116)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1117 : zz_in_Pn 1024 1117 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1117)) (2 * 1117)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1118 : zz_in_Pn 1024 1118 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1118)) (2 * 1118)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1119 : zz_in_Pn 1024 1119 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1119)) (2 * 1119)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1120 : zz_in_Pn 1024 1120 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1120)) (2 * 1120)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1121 : zz_in_Pn 1024 1121 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1121)) (2 * 1121)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1122 : zz_in_Pn 1024 1122 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1122)) (2 * 1122)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1123 : zz_in_Pn 1024 1123 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1123)) (2 * 1123)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1124 : zz_in_Pn 1024 1124 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1124)) (2 * 1124)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1125 : zz_in_Pn 1024 1125 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1125)) (2 * 1125)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1126 : zz_in_Pn 1024 1126 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1126)) (2 * 1126)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1127 : zz_in_Pn 1024 1127 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1127)) (2 * 1127)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1128 : zz_in_Pn 1024 1128 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1128)) (2 * 1128)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1129 : zz_in_Pn 1024 1129 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1129)) (2 * 1129)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1130 : zz_in_Pn 1024 1130 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1130)) (2 * 1130)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1131 : zz_in_Pn 1024 1131 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1131)) (2 * 1131)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1132 : zz_in_Pn 1024 1132 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1132)) (2 * 1132)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1133 : zz_in_Pn 1024 1133 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1133)) (2 * 1133)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1134 : zz_in_Pn 1024 1134 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1134)) (2 * 1134)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1135 : zz_in_Pn 1024 1135 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1135)) (2 * 1135)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1136 : zz_in_Pn 1024 1136 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1136)) (2 * 1136)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1137 : zz_in_Pn 1024 1137 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1137)) (2 * 1137)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1138 : zz_in_Pn 1024 1138 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1138)) (2 * 1138)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1139 : zz_in_Pn 1024 1139 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1139)) (2 * 1139)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1140 : zz_in_Pn 1024 1140 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1140)) (2 * 1140)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1141 : zz_in_Pn 1024 1141 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1141)) (2 * 1141)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1142 : zz_in_Pn 1024 1142 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1142)) (2 * 1142)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1143 : zz_in_Pn 1024 1143 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1143)) (2 * 1143)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1144 : zz_in_Pn 1024 1144 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1144)) (2 * 1144)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1145 : zz_in_Pn 1024 1145 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1145)) (2 * 1145)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1146 : zz_in_Pn 1024 1146 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1146)) (2 * 1146)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1147 : zz_in_Pn 1024 1147 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1147)) (2 * 1147)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1148 : zz_in_Pn 1024 1148 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1148)) (2 * 1148)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1149 : zz_in_Pn 1024 1149 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1149)) (2 * 1149)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1150 : zz_in_Pn 1024 1150 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1150)) (2 * 1150)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1151 : zz_in_Pn 1024 1151 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1151)) (2 * 1151)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1152 : zz_in_Pn 1024 1152 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1152)) (2 * 1152)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1153 : zz_in_Pn 1024 1153 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1153)) (2 * 1153)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1154 : zz_in_Pn 1024 1154 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1154)) (2 * 1154)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1155 : zz_in_Pn 1024 1155 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1155)) (2 * 1155)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1156 : zz_in_Pn 1024 1156 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1156)) (2 * 1156)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1157 : zz_in_Pn 1024 1157 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1157)) (2 * 1157)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1158 : zz_in_Pn 1024 1158 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1158)) (2 * 1158)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1159 : zz_in_Pn 1024 1159 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1159)) (2 * 1159)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1160 : zz_in_Pn 1024 1160 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1160)) (2 * 1160)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1161 : zz_in_Pn 1024 1161 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1161)) (2 * 1161)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1162 : zz_in_Pn 1024 1162 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1162)) (2 * 1162)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1163 : zz_in_Pn 1024 1163 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1163)) (2 * 1163)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1164 : zz_in_Pn 1024 1164 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1164)) (2 * 1164)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1165 : zz_in_Pn 1024 1165 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1165)) (2 * 1165)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1166 : zz_in_Pn 1024 1166 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1166)) (2 * 1166)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1167 : zz_in_Pn 1024 1167 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1167)) (2 * 1167)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1168 : zz_in_Pn 1024 1168 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1168)) (2 * 1168)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1169 : zz_in_Pn 1024 1169 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1169)) (2 * 1169)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1170 : zz_in_Pn 1024 1170 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1170)) (2 * 1170)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1171 : zz_in_Pn 1024 1171 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1171)) (2 * 1171)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1172 : zz_in_Pn 1024 1172 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1172)) (2 * 1172)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1173 : zz_in_Pn 1024 1173 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1173)) (2 * 1173)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1174 : zz_in_Pn 1024 1174 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1174)) (2 * 1174)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1175 : zz_in_Pn 1024 1175 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1175)) (2 * 1175)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1176 : zz_in_Pn 1024 1176 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1176)) (2 * 1176)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1177 : zz_in_Pn 1024 1177 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1177)) (2 * 1177)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1178 : zz_in_Pn 1024 1178 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1178)) (2 * 1178)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1179 : zz_in_Pn 1024 1179 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1179)) (2 * 1179)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1180 : zz_in_Pn 1024 1180 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1180)) (2 * 1180)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1181 : zz_in_Pn 1024 1181 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1181)) (2 * 1181)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1182 : zz_in_Pn 1024 1182 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1182)) (2 * 1182)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1183 : zz_in_Pn 1024 1183 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1183)) (2 * 1183)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1184 : zz_in_Pn 1024 1184 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1184)) (2 * 1184)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1185 : zz_in_Pn 1024 1185 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1185)) (2 * 1185)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1186 : zz_in_Pn 1024 1186 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1186)) (2 * 1186)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1187 : zz_in_Pn 1024 1187 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1187)) (2 * 1187)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1188 : zz_in_Pn 1024 1188 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1188)) (2 * 1188)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1189 : zz_in_Pn 1024 1189 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1189)) (2 * 1189)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1190 : zz_in_Pn 1024 1190 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1190)) (2 * 1190)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1191 : zz_in_Pn 1024 1191 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1191)) (2 * 1191)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1192 : zz_in_Pn 1024 1192 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1192)) (2 * 1192)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1193 : zz_in_Pn 1024 1193 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1193)) (2 * 1193)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1194 : zz_in_Pn 1024 1194 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1194)) (2 * 1194)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1195 : zz_in_Pn 1024 1195 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1195)) (2 * 1195)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1196 : zz_in_Pn 1024 1196 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1196)) (2 * 1196)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1197 : zz_in_Pn 1024 1197 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1197)) (2 * 1197)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1198 : zz_in_Pn 1024 1198 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1198)) (2 * 1198)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1199 : zz_in_Pn 1024 1199 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1199)) (2 * 1199)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1200 : zz_in_Pn 1024 1200 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1200)) (2 * 1200)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1201 : zz_in_Pn 1024 1201 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1201)) (2 * 1201)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1202 : zz_in_Pn 1024 1202 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1202)) (2 * 1202)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1203 : zz_in_Pn 1024 1203 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1203)) (2 * 1203)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1204 : zz_in_Pn 1024 1204 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1204)) (2 * 1204)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1205 : zz_in_Pn 1024 1205 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1205)) (2 * 1205)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1206 : zz_in_Pn 1024 1206 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1206)) (2 * 1206)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1207 : zz_in_Pn 1024 1207 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1207)) (2 * 1207)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1208 : zz_in_Pn 1024 1208 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1208)) (2 * 1208)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1209 : zz_in_Pn 1024 1209 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1209)) (2 * 1209)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1210 : zz_in_Pn 1024 1210 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1210)) (2 * 1210)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1211 : zz_in_Pn 1024 1211 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1211)) (2 * 1211)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1212 : zz_in_Pn 1024 1212 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1212)) (2 * 1212)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1213 : zz_in_Pn 1024 1213 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1213)) (2 * 1213)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1214 : zz_in_Pn 1024 1214 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1214)) (2 * 1214)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1215 : zz_in_Pn 1024 1215 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1215)) (2 * 1215)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1216 : zz_in_Pn 1024 1216 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1216)) (2 * 1216)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1217 : zz_in_Pn 1024 1217 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1217)) (2 * 1217)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1218 : zz_in_Pn 1024 1218 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1218)) (2 * 1218)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1219 : zz_in_Pn 1024 1219 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1219)) (2 * 1219)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1220 : zz_in_Pn 1024 1220 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1220)) (2 * 1220)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1221 : zz_in_Pn 1024 1221 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1221)) (2 * 1221)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1222 : zz_in_Pn 1024 1222 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1222)) (2 * 1222)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1223 : zz_in_Pn 1024 1223 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1223)) (2 * 1223)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1224 : zz_in_Pn 1024 1224 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1224)) (2 * 1224)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1225 : zz_in_Pn 1024 1225 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1225)) (2 * 1225)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1226 : zz_in_Pn 1024 1226 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1226)) (2 * 1226)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1227 : zz_in_Pn 1024 1227 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1227)) (2 * 1227)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1228 : zz_in_Pn 1024 1228 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1228)) (2 * 1228)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1229 : zz_in_Pn 1024 1229 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1229)) (2 * 1229)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1230 : zz_in_Pn 1024 1230 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1230)) (2 * 1230)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1231 : zz_in_Pn 1024 1231 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1231)) (2 * 1231)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1232 : zz_in_Pn 1024 1232 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1232)) (2 * 1232)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1233 : zz_in_Pn 1024 1233 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1233)) (2 * 1233)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1234 : zz_in_Pn 1024 1234 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1234)) (2 * 1234)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1235 : zz_in_Pn 1024 1235 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1235)) (2 * 1235)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1236 : zz_in_Pn 1024 1236 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1236)) (2 * 1236)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1237 : zz_in_Pn 1024 1237 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1237)) (2 * 1237)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1238 : zz_in_Pn 1024 1238 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1238)) (2 * 1238)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1239 : zz_in_Pn 1024 1239 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1239)) (2 * 1239)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1240 : zz_in_Pn 1024 1240 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1240)) (2 * 1240)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1241 : zz_in_Pn 1024 1241 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1241)) (2 * 1241)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1242 : zz_in_Pn 1024 1242 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1242)) (2 * 1242)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1243 : zz_in_Pn 1024 1243 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1243)) (2 * 1243)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1244 : zz_in_Pn 1024 1244 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1244)) (2 * 1244)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1245 : zz_in_Pn 1024 1245 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1245)) (2 * 1245)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1246 : zz_in_Pn 1024 1246 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1246)) (2 * 1246)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1247 : zz_in_Pn 1024 1247 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1247)) (2 * 1247)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1248 : zz_in_Pn 1024 1248 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1248)) (2 * 1248)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1249 : zz_in_Pn 1024 1249 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1249)) (2 * 1249)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1250 : zz_in_Pn 1024 1250 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1250)) (2 * 1250)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1251 : zz_in_Pn 1024 1251 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1251)) (2 * 1251)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1252 : zz_in_Pn 1024 1252 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1252)) (2 * 1252)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1253 : zz_in_Pn 1024 1253 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1253)) (2 * 1253)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1254 : zz_in_Pn 1024 1254 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1254)) (2 * 1254)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1255 : zz_in_Pn 1024 1255 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1255)) (2 * 1255)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1256 : zz_in_Pn 1024 1256 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1256)) (2 * 1256)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1257 : zz_in_Pn 1024 1257 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1257)) (2 * 1257)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1258 : zz_in_Pn 1024 1258 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1258)) (2 * 1258)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1259 : zz_in_Pn 1024 1259 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1259)) (2 * 1259)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1260 : zz_in_Pn 1024 1260 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1260)) (2 * 1260)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1261 : zz_in_Pn 1024 1261 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1261)) (2 * 1261)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1262 : zz_in_Pn 1024 1262 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1262)) (2 * 1262)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1263 : zz_in_Pn 1024 1263 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1263)) (2 * 1263)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1264 : zz_in_Pn 1024 1264 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1264)) (2 * 1264)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1265 : zz_in_Pn 1024 1265 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1265)) (2 * 1265)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1266 : zz_in_Pn 1024 1266 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1266)) (2 * 1266)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1267 : zz_in_Pn 1024 1267 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1267)) (2 * 1267)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1268 : zz_in_Pn 1024 1268 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1268)) (2 * 1268)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1269 : zz_in_Pn 1024 1269 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1269)) (2 * 1269)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1270 : zz_in_Pn 1024 1270 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1270)) (2 * 1270)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1271 : zz_in_Pn 1024 1271 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1271)) (2 * 1271)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1272 : zz_in_Pn 1024 1272 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1272)) (2 * 1272)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1273 : zz_in_Pn 1024 1273 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1273)) (2 * 1273)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1274 : zz_in_Pn 1024 1274 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1274)) (2 * 1274)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1275 : zz_in_Pn 1024 1275 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1275)) (2 * 1275)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1276 : zz_in_Pn 1024 1276 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1276)) (2 * 1276)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1277 : zz_in_Pn 1024 1277 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1277)) (2 * 1277)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1278 : zz_in_Pn 1024 1278 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1278)) (2 * 1278)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1279 : zz_in_Pn 1024 1279 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1279)) (2 * 1279)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1280 : zz_in_Pn 1024 1280 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1280)) (2 * 1280)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1281 : zz_in_Pn 1024 1281 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1281)) (2 * 1281)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1282 : zz_in_Pn 1024 1282 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1282)) (2 * 1282)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1283 : zz_in_Pn 1024 1283 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1283)) (2 * 1283)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1284 : zz_in_Pn 1024 1284 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1284)) (2 * 1284)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1285 : zz_in_Pn 1024 1285 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1285)) (2 * 1285)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1286 : zz_in_Pn 1024 1286 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1286)) (2 * 1286)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1287 : zz_in_Pn 1024 1287 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1287)) (2 * 1287)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1288 : zz_in_Pn 1024 1288 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1288)) (2 * 1288)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1289 : zz_in_Pn 1024 1289 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1289)) (2 * 1289)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1290 : zz_in_Pn 1024 1290 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1290)) (2 * 1290)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1291 : zz_in_Pn 1024 1291 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1291)) (2 * 1291)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1292 : zz_in_Pn 1024 1292 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1292)) (2 * 1292)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1293 : zz_in_Pn 1024 1293 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1293)) (2 * 1293)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1294 : zz_in_Pn 1024 1294 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1294)) (2 * 1294)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1295 : zz_in_Pn 1024 1295 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1295)) (2 * 1295)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1296 : zz_in_Pn 1024 1296 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1296)) (2 * 1296)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1297 : zz_in_Pn 1024 1297 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1297)) (2 * 1297)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1298 : zz_in_Pn 1024 1298 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1298)) (2 * 1298)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1299 : zz_in_Pn 1024 1299 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1299)) (2 * 1299)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1300 : zz_in_Pn 1024 1300 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1300)) (2 * 1300)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1301 : zz_in_Pn 1024 1301 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1301)) (2 * 1301)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1302 : zz_in_Pn 1024 1302 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1302)) (2 * 1302)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1303 : zz_in_Pn 1024 1303 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1303)) (2 * 1303)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1304 : zz_in_Pn 1024 1304 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1304)) (2 * 1304)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1305 : zz_in_Pn 1024 1305 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1305)) (2 * 1305)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1306 : zz_in_Pn 1024 1306 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1306)) (2 * 1306)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1307 : zz_in_Pn 1024 1307 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1307)) (2 * 1307)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1308 : zz_in_Pn 1024 1308 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1308)) (2 * 1308)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1309 : zz_in_Pn 1024 1309 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1309)) (2 * 1309)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1310 : zz_in_Pn 1024 1310 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1310)) (2 * 1310)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1311 : zz_in_Pn 1024 1311 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1311)) (2 * 1311)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1312 : zz_in_Pn 1024 1312 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1312)) (2 * 1312)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1313 : zz_in_Pn 1024 1313 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1313)) (2 * 1313)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1314 : zz_in_Pn 1024 1314 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1314)) (2 * 1314)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1315 : zz_in_Pn 1024 1315 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1315)) (2 * 1315)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1316 : zz_in_Pn 1024 1316 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1316)) (2 * 1316)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1317 : zz_in_Pn 1024 1317 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1317)) (2 * 1317)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1318 : zz_in_Pn 1024 1318 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1318)) (2 * 1318)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1319 : zz_in_Pn 1024 1319 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1319)) (2 * 1319)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1320 : zz_in_Pn 1024 1320 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1320)) (2 * 1320)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1321 : zz_in_Pn 1024 1321 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1321)) (2 * 1321)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1322 : zz_in_Pn 1024 1322 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1322)) (2 * 1322)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1323 : zz_in_Pn 1024 1323 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1323)) (2 * 1323)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1324 : zz_in_Pn 1024 1324 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1324)) (2 * 1324)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1325 : zz_in_Pn 1024 1325 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1325)) (2 * 1325)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1326 : zz_in_Pn 1024 1326 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1326)) (2 * 1326)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1327 : zz_in_Pn 1024 1327 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1327)) (2 * 1327)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1328 : zz_in_Pn 1024 1328 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1328)) (2 * 1328)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1329 : zz_in_Pn 1024 1329 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1329)) (2 * 1329)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1330 : zz_in_Pn 1024 1330 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1330)) (2 * 1330)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1331 : zz_in_Pn 1024 1331 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1331)) (2 * 1331)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1332 : zz_in_Pn 1024 1332 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1332)) (2 * 1332)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1333 : zz_in_Pn 1024 1333 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1333)) (2 * 1333)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1334 : zz_in_Pn 1024 1334 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1334)) (2 * 1334)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1335 : zz_in_Pn 1024 1335 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1335)) (2 * 1335)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1336 : zz_in_Pn 1024 1336 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1336)) (2 * 1336)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1337 : zz_in_Pn 1024 1337 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1337)) (2 * 1337)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1338 : zz_in_Pn 1024 1338 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1338)) (2 * 1338)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1339 : zz_in_Pn 1024 1339 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1339)) (2 * 1339)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1340 : zz_in_Pn 1024 1340 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1340)) (2 * 1340)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1341 : zz_in_Pn 1024 1341 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1341)) (2 * 1341)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1342 : zz_in_Pn 1024 1342 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1342)) (2 * 1342)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1343 : zz_in_Pn 1024 1343 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1343)) (2 * 1343)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1344 : zz_in_Pn 1024 1344 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1344)) (2 * 1344)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1345 : zz_in_Pn 1024 1345 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1345)) (2 * 1345)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1346 : zz_in_Pn 1024 1346 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1346)) (2 * 1346)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1347 : zz_in_Pn 1024 1347 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1347)) (2 * 1347)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1348 : zz_in_Pn 1024 1348 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1348)) (2 * 1348)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1349 : zz_in_Pn 1024 1349 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1349)) (2 * 1349)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1350 : zz_in_Pn 1024 1350 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1350)) (2 * 1350)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1351 : zz_in_Pn 1024 1351 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1351)) (2 * 1351)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1352 : zz_in_Pn 1024 1352 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1352)) (2 * 1352)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1353 : zz_in_Pn 1024 1353 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1353)) (2 * 1353)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1354 : zz_in_Pn 1024 1354 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1354)) (2 * 1354)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1355 : zz_in_Pn 1024 1355 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1355)) (2 * 1355)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1356 : zz_in_Pn 1024 1356 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1356)) (2 * 1356)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1357 : zz_in_Pn 1024 1357 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1357)) (2 * 1357)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1358 : zz_in_Pn 1024 1358 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1358)) (2 * 1358)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1359 : zz_in_Pn 1024 1359 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1359)) (2 * 1359)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1360 : zz_in_Pn 1024 1360 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1360)) (2 * 1360)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1361 : zz_in_Pn 1024 1361 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1361)) (2 * 1361)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1362 : zz_in_Pn 1024 1362 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1362)) (2 * 1362)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1363 : zz_in_Pn 1024 1363 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1363)) (2 * 1363)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1364 : zz_in_Pn 1024 1364 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1364)) (2 * 1364)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1365 : zz_in_Pn 1024 1365 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1365)) (2 * 1365)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1366 : zz_in_Pn 1024 1366 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1366)) (2 * 1366)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1367 : zz_in_Pn 1024 1367 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1367)) (2 * 1367)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1368 : zz_in_Pn 1024 1368 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1368)) (2 * 1368)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1369 : zz_in_Pn 1024 1369 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1369)) (2 * 1369)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1370 : zz_in_Pn 1024 1370 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1370)) (2 * 1370)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1371 : zz_in_Pn 1024 1371 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1371)) (2 * 1371)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1372 : zz_in_Pn 1024 1372 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1372)) (2 * 1372)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1373 : zz_in_Pn 1024 1373 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1373)) (2 * 1373)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1374 : zz_in_Pn 1024 1374 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1374)) (2 * 1374)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1375 : zz_in_Pn 1024 1375 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1375)) (2 * 1375)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1376 : zz_in_Pn 1024 1376 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1376)) (2 * 1376)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1377 : zz_in_Pn 1024 1377 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1377)) (2 * 1377)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1378 : zz_in_Pn 1024 1378 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1378)) (2 * 1378)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1379 : zz_in_Pn 1024 1379 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1379)) (2 * 1379)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1380 : zz_in_Pn 1024 1380 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1380)) (2 * 1380)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1381 : zz_in_Pn 1024 1381 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1381)) (2 * 1381)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1382 : zz_in_Pn 1024 1382 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1382)) (2 * 1382)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1383 : zz_in_Pn 1024 1383 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1383)) (2 * 1383)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1384 : zz_in_Pn 1024 1384 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1384)) (2 * 1384)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1385 : zz_in_Pn 1024 1385 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1385)) (2 * 1385)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1386 : zz_in_Pn 1024 1386 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1386)) (2 * 1386)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1387 : zz_in_Pn 1024 1387 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1387)) (2 * 1387)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1388 : zz_in_Pn 1024 1388 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1388)) (2 * 1388)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1389 : zz_in_Pn 1024 1389 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1389)) (2 * 1389)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1390 : zz_in_Pn 1024 1390 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1390)) (2 * 1390)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1391 : zz_in_Pn 1024 1391 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1391)) (2 * 1391)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1392 : zz_in_Pn 1024 1392 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1392)) (2 * 1392)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1393 : zz_in_Pn 1024 1393 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1393)) (2 * 1393)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1394 : zz_in_Pn 1024 1394 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1394)) (2 * 1394)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1395 : zz_in_Pn 1024 1395 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1395)) (2 * 1395)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1396 : zz_in_Pn 1024 1396 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1396)) (2 * 1396)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1397 : zz_in_Pn 1024 1397 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1397)) (2 * 1397)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1398 : zz_in_Pn 1024 1398 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1398)) (2 * 1398)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1399 : zz_in_Pn 1024 1399 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1399)) (2 * 1399)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1400 : zz_in_Pn 1024 1400 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1400)) (2 * 1400)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1401 : zz_in_Pn 1024 1401 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1401)) (2 * 1401)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1402 : zz_in_Pn 1024 1402 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1402)) (2 * 1402)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1403 : zz_in_Pn 1024 1403 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1403)) (2 * 1403)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1404 : zz_in_Pn 1024 1404 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1404)) (2 * 1404)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1405 : zz_in_Pn 1024 1405 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1405)) (2 * 1405)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1406 : zz_in_Pn 1024 1406 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1406)) (2 * 1406)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1407 : zz_in_Pn 1024 1407 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1407)) (2 * 1407)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1408 : zz_in_Pn 1024 1408 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1408)) (2 * 1408)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1409 : zz_in_Pn 1024 1409 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1409)) (2 * 1409)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1410 : zz_in_Pn 1024 1410 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1410)) (2 * 1410)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1411 : zz_in_Pn 1024 1411 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1411)) (2 * 1411)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1412 : zz_in_Pn 1024 1412 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1412)) (2 * 1412)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1413 : zz_in_Pn 1024 1413 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1413)) (2 * 1413)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1414 : zz_in_Pn 1024 1414 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1414)) (2 * 1414)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1415 : zz_in_Pn 1024 1415 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1415)) (2 * 1415)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1416 : zz_in_Pn 1024 1416 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1416)) (2 * 1416)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1417 : zz_in_Pn 1024 1417 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1417)) (2 * 1417)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1418 : zz_in_Pn 1024 1418 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1418)) (2 * 1418)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1419 : zz_in_Pn 1024 1419 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1419)) (2 * 1419)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1420 : zz_in_Pn 1024 1420 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1420)) (2 * 1420)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1421 : zz_in_Pn 1024 1421 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1421)) (2 * 1421)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1422 : zz_in_Pn 1024 1422 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1422)) (2 * 1422)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1423 : zz_in_Pn 1024 1423 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1423)) (2 * 1423)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1424 : zz_in_Pn 1024 1424 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1424)) (2 * 1424)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1425 : zz_in_Pn 1024 1425 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1425)) (2 * 1425)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1426 : zz_in_Pn 1024 1426 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1426)) (2 * 1426)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1427 : zz_in_Pn 1024 1427 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1427)) (2 * 1427)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1428 : zz_in_Pn 1024 1428 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1428)) (2 * 1428)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1429 : zz_in_Pn 1024 1429 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1429)) (2 * 1429)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1430 : zz_in_Pn 1024 1430 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1430)) (2 * 1430)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1431 : zz_in_Pn 1024 1431 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1431)) (2 * 1431)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1432 : zz_in_Pn 1024 1432 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1432)) (2 * 1432)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1433 : zz_in_Pn 1024 1433 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1433)) (2 * 1433)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1434 : zz_in_Pn 1024 1434 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1434)) (2 * 1434)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1435 : zz_in_Pn 1024 1435 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1435)) (2 * 1435)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1436 : zz_in_Pn 1024 1436 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1436)) (2 * 1436)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1437 : zz_in_Pn 1024 1437 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1437)) (2 * 1437)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1438 : zz_in_Pn 1024 1438 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1438)) (2 * 1438)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1439 : zz_in_Pn 1024 1439 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1439)) (2 * 1439)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1440 : zz_in_Pn 1024 1440 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1440)) (2 * 1440)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1441 : zz_in_Pn 1024 1441 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1441)) (2 * 1441)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1442 : zz_in_Pn 1024 1442 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1442)) (2 * 1442)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1443 : zz_in_Pn 1024 1443 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1443)) (2 * 1443)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1444 : zz_in_Pn 1024 1444 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1444)) (2 * 1444)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1445 : zz_in_Pn 1024 1445 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1445)) (2 * 1445)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1446 : zz_in_Pn 1024 1446 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1446)) (2 * 1446)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1447 : zz_in_Pn 1024 1447 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1447)) (2 * 1447)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1448 : zz_in_Pn 1024 1448 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1448)) (2 * 1448)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1449 : zz_in_Pn 1024 1449 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1449)) (2 * 1449)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1450 : zz_in_Pn 1024 1450 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1450)) (2 * 1450)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1451 : zz_in_Pn 1024 1451 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1451)) (2 * 1451)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1452 : zz_in_Pn 1024 1452 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1452)) (2 * 1452)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1453 : zz_in_Pn 1024 1453 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1453)) (2 * 1453)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1454 : zz_in_Pn 1024 1454 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1454)) (2 * 1454)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1455 : zz_in_Pn 1024 1455 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1455)) (2 * 1455)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1456 : zz_in_Pn 1024 1456 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1456)) (2 * 1456)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1457 : zz_in_Pn 1024 1457 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1457)) (2 * 1457)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1458 : zz_in_Pn 1024 1458 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1458)) (2 * 1458)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1459 : zz_in_Pn 1024 1459 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1459)) (2 * 1459)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1460 : zz_in_Pn 1024 1460 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1460)) (2 * 1460)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1461 : zz_in_Pn 1024 1461 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1461)) (2 * 1461)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1462 : zz_in_Pn 1024 1462 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1462)) (2 * 1462)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1463 : zz_in_Pn 1024 1463 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1463)) (2 * 1463)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1464 : zz_in_Pn 1024 1464 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1464)) (2 * 1464)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1465 : zz_in_Pn 1024 1465 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1465)) (2 * 1465)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1466 : zz_in_Pn 1024 1466 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1466)) (2 * 1466)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1467 : zz_in_Pn 1024 1467 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1467)) (2 * 1467)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1468 : zz_in_Pn 1024 1468 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1468)) (2 * 1468)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1469 : zz_in_Pn 1024 1469 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1469)) (2 * 1469)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1470 : zz_in_Pn 1024 1470 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1470)) (2 * 1470)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1471 : zz_in_Pn 1024 1471 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1471)) (2 * 1471)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1472 : zz_in_Pn 1024 1472 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1472)) (2 * 1472)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1473 : zz_in_Pn 1024 1473 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1473)) (2 * 1473)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1474 : zz_in_Pn 1024 1474 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1474)) (2 * 1474)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1475 : zz_in_Pn 1024 1475 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1475)) (2 * 1475)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1476 : zz_in_Pn 1024 1476 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1476)) (2 * 1476)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1477 : zz_in_Pn 1024 1477 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1477)) (2 * 1477)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1478 : zz_in_Pn 1024 1478 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1478)) (2 * 1478)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1479 : zz_in_Pn 1024 1479 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1479)) (2 * 1479)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1480 : zz_in_Pn 1024 1480 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1480)) (2 * 1480)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1481 : zz_in_Pn 1024 1481 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1481)) (2 * 1481)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1482 : zz_in_Pn 1024 1482 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1482)) (2 * 1482)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1483 : zz_in_Pn 1024 1483 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1483)) (2 * 1483)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1484 : zz_in_Pn 1024 1484 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1484)) (2 * 1484)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1485 : zz_in_Pn 1024 1485 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1485)) (2 * 1485)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1486 : zz_in_Pn 1024 1486 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1486)) (2 * 1486)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1487 : zz_in_Pn 1024 1487 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1487)) (2 * 1487)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1488 : zz_in_Pn 1024 1488 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1488)) (2 * 1488)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1489 : zz_in_Pn 1024 1489 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1489)) (2 * 1489)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1490 : zz_in_Pn 1024 1490 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1490)) (2 * 1490)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1491 : zz_in_Pn 1024 1491 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1491)) (2 * 1491)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1492 : zz_in_Pn 1024 1492 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1492)) (2 * 1492)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1493 : zz_in_Pn 1024 1493 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1493)) (2 * 1493)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1494 : zz_in_Pn 1024 1494 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1494)) (2 * 1494)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1495 : zz_in_Pn 1024 1495 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1495)) (2 * 1495)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1496 : zz_in_Pn 1024 1496 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1496)) (2 * 1496)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1497 : zz_in_Pn 1024 1497 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1497)) (2 * 1497)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1498 : zz_in_Pn 1024 1498 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1498)) (2 * 1498)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1499 : zz_in_Pn 1024 1499 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1499)) (2 * 1499)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1500 : zz_in_Pn 1024 1500 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1500)) (2 * 1500)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1501 : zz_in_Pn 1024 1501 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1501)) (2 * 1501)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1502 : zz_in_Pn 1024 1502 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1502)) (2 * 1502)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1503 : zz_in_Pn 1024 1503 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1503)) (2 * 1503)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1504 : zz_in_Pn 1024 1504 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1504)) (2 * 1504)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1505 : zz_in_Pn 1024 1505 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1505)) (2 * 1505)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1506 : zz_in_Pn 1024 1506 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1506)) (2 * 1506)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1507 : zz_in_Pn 1024 1507 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1507)) (2 * 1507)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1508 : zz_in_Pn 1024 1508 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1508)) (2 * 1508)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1509 : zz_in_Pn 1024 1509 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1509)) (2 * 1509)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1510 : zz_in_Pn 1024 1510 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1510)) (2 * 1510)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1511 : zz_in_Pn 1024 1511 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1511)) (2 * 1511)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1512 : zz_in_Pn 1024 1512 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1512)) (2 * 1512)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1513 : zz_in_Pn 1024 1513 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1513)) (2 * 1513)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1514 : zz_in_Pn 1024 1514 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1514)) (2 * 1514)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1515 : zz_in_Pn 1024 1515 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1515)) (2 * 1515)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1516 : zz_in_Pn 1024 1516 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1516)) (2 * 1516)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1517 : zz_in_Pn 1024 1517 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1517)) (2 * 1517)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1518 : zz_in_Pn 1024 1518 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1518)) (2 * 1518)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1519 : zz_in_Pn 1024 1519 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1519)) (2 * 1519)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1520 : zz_in_Pn 1024 1520 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1520)) (2 * 1520)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1521 : zz_in_Pn 1024 1521 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1521)) (2 * 1521)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1522 : zz_in_Pn 1024 1522 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1522)) (2 * 1522)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1523 : zz_in_Pn 1024 1523 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1523)) (2 * 1523)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1524 : zz_in_Pn 1024 1524 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1524)) (2 * 1524)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1525 : zz_in_Pn 1024 1525 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1525)) (2 * 1525)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1526 : zz_in_Pn 1024 1526 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1526)) (2 * 1526)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1527 : zz_in_Pn 1024 1527 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1527)) (2 * 1527)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1528 : zz_in_Pn 1024 1528 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1528)) (2 * 1528)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1529 : zz_in_Pn 1024 1529 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1529)) (2 * 1529)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1530 : zz_in_Pn 1024 1530 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1530)) (2 * 1530)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1531 : zz_in_Pn 1024 1531 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1531)) (2 * 1531)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1532 : zz_in_Pn 1024 1532 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1532)) (2 * 1532)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1533 : zz_in_Pn 1024 1533 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1533)) (2 * 1533)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1534 : zz_in_Pn 1024 1534 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1534)) (2 * 1534)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1535 : zz_in_Pn 1024 1535 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1535)) (2 * 1535)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

Lemma piu_zz_inPn_1024_1536 : zz_in_Pn 1024 1536 = false.
Proof.
  unfold zz_in_Pn.
  replace (Nat.ltb (3 * (1024 mod 1536)) (2 * 1536)) with false by (vm_compute; reflexivity).
  repeat (rewrite andb_false_l || rewrite andb_false_r).
  reflexivity.
Qed.

