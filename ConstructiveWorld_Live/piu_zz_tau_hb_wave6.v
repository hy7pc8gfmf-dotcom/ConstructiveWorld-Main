(* piu_zz_tau_hb_wave6.v — KB11 Hb 升格候选子片 6/8（1024 段 Hb48-Hb63·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave6.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L2027-L2047 (assert Hb48) *)
Lemma piu_zz_hb_1024_48 : piu_zz_zprod_seg 1024%nat (512%nat + 752%nat) 16%nat = ((if zz_in_Pn 1024 1265%nat then Z.of_nat 1265%nat else 1%Z) * ((if zz_in_Pn 1024 1266%nat then Z.of_nat 1266%nat else 1%Z) * ((if zz_in_Pn 1024 1267%nat then Z.of_nat 1267%nat else 1%Z) * ((if zz_in_Pn 1024 1268%nat then Z.of_nat 1268%nat else 1%Z) * ((if zz_in_Pn 1024 1269%nat then Z.of_nat 1269%nat else 1%Z) * ((if zz_in_Pn 1024 1270%nat then Z.of_nat 1270%nat else 1%Z) * ((if zz_in_Pn 1024 1271%nat then Z.of_nat 1271%nat else 1%Z) * ((if zz_in_Pn 1024 1272%nat then Z.of_nat 1272%nat else 1%Z) * ((if zz_in_Pn 1024 1273%nat then Z.of_nat 1273%nat else 1%Z) * ((if zz_in_Pn 1024 1274%nat then Z.of_nat 1274%nat else 1%Z) * ((if zz_in_Pn 1024 1275%nat then Z.of_nat 1275%nat else 1%Z) * ((if zz_in_Pn 1024 1276%nat then Z.of_nat 1276%nat else 1%Z) * ((if zz_in_Pn 1024 1277%nat then Z.of_nat 1277%nat else 1%Z) * ((if zz_in_Pn 1024 1278%nat then Z.of_nat 1278%nat else 1%Z) * ((if zz_in_Pn 1024 1279%nat then Z.of_nat 1279%nat else 1%Z) * (if zz_in_Pn 1024 1280%nat then Z.of_nat 1280%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1280.
    rewrite piu_zz_inPn_1024_1279.
    rewrite piu_zz_inPn_1024_1278.
    rewrite piu_zz_inPn_1024_1277.
    rewrite piu_zz_inPn_1024_1276.
    rewrite piu_zz_inPn_1024_1275.
    rewrite piu_zz_inPn_1024_1274.
    rewrite piu_zz_inPn_1024_1273.
    rewrite piu_zz_inPn_1024_1272.
    rewrite piu_zz_inPn_1024_1271.
    rewrite piu_zz_inPn_1024_1270.
    rewrite piu_zz_inPn_1024_1269.
    rewrite piu_zz_inPn_1024_1268.
    rewrite piu_zz_inPn_1024_1267.
    rewrite piu_zz_inPn_1024_1266.
    rewrite piu_zz_inPn_1024_1265.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2048-L2068 (assert Hb49) *)
Lemma piu_zz_hb_1024_49 : piu_zz_zprod_seg 1024%nat (512%nat + 736%nat) 16%nat = ((if zz_in_Pn 1024 1249%nat then Z.of_nat 1249%nat else 1%Z) * ((if zz_in_Pn 1024 1250%nat then Z.of_nat 1250%nat else 1%Z) * ((if zz_in_Pn 1024 1251%nat then Z.of_nat 1251%nat else 1%Z) * ((if zz_in_Pn 1024 1252%nat then Z.of_nat 1252%nat else 1%Z) * ((if zz_in_Pn 1024 1253%nat then Z.of_nat 1253%nat else 1%Z) * ((if zz_in_Pn 1024 1254%nat then Z.of_nat 1254%nat else 1%Z) * ((if zz_in_Pn 1024 1255%nat then Z.of_nat 1255%nat else 1%Z) * ((if zz_in_Pn 1024 1256%nat then Z.of_nat 1256%nat else 1%Z) * ((if zz_in_Pn 1024 1257%nat then Z.of_nat 1257%nat else 1%Z) * ((if zz_in_Pn 1024 1258%nat then Z.of_nat 1258%nat else 1%Z) * ((if zz_in_Pn 1024 1259%nat then Z.of_nat 1259%nat else 1%Z) * ((if zz_in_Pn 1024 1260%nat then Z.of_nat 1260%nat else 1%Z) * ((if zz_in_Pn 1024 1261%nat then Z.of_nat 1261%nat else 1%Z) * ((if zz_in_Pn 1024 1262%nat then Z.of_nat 1262%nat else 1%Z) * ((if zz_in_Pn 1024 1263%nat then Z.of_nat 1263%nat else 1%Z) * (if zz_in_Pn 1024 1264%nat then Z.of_nat 1264%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1264.
    rewrite piu_zz_inPn_1024_1263.
    rewrite piu_zz_inPn_1024_1262.
    rewrite piu_zz_inPn_1024_1261.
    rewrite piu_zz_inPn_1024_1260.
    rewrite piu_zz_inPn_1024_1259.
    rewrite piu_zz_inPn_1024_1258.
    rewrite piu_zz_inPn_1024_1257.
    rewrite piu_zz_inPn_1024_1256.
    rewrite piu_zz_inPn_1024_1255.
    rewrite piu_zz_inPn_1024_1254.
    rewrite piu_zz_inPn_1024_1253.
    rewrite piu_zz_inPn_1024_1252.
    rewrite piu_zz_inPn_1024_1251.
    rewrite piu_zz_inPn_1024_1250.
    rewrite piu_zz_inPn_1024_1249.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2069-L2089 (assert Hb50) *)
Lemma piu_zz_hb_1024_50 : piu_zz_zprod_seg 1024%nat (512%nat + 720%nat) 16%nat = ((if zz_in_Pn 1024 1233%nat then Z.of_nat 1233%nat else 1%Z) * ((if zz_in_Pn 1024 1234%nat then Z.of_nat 1234%nat else 1%Z) * ((if zz_in_Pn 1024 1235%nat then Z.of_nat 1235%nat else 1%Z) * ((if zz_in_Pn 1024 1236%nat then Z.of_nat 1236%nat else 1%Z) * ((if zz_in_Pn 1024 1237%nat then Z.of_nat 1237%nat else 1%Z) * ((if zz_in_Pn 1024 1238%nat then Z.of_nat 1238%nat else 1%Z) * ((if zz_in_Pn 1024 1239%nat then Z.of_nat 1239%nat else 1%Z) * ((if zz_in_Pn 1024 1240%nat then Z.of_nat 1240%nat else 1%Z) * ((if zz_in_Pn 1024 1241%nat then Z.of_nat 1241%nat else 1%Z) * ((if zz_in_Pn 1024 1242%nat then Z.of_nat 1242%nat else 1%Z) * ((if zz_in_Pn 1024 1243%nat then Z.of_nat 1243%nat else 1%Z) * ((if zz_in_Pn 1024 1244%nat then Z.of_nat 1244%nat else 1%Z) * ((if zz_in_Pn 1024 1245%nat then Z.of_nat 1245%nat else 1%Z) * ((if zz_in_Pn 1024 1246%nat then Z.of_nat 1246%nat else 1%Z) * ((if zz_in_Pn 1024 1247%nat then Z.of_nat 1247%nat else 1%Z) * (if zz_in_Pn 1024 1248%nat then Z.of_nat 1248%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1248.
    rewrite piu_zz_inPn_1024_1247.
    rewrite piu_zz_inPn_1024_1246.
    rewrite piu_zz_inPn_1024_1245.
    rewrite piu_zz_inPn_1024_1244.
    rewrite piu_zz_inPn_1024_1243.
    rewrite piu_zz_inPn_1024_1242.
    rewrite piu_zz_inPn_1024_1241.
    rewrite piu_zz_inPn_1024_1240.
    rewrite piu_zz_inPn_1024_1239.
    rewrite piu_zz_inPn_1024_1238.
    rewrite piu_zz_inPn_1024_1237.
    rewrite piu_zz_inPn_1024_1236.
    rewrite piu_zz_inPn_1024_1235.
    rewrite piu_zz_inPn_1024_1234.
    rewrite piu_zz_inPn_1024_1233.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2090-L2110 (assert Hb51) *)
Lemma piu_zz_hb_1024_51 : piu_zz_zprod_seg 1024%nat (512%nat + 704%nat) 16%nat = ((if zz_in_Pn 1024 1217%nat then Z.of_nat 1217%nat else 1%Z) * ((if zz_in_Pn 1024 1218%nat then Z.of_nat 1218%nat else 1%Z) * ((if zz_in_Pn 1024 1219%nat then Z.of_nat 1219%nat else 1%Z) * ((if zz_in_Pn 1024 1220%nat then Z.of_nat 1220%nat else 1%Z) * ((if zz_in_Pn 1024 1221%nat then Z.of_nat 1221%nat else 1%Z) * ((if zz_in_Pn 1024 1222%nat then Z.of_nat 1222%nat else 1%Z) * ((if zz_in_Pn 1024 1223%nat then Z.of_nat 1223%nat else 1%Z) * ((if zz_in_Pn 1024 1224%nat then Z.of_nat 1224%nat else 1%Z) * ((if zz_in_Pn 1024 1225%nat then Z.of_nat 1225%nat else 1%Z) * ((if zz_in_Pn 1024 1226%nat then Z.of_nat 1226%nat else 1%Z) * ((if zz_in_Pn 1024 1227%nat then Z.of_nat 1227%nat else 1%Z) * ((if zz_in_Pn 1024 1228%nat then Z.of_nat 1228%nat else 1%Z) * ((if zz_in_Pn 1024 1229%nat then Z.of_nat 1229%nat else 1%Z) * ((if zz_in_Pn 1024 1230%nat then Z.of_nat 1230%nat else 1%Z) * ((if zz_in_Pn 1024 1231%nat then Z.of_nat 1231%nat else 1%Z) * (if zz_in_Pn 1024 1232%nat then Z.of_nat 1232%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1232.
    rewrite piu_zz_inPn_1024_1231.
    rewrite piu_zz_inPn_1024_1230.
    rewrite piu_zz_inPn_1024_1229.
    rewrite piu_zz_inPn_1024_1228.
    rewrite piu_zz_inPn_1024_1227.
    rewrite piu_zz_inPn_1024_1226.
    rewrite piu_zz_inPn_1024_1225.
    rewrite piu_zz_inPn_1024_1224.
    rewrite piu_zz_inPn_1024_1223.
    rewrite piu_zz_inPn_1024_1222.
    rewrite piu_zz_inPn_1024_1221.
    rewrite piu_zz_inPn_1024_1220.
    rewrite piu_zz_inPn_1024_1219.
    rewrite piu_zz_inPn_1024_1218.
    rewrite piu_zz_inPn_1024_1217.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2111-L2131 (assert Hb52) *)
Lemma piu_zz_hb_1024_52 : piu_zz_zprod_seg 1024%nat (512%nat + 688%nat) 16%nat = ((if zz_in_Pn 1024 1201%nat then Z.of_nat 1201%nat else 1%Z) * ((if zz_in_Pn 1024 1202%nat then Z.of_nat 1202%nat else 1%Z) * ((if zz_in_Pn 1024 1203%nat then Z.of_nat 1203%nat else 1%Z) * ((if zz_in_Pn 1024 1204%nat then Z.of_nat 1204%nat else 1%Z) * ((if zz_in_Pn 1024 1205%nat then Z.of_nat 1205%nat else 1%Z) * ((if zz_in_Pn 1024 1206%nat then Z.of_nat 1206%nat else 1%Z) * ((if zz_in_Pn 1024 1207%nat then Z.of_nat 1207%nat else 1%Z) * ((if zz_in_Pn 1024 1208%nat then Z.of_nat 1208%nat else 1%Z) * ((if zz_in_Pn 1024 1209%nat then Z.of_nat 1209%nat else 1%Z) * ((if zz_in_Pn 1024 1210%nat then Z.of_nat 1210%nat else 1%Z) * ((if zz_in_Pn 1024 1211%nat then Z.of_nat 1211%nat else 1%Z) * ((if zz_in_Pn 1024 1212%nat then Z.of_nat 1212%nat else 1%Z) * ((if zz_in_Pn 1024 1213%nat then Z.of_nat 1213%nat else 1%Z) * ((if zz_in_Pn 1024 1214%nat then Z.of_nat 1214%nat else 1%Z) * ((if zz_in_Pn 1024 1215%nat then Z.of_nat 1215%nat else 1%Z) * (if zz_in_Pn 1024 1216%nat then Z.of_nat 1216%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1216.
    rewrite piu_zz_inPn_1024_1215.
    rewrite piu_zz_inPn_1024_1214.
    rewrite piu_zz_inPn_1024_1213.
    rewrite piu_zz_inPn_1024_1212.
    rewrite piu_zz_inPn_1024_1211.
    rewrite piu_zz_inPn_1024_1210.
    rewrite piu_zz_inPn_1024_1209.
    rewrite piu_zz_inPn_1024_1208.
    rewrite piu_zz_inPn_1024_1207.
    rewrite piu_zz_inPn_1024_1206.
    rewrite piu_zz_inPn_1024_1205.
    rewrite piu_zz_inPn_1024_1204.
    rewrite piu_zz_inPn_1024_1203.
    rewrite piu_zz_inPn_1024_1202.
    rewrite piu_zz_inPn_1024_1201.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2132-L2152 (assert Hb53) *)
Lemma piu_zz_hb_1024_53 : piu_zz_zprod_seg 1024%nat (512%nat + 672%nat) 16%nat = ((if zz_in_Pn 1024 1185%nat then Z.of_nat 1185%nat else 1%Z) * ((if zz_in_Pn 1024 1186%nat then Z.of_nat 1186%nat else 1%Z) * ((if zz_in_Pn 1024 1187%nat then Z.of_nat 1187%nat else 1%Z) * ((if zz_in_Pn 1024 1188%nat then Z.of_nat 1188%nat else 1%Z) * ((if zz_in_Pn 1024 1189%nat then Z.of_nat 1189%nat else 1%Z) * ((if zz_in_Pn 1024 1190%nat then Z.of_nat 1190%nat else 1%Z) * ((if zz_in_Pn 1024 1191%nat then Z.of_nat 1191%nat else 1%Z) * ((if zz_in_Pn 1024 1192%nat then Z.of_nat 1192%nat else 1%Z) * ((if zz_in_Pn 1024 1193%nat then Z.of_nat 1193%nat else 1%Z) * ((if zz_in_Pn 1024 1194%nat then Z.of_nat 1194%nat else 1%Z) * ((if zz_in_Pn 1024 1195%nat then Z.of_nat 1195%nat else 1%Z) * ((if zz_in_Pn 1024 1196%nat then Z.of_nat 1196%nat else 1%Z) * ((if zz_in_Pn 1024 1197%nat then Z.of_nat 1197%nat else 1%Z) * ((if zz_in_Pn 1024 1198%nat then Z.of_nat 1198%nat else 1%Z) * ((if zz_in_Pn 1024 1199%nat then Z.of_nat 1199%nat else 1%Z) * (if zz_in_Pn 1024 1200%nat then Z.of_nat 1200%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1200.
    rewrite piu_zz_inPn_1024_1199.
    rewrite piu_zz_inPn_1024_1198.
    rewrite piu_zz_inPn_1024_1197.
    rewrite piu_zz_inPn_1024_1196.
    rewrite piu_zz_inPn_1024_1195.
    rewrite piu_zz_inPn_1024_1194.
    rewrite piu_zz_inPn_1024_1193.
    rewrite piu_zz_inPn_1024_1192.
    rewrite piu_zz_inPn_1024_1191.
    rewrite piu_zz_inPn_1024_1190.
    rewrite piu_zz_inPn_1024_1189.
    rewrite piu_zz_inPn_1024_1188.
    rewrite piu_zz_inPn_1024_1187.
    rewrite piu_zz_inPn_1024_1186.
    rewrite piu_zz_inPn_1024_1185.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2153-L2173 (assert Hb54) *)
Lemma piu_zz_hb_1024_54 : piu_zz_zprod_seg 1024%nat (512%nat + 656%nat) 16%nat = ((if zz_in_Pn 1024 1169%nat then Z.of_nat 1169%nat else 1%Z) * ((if zz_in_Pn 1024 1170%nat then Z.of_nat 1170%nat else 1%Z) * ((if zz_in_Pn 1024 1171%nat then Z.of_nat 1171%nat else 1%Z) * ((if zz_in_Pn 1024 1172%nat then Z.of_nat 1172%nat else 1%Z) * ((if zz_in_Pn 1024 1173%nat then Z.of_nat 1173%nat else 1%Z) * ((if zz_in_Pn 1024 1174%nat then Z.of_nat 1174%nat else 1%Z) * ((if zz_in_Pn 1024 1175%nat then Z.of_nat 1175%nat else 1%Z) * ((if zz_in_Pn 1024 1176%nat then Z.of_nat 1176%nat else 1%Z) * ((if zz_in_Pn 1024 1177%nat then Z.of_nat 1177%nat else 1%Z) * ((if zz_in_Pn 1024 1178%nat then Z.of_nat 1178%nat else 1%Z) * ((if zz_in_Pn 1024 1179%nat then Z.of_nat 1179%nat else 1%Z) * ((if zz_in_Pn 1024 1180%nat then Z.of_nat 1180%nat else 1%Z) * ((if zz_in_Pn 1024 1181%nat then Z.of_nat 1181%nat else 1%Z) * ((if zz_in_Pn 1024 1182%nat then Z.of_nat 1182%nat else 1%Z) * ((if zz_in_Pn 1024 1183%nat then Z.of_nat 1183%nat else 1%Z) * (if zz_in_Pn 1024 1184%nat then Z.of_nat 1184%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1184.
    rewrite piu_zz_inPn_1024_1183.
    rewrite piu_zz_inPn_1024_1182.
    rewrite piu_zz_inPn_1024_1181.
    rewrite piu_zz_inPn_1024_1180.
    rewrite piu_zz_inPn_1024_1179.
    rewrite piu_zz_inPn_1024_1178.
    rewrite piu_zz_inPn_1024_1177.
    rewrite piu_zz_inPn_1024_1176.
    rewrite piu_zz_inPn_1024_1175.
    rewrite piu_zz_inPn_1024_1174.
    rewrite piu_zz_inPn_1024_1173.
    rewrite piu_zz_inPn_1024_1172.
    rewrite piu_zz_inPn_1024_1171.
    rewrite piu_zz_inPn_1024_1170.
    rewrite piu_zz_inPn_1024_1169.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2174-L2194 (assert Hb55) *)
Lemma piu_zz_hb_1024_55 : piu_zz_zprod_seg 1024%nat (512%nat + 640%nat) 16%nat = ((if zz_in_Pn 1024 1153%nat then Z.of_nat 1153%nat else 1%Z) * ((if zz_in_Pn 1024 1154%nat then Z.of_nat 1154%nat else 1%Z) * ((if zz_in_Pn 1024 1155%nat then Z.of_nat 1155%nat else 1%Z) * ((if zz_in_Pn 1024 1156%nat then Z.of_nat 1156%nat else 1%Z) * ((if zz_in_Pn 1024 1157%nat then Z.of_nat 1157%nat else 1%Z) * ((if zz_in_Pn 1024 1158%nat then Z.of_nat 1158%nat else 1%Z) * ((if zz_in_Pn 1024 1159%nat then Z.of_nat 1159%nat else 1%Z) * ((if zz_in_Pn 1024 1160%nat then Z.of_nat 1160%nat else 1%Z) * ((if zz_in_Pn 1024 1161%nat then Z.of_nat 1161%nat else 1%Z) * ((if zz_in_Pn 1024 1162%nat then Z.of_nat 1162%nat else 1%Z) * ((if zz_in_Pn 1024 1163%nat then Z.of_nat 1163%nat else 1%Z) * ((if zz_in_Pn 1024 1164%nat then Z.of_nat 1164%nat else 1%Z) * ((if zz_in_Pn 1024 1165%nat then Z.of_nat 1165%nat else 1%Z) * ((if zz_in_Pn 1024 1166%nat then Z.of_nat 1166%nat else 1%Z) * ((if zz_in_Pn 1024 1167%nat then Z.of_nat 1167%nat else 1%Z) * (if zz_in_Pn 1024 1168%nat then Z.of_nat 1168%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1168.
    rewrite piu_zz_inPn_1024_1167.
    rewrite piu_zz_inPn_1024_1166.
    rewrite piu_zz_inPn_1024_1165.
    rewrite piu_zz_inPn_1024_1164.
    rewrite piu_zz_inPn_1024_1163.
    rewrite piu_zz_inPn_1024_1162.
    rewrite piu_zz_inPn_1024_1161.
    rewrite piu_zz_inPn_1024_1160.
    rewrite piu_zz_inPn_1024_1159.
    rewrite piu_zz_inPn_1024_1158.
    rewrite piu_zz_inPn_1024_1157.
    rewrite piu_zz_inPn_1024_1156.
    rewrite piu_zz_inPn_1024_1155.
    rewrite piu_zz_inPn_1024_1154.
    rewrite piu_zz_inPn_1024_1153.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2195-L2215 (assert Hb56) *)
Lemma piu_zz_hb_1024_56 : piu_zz_zprod_seg 1024%nat (512%nat + 624%nat) 16%nat = ((if zz_in_Pn 1024 1137%nat then Z.of_nat 1137%nat else 1%Z) * ((if zz_in_Pn 1024 1138%nat then Z.of_nat 1138%nat else 1%Z) * ((if zz_in_Pn 1024 1139%nat then Z.of_nat 1139%nat else 1%Z) * ((if zz_in_Pn 1024 1140%nat then Z.of_nat 1140%nat else 1%Z) * ((if zz_in_Pn 1024 1141%nat then Z.of_nat 1141%nat else 1%Z) * ((if zz_in_Pn 1024 1142%nat then Z.of_nat 1142%nat else 1%Z) * ((if zz_in_Pn 1024 1143%nat then Z.of_nat 1143%nat else 1%Z) * ((if zz_in_Pn 1024 1144%nat then Z.of_nat 1144%nat else 1%Z) * ((if zz_in_Pn 1024 1145%nat then Z.of_nat 1145%nat else 1%Z) * ((if zz_in_Pn 1024 1146%nat then Z.of_nat 1146%nat else 1%Z) * ((if zz_in_Pn 1024 1147%nat then Z.of_nat 1147%nat else 1%Z) * ((if zz_in_Pn 1024 1148%nat then Z.of_nat 1148%nat else 1%Z) * ((if zz_in_Pn 1024 1149%nat then Z.of_nat 1149%nat else 1%Z) * ((if zz_in_Pn 1024 1150%nat then Z.of_nat 1150%nat else 1%Z) * ((if zz_in_Pn 1024 1151%nat then Z.of_nat 1151%nat else 1%Z) * (if zz_in_Pn 1024 1152%nat then Z.of_nat 1152%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1152.
    rewrite piu_zz_inPn_1024_1151.
    rewrite piu_zz_inPn_1024_1150.
    rewrite piu_zz_inPn_1024_1149.
    rewrite piu_zz_inPn_1024_1148.
    rewrite piu_zz_inPn_1024_1147.
    rewrite piu_zz_inPn_1024_1146.
    rewrite piu_zz_inPn_1024_1145.
    rewrite piu_zz_inPn_1024_1144.
    rewrite piu_zz_inPn_1024_1143.
    rewrite piu_zz_inPn_1024_1142.
    rewrite piu_zz_inPn_1024_1141.
    rewrite piu_zz_inPn_1024_1140.
    rewrite piu_zz_inPn_1024_1139.
    rewrite piu_zz_inPn_1024_1138.
    rewrite piu_zz_inPn_1024_1137.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2216-L2236 (assert Hb57) *)
Lemma piu_zz_hb_1024_57 : piu_zz_zprod_seg 1024%nat (512%nat + 608%nat) 16%nat = ((if zz_in_Pn 1024 1121%nat then Z.of_nat 1121%nat else 1%Z) * ((if zz_in_Pn 1024 1122%nat then Z.of_nat 1122%nat else 1%Z) * ((if zz_in_Pn 1024 1123%nat then Z.of_nat 1123%nat else 1%Z) * ((if zz_in_Pn 1024 1124%nat then Z.of_nat 1124%nat else 1%Z) * ((if zz_in_Pn 1024 1125%nat then Z.of_nat 1125%nat else 1%Z) * ((if zz_in_Pn 1024 1126%nat then Z.of_nat 1126%nat else 1%Z) * ((if zz_in_Pn 1024 1127%nat then Z.of_nat 1127%nat else 1%Z) * ((if zz_in_Pn 1024 1128%nat then Z.of_nat 1128%nat else 1%Z) * ((if zz_in_Pn 1024 1129%nat then Z.of_nat 1129%nat else 1%Z) * ((if zz_in_Pn 1024 1130%nat then Z.of_nat 1130%nat else 1%Z) * ((if zz_in_Pn 1024 1131%nat then Z.of_nat 1131%nat else 1%Z) * ((if zz_in_Pn 1024 1132%nat then Z.of_nat 1132%nat else 1%Z) * ((if zz_in_Pn 1024 1133%nat then Z.of_nat 1133%nat else 1%Z) * ((if zz_in_Pn 1024 1134%nat then Z.of_nat 1134%nat else 1%Z) * ((if zz_in_Pn 1024 1135%nat then Z.of_nat 1135%nat else 1%Z) * (if zz_in_Pn 1024 1136%nat then Z.of_nat 1136%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1136.
    rewrite piu_zz_inPn_1024_1135.
    rewrite piu_zz_inPn_1024_1134.
    rewrite piu_zz_inPn_1024_1133.
    rewrite piu_zz_inPn_1024_1132.
    rewrite piu_zz_inPn_1024_1131.
    rewrite piu_zz_inPn_1024_1130.
    rewrite piu_zz_inPn_1024_1129.
    rewrite piu_zz_inPn_1024_1128.
    rewrite piu_zz_inPn_1024_1127.
    rewrite piu_zz_inPn_1024_1126.
    rewrite piu_zz_inPn_1024_1125.
    rewrite piu_zz_inPn_1024_1124.
    rewrite piu_zz_inPn_1024_1123.
    rewrite piu_zz_inPn_1024_1122.
    rewrite piu_zz_inPn_1024_1121.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2237-L2257 (assert Hb58) *)
Lemma piu_zz_hb_1024_58 : piu_zz_zprod_seg 1024%nat (512%nat + 592%nat) 16%nat = ((if zz_in_Pn 1024 1105%nat then Z.of_nat 1105%nat else 1%Z) * ((if zz_in_Pn 1024 1106%nat then Z.of_nat 1106%nat else 1%Z) * ((if zz_in_Pn 1024 1107%nat then Z.of_nat 1107%nat else 1%Z) * ((if zz_in_Pn 1024 1108%nat then Z.of_nat 1108%nat else 1%Z) * ((if zz_in_Pn 1024 1109%nat then Z.of_nat 1109%nat else 1%Z) * ((if zz_in_Pn 1024 1110%nat then Z.of_nat 1110%nat else 1%Z) * ((if zz_in_Pn 1024 1111%nat then Z.of_nat 1111%nat else 1%Z) * ((if zz_in_Pn 1024 1112%nat then Z.of_nat 1112%nat else 1%Z) * ((if zz_in_Pn 1024 1113%nat then Z.of_nat 1113%nat else 1%Z) * ((if zz_in_Pn 1024 1114%nat then Z.of_nat 1114%nat else 1%Z) * ((if zz_in_Pn 1024 1115%nat then Z.of_nat 1115%nat else 1%Z) * ((if zz_in_Pn 1024 1116%nat then Z.of_nat 1116%nat else 1%Z) * ((if zz_in_Pn 1024 1117%nat then Z.of_nat 1117%nat else 1%Z) * ((if zz_in_Pn 1024 1118%nat then Z.of_nat 1118%nat else 1%Z) * ((if zz_in_Pn 1024 1119%nat then Z.of_nat 1119%nat else 1%Z) * (if zz_in_Pn 1024 1120%nat then Z.of_nat 1120%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1120.
    rewrite piu_zz_inPn_1024_1119.
    rewrite piu_zz_inPn_1024_1118.
    rewrite piu_zz_inPn_1024_1117.
    rewrite piu_zz_inPn_1024_1116.
    rewrite piu_zz_inPn_1024_1115.
    rewrite piu_zz_inPn_1024_1114.
    rewrite piu_zz_inPn_1024_1113.
    rewrite piu_zz_inPn_1024_1112.
    rewrite piu_zz_inPn_1024_1111.
    rewrite piu_zz_inPn_1024_1110.
    rewrite piu_zz_inPn_1024_1109.
    rewrite piu_zz_inPn_1024_1108.
    rewrite piu_zz_inPn_1024_1107.
    rewrite piu_zz_inPn_1024_1106.
    rewrite piu_zz_inPn_1024_1105.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2258-L2278 (assert Hb59) *)
Lemma piu_zz_hb_1024_59 : piu_zz_zprod_seg 1024%nat (512%nat + 576%nat) 16%nat = ((if zz_in_Pn 1024 1089%nat then Z.of_nat 1089%nat else 1%Z) * ((if zz_in_Pn 1024 1090%nat then Z.of_nat 1090%nat else 1%Z) * ((if zz_in_Pn 1024 1091%nat then Z.of_nat 1091%nat else 1%Z) * ((if zz_in_Pn 1024 1092%nat then Z.of_nat 1092%nat else 1%Z) * ((if zz_in_Pn 1024 1093%nat then Z.of_nat 1093%nat else 1%Z) * ((if zz_in_Pn 1024 1094%nat then Z.of_nat 1094%nat else 1%Z) * ((if zz_in_Pn 1024 1095%nat then Z.of_nat 1095%nat else 1%Z) * ((if zz_in_Pn 1024 1096%nat then Z.of_nat 1096%nat else 1%Z) * ((if zz_in_Pn 1024 1097%nat then Z.of_nat 1097%nat else 1%Z) * ((if zz_in_Pn 1024 1098%nat then Z.of_nat 1098%nat else 1%Z) * ((if zz_in_Pn 1024 1099%nat then Z.of_nat 1099%nat else 1%Z) * ((if zz_in_Pn 1024 1100%nat then Z.of_nat 1100%nat else 1%Z) * ((if zz_in_Pn 1024 1101%nat then Z.of_nat 1101%nat else 1%Z) * ((if zz_in_Pn 1024 1102%nat then Z.of_nat 1102%nat else 1%Z) * ((if zz_in_Pn 1024 1103%nat then Z.of_nat 1103%nat else 1%Z) * (if zz_in_Pn 1024 1104%nat then Z.of_nat 1104%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1104.
    rewrite piu_zz_inPn_1024_1103.
    rewrite piu_zz_inPn_1024_1102.
    rewrite piu_zz_inPn_1024_1101.
    rewrite piu_zz_inPn_1024_1100.
    rewrite piu_zz_inPn_1024_1099.
    rewrite piu_zz_inPn_1024_1098.
    rewrite piu_zz_inPn_1024_1097.
    rewrite piu_zz_inPn_1024_1096.
    rewrite piu_zz_inPn_1024_1095.
    rewrite piu_zz_inPn_1024_1094.
    rewrite piu_zz_inPn_1024_1093.
    rewrite piu_zz_inPn_1024_1092.
    rewrite piu_zz_inPn_1024_1091.
    rewrite piu_zz_inPn_1024_1090.
    rewrite piu_zz_inPn_1024_1089.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2279-L2299 (assert Hb60) *)
Lemma piu_zz_hb_1024_60 : piu_zz_zprod_seg 1024%nat (512%nat + 560%nat) 16%nat = ((if zz_in_Pn 1024 1073%nat then Z.of_nat 1073%nat else 1%Z) * ((if zz_in_Pn 1024 1074%nat then Z.of_nat 1074%nat else 1%Z) * ((if zz_in_Pn 1024 1075%nat then Z.of_nat 1075%nat else 1%Z) * ((if zz_in_Pn 1024 1076%nat then Z.of_nat 1076%nat else 1%Z) * ((if zz_in_Pn 1024 1077%nat then Z.of_nat 1077%nat else 1%Z) * ((if zz_in_Pn 1024 1078%nat then Z.of_nat 1078%nat else 1%Z) * ((if zz_in_Pn 1024 1079%nat then Z.of_nat 1079%nat else 1%Z) * ((if zz_in_Pn 1024 1080%nat then Z.of_nat 1080%nat else 1%Z) * ((if zz_in_Pn 1024 1081%nat then Z.of_nat 1081%nat else 1%Z) * ((if zz_in_Pn 1024 1082%nat then Z.of_nat 1082%nat else 1%Z) * ((if zz_in_Pn 1024 1083%nat then Z.of_nat 1083%nat else 1%Z) * ((if zz_in_Pn 1024 1084%nat then Z.of_nat 1084%nat else 1%Z) * ((if zz_in_Pn 1024 1085%nat then Z.of_nat 1085%nat else 1%Z) * ((if zz_in_Pn 1024 1086%nat then Z.of_nat 1086%nat else 1%Z) * ((if zz_in_Pn 1024 1087%nat then Z.of_nat 1087%nat else 1%Z) * (if zz_in_Pn 1024 1088%nat then Z.of_nat 1088%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1088.
    rewrite piu_zz_inPn_1024_1087.
    rewrite piu_zz_inPn_1024_1086.
    rewrite piu_zz_inPn_1024_1085.
    rewrite piu_zz_inPn_1024_1084.
    rewrite piu_zz_inPn_1024_1083.
    rewrite piu_zz_inPn_1024_1082.
    rewrite piu_zz_inPn_1024_1081.
    rewrite piu_zz_inPn_1024_1080.
    rewrite piu_zz_inPn_1024_1079.
    rewrite piu_zz_inPn_1024_1078.
    rewrite piu_zz_inPn_1024_1077.
    rewrite piu_zz_inPn_1024_1076.
    rewrite piu_zz_inPn_1024_1075.
    rewrite piu_zz_inPn_1024_1074.
    rewrite piu_zz_inPn_1024_1073.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2300-L2320 (assert Hb61) *)
Lemma piu_zz_hb_1024_61 : piu_zz_zprod_seg 1024%nat (512%nat + 544%nat) 16%nat = ((if zz_in_Pn 1024 1057%nat then Z.of_nat 1057%nat else 1%Z) * ((if zz_in_Pn 1024 1058%nat then Z.of_nat 1058%nat else 1%Z) * ((if zz_in_Pn 1024 1059%nat then Z.of_nat 1059%nat else 1%Z) * ((if zz_in_Pn 1024 1060%nat then Z.of_nat 1060%nat else 1%Z) * ((if zz_in_Pn 1024 1061%nat then Z.of_nat 1061%nat else 1%Z) * ((if zz_in_Pn 1024 1062%nat then Z.of_nat 1062%nat else 1%Z) * ((if zz_in_Pn 1024 1063%nat then Z.of_nat 1063%nat else 1%Z) * ((if zz_in_Pn 1024 1064%nat then Z.of_nat 1064%nat else 1%Z) * ((if zz_in_Pn 1024 1065%nat then Z.of_nat 1065%nat else 1%Z) * ((if zz_in_Pn 1024 1066%nat then Z.of_nat 1066%nat else 1%Z) * ((if zz_in_Pn 1024 1067%nat then Z.of_nat 1067%nat else 1%Z) * ((if zz_in_Pn 1024 1068%nat then Z.of_nat 1068%nat else 1%Z) * ((if zz_in_Pn 1024 1069%nat then Z.of_nat 1069%nat else 1%Z) * ((if zz_in_Pn 1024 1070%nat then Z.of_nat 1070%nat else 1%Z) * ((if zz_in_Pn 1024 1071%nat then Z.of_nat 1071%nat else 1%Z) * (if zz_in_Pn 1024 1072%nat then Z.of_nat 1072%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1072.
    rewrite piu_zz_inPn_1024_1071.
    rewrite piu_zz_inPn_1024_1070.
    rewrite piu_zz_inPn_1024_1069.
    rewrite piu_zz_inPn_1024_1068.
    rewrite piu_zz_inPn_1024_1067.
    rewrite piu_zz_inPn_1024_1066.
    rewrite piu_zz_inPn_1024_1065.
    rewrite piu_zz_inPn_1024_1064.
    rewrite piu_zz_inPn_1024_1063.
    rewrite piu_zz_inPn_1024_1062.
    rewrite piu_zz_inPn_1024_1061.
    rewrite piu_zz_inPn_1024_1060.
    rewrite piu_zz_inPn_1024_1059.
    rewrite piu_zz_inPn_1024_1058.
    rewrite piu_zz_inPn_1024_1057.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2321-L2341 (assert Hb62) *)
Lemma piu_zz_hb_1024_62 : piu_zz_zprod_seg 1024%nat (512%nat + 528%nat) 16%nat = ((if zz_in_Pn 1024 1041%nat then Z.of_nat 1041%nat else 1%Z) * ((if zz_in_Pn 1024 1042%nat then Z.of_nat 1042%nat else 1%Z) * ((if zz_in_Pn 1024 1043%nat then Z.of_nat 1043%nat else 1%Z) * ((if zz_in_Pn 1024 1044%nat then Z.of_nat 1044%nat else 1%Z) * ((if zz_in_Pn 1024 1045%nat then Z.of_nat 1045%nat else 1%Z) * ((if zz_in_Pn 1024 1046%nat then Z.of_nat 1046%nat else 1%Z) * ((if zz_in_Pn 1024 1047%nat then Z.of_nat 1047%nat else 1%Z) * ((if zz_in_Pn 1024 1048%nat then Z.of_nat 1048%nat else 1%Z) * ((if zz_in_Pn 1024 1049%nat then Z.of_nat 1049%nat else 1%Z) * ((if zz_in_Pn 1024 1050%nat then Z.of_nat 1050%nat else 1%Z) * ((if zz_in_Pn 1024 1051%nat then Z.of_nat 1051%nat else 1%Z) * ((if zz_in_Pn 1024 1052%nat then Z.of_nat 1052%nat else 1%Z) * ((if zz_in_Pn 1024 1053%nat then Z.of_nat 1053%nat else 1%Z) * ((if zz_in_Pn 1024 1054%nat then Z.of_nat 1054%nat else 1%Z) * ((if zz_in_Pn 1024 1055%nat then Z.of_nat 1055%nat else 1%Z) * (if zz_in_Pn 1024 1056%nat then Z.of_nat 1056%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1056.
    rewrite piu_zz_inPn_1024_1055.
    rewrite piu_zz_inPn_1024_1054.
    rewrite piu_zz_inPn_1024_1053.
    rewrite piu_zz_inPn_1024_1052.
    rewrite piu_zz_inPn_1024_1051.
    rewrite piu_zz_inPn_1024_1050.
    rewrite piu_zz_inPn_1024_1049.
    rewrite piu_zz_inPn_1024_1048.
    rewrite piu_zz_inPn_1024_1047.
    rewrite piu_zz_inPn_1024_1046.
    rewrite piu_zz_inPn_1024_1045.
    rewrite piu_zz_inPn_1024_1044.
    rewrite piu_zz_inPn_1024_1043.
    rewrite piu_zz_inPn_1024_1042.
    rewrite piu_zz_inPn_1024_1041.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2342-L2362 (assert Hb63) *)
Lemma piu_zz_hb_1024_63 : piu_zz_zprod_seg 1024%nat (512%nat + 512%nat) 16%nat = ((if zz_in_Pn 1024 1025%nat then Z.of_nat 1025%nat else 1%Z) * ((if zz_in_Pn 1024 1026%nat then Z.of_nat 1026%nat else 1%Z) * ((if zz_in_Pn 1024 1027%nat then Z.of_nat 1027%nat else 1%Z) * ((if zz_in_Pn 1024 1028%nat then Z.of_nat 1028%nat else 1%Z) * ((if zz_in_Pn 1024 1029%nat then Z.of_nat 1029%nat else 1%Z) * ((if zz_in_Pn 1024 1030%nat then Z.of_nat 1030%nat else 1%Z) * ((if zz_in_Pn 1024 1031%nat then Z.of_nat 1031%nat else 1%Z) * ((if zz_in_Pn 1024 1032%nat then Z.of_nat 1032%nat else 1%Z) * ((if zz_in_Pn 1024 1033%nat then Z.of_nat 1033%nat else 1%Z) * ((if zz_in_Pn 1024 1034%nat then Z.of_nat 1034%nat else 1%Z) * ((if zz_in_Pn 1024 1035%nat then Z.of_nat 1035%nat else 1%Z) * ((if zz_in_Pn 1024 1036%nat then Z.of_nat 1036%nat else 1%Z) * ((if zz_in_Pn 1024 1037%nat then Z.of_nat 1037%nat else 1%Z) * ((if zz_in_Pn 1024 1038%nat then Z.of_nat 1038%nat else 1%Z) * ((if zz_in_Pn 1024 1039%nat then Z.of_nat 1039%nat else 1%Z) * (if zz_in_Pn 1024 1040%nat then Z.of_nat 1040%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1040.
    rewrite piu_zz_inPn_1024_1039.
    rewrite piu_zz_inPn_1024_1038.
    rewrite piu_zz_inPn_1024_1037.
    rewrite piu_zz_inPn_1024_1036.
    rewrite piu_zz_inPn_1024_1035.
    rewrite piu_zz_inPn_1024_1034.
    rewrite piu_zz_inPn_1024_1033.
    rewrite piu_zz_inPn_1024_1032.
    rewrite piu_zz_inPn_1024_1031.
    rewrite piu_zz_inPn_1024_1030.
    rewrite piu_zz_inPn_1024_1029.
    rewrite piu_zz_inPn_1024_1028.
    rewrite piu_zz_inPn_1024_1027.
    rewrite piu_zz_inPn_1024_1026.
    rewrite piu_zz_inPn_1024_1025.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
