(* piu_zz_tau_hb_wave5.v — KB11 Hb 升格候选子片 5/8（1024 段 Hb32-Hb47·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave5.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L1691-L1711 (assert Hb32) *)
Lemma piu_zz_hb_1024_32 : piu_zz_zprod_seg 1024%nat (512%nat + 1008%nat) 16%nat = ((if zz_in_Pn 1024 1521%nat then Z.of_nat 1521%nat else 1%Z) * ((if zz_in_Pn 1024 1522%nat then Z.of_nat 1522%nat else 1%Z) * ((if zz_in_Pn 1024 1523%nat then Z.of_nat 1523%nat else 1%Z) * ((if zz_in_Pn 1024 1524%nat then Z.of_nat 1524%nat else 1%Z) * ((if zz_in_Pn 1024 1525%nat then Z.of_nat 1525%nat else 1%Z) * ((if zz_in_Pn 1024 1526%nat then Z.of_nat 1526%nat else 1%Z) * ((if zz_in_Pn 1024 1527%nat then Z.of_nat 1527%nat else 1%Z) * ((if zz_in_Pn 1024 1528%nat then Z.of_nat 1528%nat else 1%Z) * ((if zz_in_Pn 1024 1529%nat then Z.of_nat 1529%nat else 1%Z) * ((if zz_in_Pn 1024 1530%nat then Z.of_nat 1530%nat else 1%Z) * ((if zz_in_Pn 1024 1531%nat then Z.of_nat 1531%nat else 1%Z) * ((if zz_in_Pn 1024 1532%nat then Z.of_nat 1532%nat else 1%Z) * ((if zz_in_Pn 1024 1533%nat then Z.of_nat 1533%nat else 1%Z) * ((if zz_in_Pn 1024 1534%nat then Z.of_nat 1534%nat else 1%Z) * ((if zz_in_Pn 1024 1535%nat then Z.of_nat 1535%nat else 1%Z) * (if zz_in_Pn 1024 1536%nat then Z.of_nat 1536%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1536.
    rewrite piu_zz_inPn_1024_1535.
    rewrite piu_zz_inPn_1024_1534.
    rewrite piu_zz_inPn_1024_1533.
    rewrite piu_zz_inPn_1024_1532.
    rewrite piu_zz_inPn_1024_1531.
    rewrite piu_zz_inPn_1024_1530.
    rewrite piu_zz_inPn_1024_1529.
    rewrite piu_zz_inPn_1024_1528.
    rewrite piu_zz_inPn_1024_1527.
    rewrite piu_zz_inPn_1024_1526.
    rewrite piu_zz_inPn_1024_1525.
    rewrite piu_zz_inPn_1024_1524.
    rewrite piu_zz_inPn_1024_1523.
    rewrite piu_zz_inPn_1024_1522.
    rewrite piu_zz_inPn_1024_1521.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1712-L1732 (assert Hb33) *)
Lemma piu_zz_hb_1024_33 : piu_zz_zprod_seg 1024%nat (512%nat + 992%nat) 16%nat = ((if zz_in_Pn 1024 1505%nat then Z.of_nat 1505%nat else 1%Z) * ((if zz_in_Pn 1024 1506%nat then Z.of_nat 1506%nat else 1%Z) * ((if zz_in_Pn 1024 1507%nat then Z.of_nat 1507%nat else 1%Z) * ((if zz_in_Pn 1024 1508%nat then Z.of_nat 1508%nat else 1%Z) * ((if zz_in_Pn 1024 1509%nat then Z.of_nat 1509%nat else 1%Z) * ((if zz_in_Pn 1024 1510%nat then Z.of_nat 1510%nat else 1%Z) * ((if zz_in_Pn 1024 1511%nat then Z.of_nat 1511%nat else 1%Z) * ((if zz_in_Pn 1024 1512%nat then Z.of_nat 1512%nat else 1%Z) * ((if zz_in_Pn 1024 1513%nat then Z.of_nat 1513%nat else 1%Z) * ((if zz_in_Pn 1024 1514%nat then Z.of_nat 1514%nat else 1%Z) * ((if zz_in_Pn 1024 1515%nat then Z.of_nat 1515%nat else 1%Z) * ((if zz_in_Pn 1024 1516%nat then Z.of_nat 1516%nat else 1%Z) * ((if zz_in_Pn 1024 1517%nat then Z.of_nat 1517%nat else 1%Z) * ((if zz_in_Pn 1024 1518%nat then Z.of_nat 1518%nat else 1%Z) * ((if zz_in_Pn 1024 1519%nat then Z.of_nat 1519%nat else 1%Z) * (if zz_in_Pn 1024 1520%nat then Z.of_nat 1520%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1520.
    rewrite piu_zz_inPn_1024_1519.
    rewrite piu_zz_inPn_1024_1518.
    rewrite piu_zz_inPn_1024_1517.
    rewrite piu_zz_inPn_1024_1516.
    rewrite piu_zz_inPn_1024_1515.
    rewrite piu_zz_inPn_1024_1514.
    rewrite piu_zz_inPn_1024_1513.
    rewrite piu_zz_inPn_1024_1512.
    rewrite piu_zz_inPn_1024_1511.
    rewrite piu_zz_inPn_1024_1510.
    rewrite piu_zz_inPn_1024_1509.
    rewrite piu_zz_inPn_1024_1508.
    rewrite piu_zz_inPn_1024_1507.
    rewrite piu_zz_inPn_1024_1506.
    rewrite piu_zz_inPn_1024_1505.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1733-L1753 (assert Hb34) *)
Lemma piu_zz_hb_1024_34 : piu_zz_zprod_seg 1024%nat (512%nat + 976%nat) 16%nat = ((if zz_in_Pn 1024 1489%nat then Z.of_nat 1489%nat else 1%Z) * ((if zz_in_Pn 1024 1490%nat then Z.of_nat 1490%nat else 1%Z) * ((if zz_in_Pn 1024 1491%nat then Z.of_nat 1491%nat else 1%Z) * ((if zz_in_Pn 1024 1492%nat then Z.of_nat 1492%nat else 1%Z) * ((if zz_in_Pn 1024 1493%nat then Z.of_nat 1493%nat else 1%Z) * ((if zz_in_Pn 1024 1494%nat then Z.of_nat 1494%nat else 1%Z) * ((if zz_in_Pn 1024 1495%nat then Z.of_nat 1495%nat else 1%Z) * ((if zz_in_Pn 1024 1496%nat then Z.of_nat 1496%nat else 1%Z) * ((if zz_in_Pn 1024 1497%nat then Z.of_nat 1497%nat else 1%Z) * ((if zz_in_Pn 1024 1498%nat then Z.of_nat 1498%nat else 1%Z) * ((if zz_in_Pn 1024 1499%nat then Z.of_nat 1499%nat else 1%Z) * ((if zz_in_Pn 1024 1500%nat then Z.of_nat 1500%nat else 1%Z) * ((if zz_in_Pn 1024 1501%nat then Z.of_nat 1501%nat else 1%Z) * ((if zz_in_Pn 1024 1502%nat then Z.of_nat 1502%nat else 1%Z) * ((if zz_in_Pn 1024 1503%nat then Z.of_nat 1503%nat else 1%Z) * (if zz_in_Pn 1024 1504%nat then Z.of_nat 1504%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1504.
    rewrite piu_zz_inPn_1024_1503.
    rewrite piu_zz_inPn_1024_1502.
    rewrite piu_zz_inPn_1024_1501.
    rewrite piu_zz_inPn_1024_1500.
    rewrite piu_zz_inPn_1024_1499.
    rewrite piu_zz_inPn_1024_1498.
    rewrite piu_zz_inPn_1024_1497.
    rewrite piu_zz_inPn_1024_1496.
    rewrite piu_zz_inPn_1024_1495.
    rewrite piu_zz_inPn_1024_1494.
    rewrite piu_zz_inPn_1024_1493.
    rewrite piu_zz_inPn_1024_1492.
    rewrite piu_zz_inPn_1024_1491.
    rewrite piu_zz_inPn_1024_1490.
    rewrite piu_zz_inPn_1024_1489.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1754-L1774 (assert Hb35) *)
Lemma piu_zz_hb_1024_35 : piu_zz_zprod_seg 1024%nat (512%nat + 960%nat) 16%nat = ((if zz_in_Pn 1024 1473%nat then Z.of_nat 1473%nat else 1%Z) * ((if zz_in_Pn 1024 1474%nat then Z.of_nat 1474%nat else 1%Z) * ((if zz_in_Pn 1024 1475%nat then Z.of_nat 1475%nat else 1%Z) * ((if zz_in_Pn 1024 1476%nat then Z.of_nat 1476%nat else 1%Z) * ((if zz_in_Pn 1024 1477%nat then Z.of_nat 1477%nat else 1%Z) * ((if zz_in_Pn 1024 1478%nat then Z.of_nat 1478%nat else 1%Z) * ((if zz_in_Pn 1024 1479%nat then Z.of_nat 1479%nat else 1%Z) * ((if zz_in_Pn 1024 1480%nat then Z.of_nat 1480%nat else 1%Z) * ((if zz_in_Pn 1024 1481%nat then Z.of_nat 1481%nat else 1%Z) * ((if zz_in_Pn 1024 1482%nat then Z.of_nat 1482%nat else 1%Z) * ((if zz_in_Pn 1024 1483%nat then Z.of_nat 1483%nat else 1%Z) * ((if zz_in_Pn 1024 1484%nat then Z.of_nat 1484%nat else 1%Z) * ((if zz_in_Pn 1024 1485%nat then Z.of_nat 1485%nat else 1%Z) * ((if zz_in_Pn 1024 1486%nat then Z.of_nat 1486%nat else 1%Z) * ((if zz_in_Pn 1024 1487%nat then Z.of_nat 1487%nat else 1%Z) * (if zz_in_Pn 1024 1488%nat then Z.of_nat 1488%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1488.
    rewrite piu_zz_inPn_1024_1487.
    rewrite piu_zz_inPn_1024_1486.
    rewrite piu_zz_inPn_1024_1485.
    rewrite piu_zz_inPn_1024_1484.
    rewrite piu_zz_inPn_1024_1483.
    rewrite piu_zz_inPn_1024_1482.
    rewrite piu_zz_inPn_1024_1481.
    rewrite piu_zz_inPn_1024_1480.
    rewrite piu_zz_inPn_1024_1479.
    rewrite piu_zz_inPn_1024_1478.
    rewrite piu_zz_inPn_1024_1477.
    rewrite piu_zz_inPn_1024_1476.
    rewrite piu_zz_inPn_1024_1475.
    rewrite piu_zz_inPn_1024_1474.
    rewrite piu_zz_inPn_1024_1473.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1775-L1795 (assert Hb36) *)
Lemma piu_zz_hb_1024_36 : piu_zz_zprod_seg 1024%nat (512%nat + 944%nat) 16%nat = ((if zz_in_Pn 1024 1457%nat then Z.of_nat 1457%nat else 1%Z) * ((if zz_in_Pn 1024 1458%nat then Z.of_nat 1458%nat else 1%Z) * ((if zz_in_Pn 1024 1459%nat then Z.of_nat 1459%nat else 1%Z) * ((if zz_in_Pn 1024 1460%nat then Z.of_nat 1460%nat else 1%Z) * ((if zz_in_Pn 1024 1461%nat then Z.of_nat 1461%nat else 1%Z) * ((if zz_in_Pn 1024 1462%nat then Z.of_nat 1462%nat else 1%Z) * ((if zz_in_Pn 1024 1463%nat then Z.of_nat 1463%nat else 1%Z) * ((if zz_in_Pn 1024 1464%nat then Z.of_nat 1464%nat else 1%Z) * ((if zz_in_Pn 1024 1465%nat then Z.of_nat 1465%nat else 1%Z) * ((if zz_in_Pn 1024 1466%nat then Z.of_nat 1466%nat else 1%Z) * ((if zz_in_Pn 1024 1467%nat then Z.of_nat 1467%nat else 1%Z) * ((if zz_in_Pn 1024 1468%nat then Z.of_nat 1468%nat else 1%Z) * ((if zz_in_Pn 1024 1469%nat then Z.of_nat 1469%nat else 1%Z) * ((if zz_in_Pn 1024 1470%nat then Z.of_nat 1470%nat else 1%Z) * ((if zz_in_Pn 1024 1471%nat then Z.of_nat 1471%nat else 1%Z) * (if zz_in_Pn 1024 1472%nat then Z.of_nat 1472%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1472.
    rewrite piu_zz_inPn_1024_1471.
    rewrite piu_zz_inPn_1024_1470.
    rewrite piu_zz_inPn_1024_1469.
    rewrite piu_zz_inPn_1024_1468.
    rewrite piu_zz_inPn_1024_1467.
    rewrite piu_zz_inPn_1024_1466.
    rewrite piu_zz_inPn_1024_1465.
    rewrite piu_zz_inPn_1024_1464.
    rewrite piu_zz_inPn_1024_1463.
    rewrite piu_zz_inPn_1024_1462.
    rewrite piu_zz_inPn_1024_1461.
    rewrite piu_zz_inPn_1024_1460.
    rewrite piu_zz_inPn_1024_1459.
    rewrite piu_zz_inPn_1024_1458.
    rewrite piu_zz_inPn_1024_1457.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1796-L1816 (assert Hb37) *)
Lemma piu_zz_hb_1024_37 : piu_zz_zprod_seg 1024%nat (512%nat + 928%nat) 16%nat = ((if zz_in_Pn 1024 1441%nat then Z.of_nat 1441%nat else 1%Z) * ((if zz_in_Pn 1024 1442%nat then Z.of_nat 1442%nat else 1%Z) * ((if zz_in_Pn 1024 1443%nat then Z.of_nat 1443%nat else 1%Z) * ((if zz_in_Pn 1024 1444%nat then Z.of_nat 1444%nat else 1%Z) * ((if zz_in_Pn 1024 1445%nat then Z.of_nat 1445%nat else 1%Z) * ((if zz_in_Pn 1024 1446%nat then Z.of_nat 1446%nat else 1%Z) * ((if zz_in_Pn 1024 1447%nat then Z.of_nat 1447%nat else 1%Z) * ((if zz_in_Pn 1024 1448%nat then Z.of_nat 1448%nat else 1%Z) * ((if zz_in_Pn 1024 1449%nat then Z.of_nat 1449%nat else 1%Z) * ((if zz_in_Pn 1024 1450%nat then Z.of_nat 1450%nat else 1%Z) * ((if zz_in_Pn 1024 1451%nat then Z.of_nat 1451%nat else 1%Z) * ((if zz_in_Pn 1024 1452%nat then Z.of_nat 1452%nat else 1%Z) * ((if zz_in_Pn 1024 1453%nat then Z.of_nat 1453%nat else 1%Z) * ((if zz_in_Pn 1024 1454%nat then Z.of_nat 1454%nat else 1%Z) * ((if zz_in_Pn 1024 1455%nat then Z.of_nat 1455%nat else 1%Z) * (if zz_in_Pn 1024 1456%nat then Z.of_nat 1456%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1456.
    rewrite piu_zz_inPn_1024_1455.
    rewrite piu_zz_inPn_1024_1454.
    rewrite piu_zz_inPn_1024_1453.
    rewrite piu_zz_inPn_1024_1452.
    rewrite piu_zz_inPn_1024_1451.
    rewrite piu_zz_inPn_1024_1450.
    rewrite piu_zz_inPn_1024_1449.
    rewrite piu_zz_inPn_1024_1448.
    rewrite piu_zz_inPn_1024_1447.
    rewrite piu_zz_inPn_1024_1446.
    rewrite piu_zz_inPn_1024_1445.
    rewrite piu_zz_inPn_1024_1444.
    rewrite piu_zz_inPn_1024_1443.
    rewrite piu_zz_inPn_1024_1442.
    rewrite piu_zz_inPn_1024_1441.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1817-L1837 (assert Hb38) *)
Lemma piu_zz_hb_1024_38 : piu_zz_zprod_seg 1024%nat (512%nat + 912%nat) 16%nat = ((if zz_in_Pn 1024 1425%nat then Z.of_nat 1425%nat else 1%Z) * ((if zz_in_Pn 1024 1426%nat then Z.of_nat 1426%nat else 1%Z) * ((if zz_in_Pn 1024 1427%nat then Z.of_nat 1427%nat else 1%Z) * ((if zz_in_Pn 1024 1428%nat then Z.of_nat 1428%nat else 1%Z) * ((if zz_in_Pn 1024 1429%nat then Z.of_nat 1429%nat else 1%Z) * ((if zz_in_Pn 1024 1430%nat then Z.of_nat 1430%nat else 1%Z) * ((if zz_in_Pn 1024 1431%nat then Z.of_nat 1431%nat else 1%Z) * ((if zz_in_Pn 1024 1432%nat then Z.of_nat 1432%nat else 1%Z) * ((if zz_in_Pn 1024 1433%nat then Z.of_nat 1433%nat else 1%Z) * ((if zz_in_Pn 1024 1434%nat then Z.of_nat 1434%nat else 1%Z) * ((if zz_in_Pn 1024 1435%nat then Z.of_nat 1435%nat else 1%Z) * ((if zz_in_Pn 1024 1436%nat then Z.of_nat 1436%nat else 1%Z) * ((if zz_in_Pn 1024 1437%nat then Z.of_nat 1437%nat else 1%Z) * ((if zz_in_Pn 1024 1438%nat then Z.of_nat 1438%nat else 1%Z) * ((if zz_in_Pn 1024 1439%nat then Z.of_nat 1439%nat else 1%Z) * (if zz_in_Pn 1024 1440%nat then Z.of_nat 1440%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1440.
    rewrite piu_zz_inPn_1024_1439.
    rewrite piu_zz_inPn_1024_1438.
    rewrite piu_zz_inPn_1024_1437.
    rewrite piu_zz_inPn_1024_1436.
    rewrite piu_zz_inPn_1024_1435.
    rewrite piu_zz_inPn_1024_1434.
    rewrite piu_zz_inPn_1024_1433.
    rewrite piu_zz_inPn_1024_1432.
    rewrite piu_zz_inPn_1024_1431.
    rewrite piu_zz_inPn_1024_1430.
    rewrite piu_zz_inPn_1024_1429.
    rewrite piu_zz_inPn_1024_1428.
    rewrite piu_zz_inPn_1024_1427.
    rewrite piu_zz_inPn_1024_1426.
    rewrite piu_zz_inPn_1024_1425.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1838-L1858 (assert Hb39) *)
Lemma piu_zz_hb_1024_39 : piu_zz_zprod_seg 1024%nat (512%nat + 896%nat) 16%nat = ((if zz_in_Pn 1024 1409%nat then Z.of_nat 1409%nat else 1%Z) * ((if zz_in_Pn 1024 1410%nat then Z.of_nat 1410%nat else 1%Z) * ((if zz_in_Pn 1024 1411%nat then Z.of_nat 1411%nat else 1%Z) * ((if zz_in_Pn 1024 1412%nat then Z.of_nat 1412%nat else 1%Z) * ((if zz_in_Pn 1024 1413%nat then Z.of_nat 1413%nat else 1%Z) * ((if zz_in_Pn 1024 1414%nat then Z.of_nat 1414%nat else 1%Z) * ((if zz_in_Pn 1024 1415%nat then Z.of_nat 1415%nat else 1%Z) * ((if zz_in_Pn 1024 1416%nat then Z.of_nat 1416%nat else 1%Z) * ((if zz_in_Pn 1024 1417%nat then Z.of_nat 1417%nat else 1%Z) * ((if zz_in_Pn 1024 1418%nat then Z.of_nat 1418%nat else 1%Z) * ((if zz_in_Pn 1024 1419%nat then Z.of_nat 1419%nat else 1%Z) * ((if zz_in_Pn 1024 1420%nat then Z.of_nat 1420%nat else 1%Z) * ((if zz_in_Pn 1024 1421%nat then Z.of_nat 1421%nat else 1%Z) * ((if zz_in_Pn 1024 1422%nat then Z.of_nat 1422%nat else 1%Z) * ((if zz_in_Pn 1024 1423%nat then Z.of_nat 1423%nat else 1%Z) * (if zz_in_Pn 1024 1424%nat then Z.of_nat 1424%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1424.
    rewrite piu_zz_inPn_1024_1423.
    rewrite piu_zz_inPn_1024_1422.
    rewrite piu_zz_inPn_1024_1421.
    rewrite piu_zz_inPn_1024_1420.
    rewrite piu_zz_inPn_1024_1419.
    rewrite piu_zz_inPn_1024_1418.
    rewrite piu_zz_inPn_1024_1417.
    rewrite piu_zz_inPn_1024_1416.
    rewrite piu_zz_inPn_1024_1415.
    rewrite piu_zz_inPn_1024_1414.
    rewrite piu_zz_inPn_1024_1413.
    rewrite piu_zz_inPn_1024_1412.
    rewrite piu_zz_inPn_1024_1411.
    rewrite piu_zz_inPn_1024_1410.
    rewrite piu_zz_inPn_1024_1409.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1859-L1879 (assert Hb40) *)
Lemma piu_zz_hb_1024_40 : piu_zz_zprod_seg 1024%nat (512%nat + 880%nat) 16%nat = ((if zz_in_Pn 1024 1393%nat then Z.of_nat 1393%nat else 1%Z) * ((if zz_in_Pn 1024 1394%nat then Z.of_nat 1394%nat else 1%Z) * ((if zz_in_Pn 1024 1395%nat then Z.of_nat 1395%nat else 1%Z) * ((if zz_in_Pn 1024 1396%nat then Z.of_nat 1396%nat else 1%Z) * ((if zz_in_Pn 1024 1397%nat then Z.of_nat 1397%nat else 1%Z) * ((if zz_in_Pn 1024 1398%nat then Z.of_nat 1398%nat else 1%Z) * ((if zz_in_Pn 1024 1399%nat then Z.of_nat 1399%nat else 1%Z) * ((if zz_in_Pn 1024 1400%nat then Z.of_nat 1400%nat else 1%Z) * ((if zz_in_Pn 1024 1401%nat then Z.of_nat 1401%nat else 1%Z) * ((if zz_in_Pn 1024 1402%nat then Z.of_nat 1402%nat else 1%Z) * ((if zz_in_Pn 1024 1403%nat then Z.of_nat 1403%nat else 1%Z) * ((if zz_in_Pn 1024 1404%nat then Z.of_nat 1404%nat else 1%Z) * ((if zz_in_Pn 1024 1405%nat then Z.of_nat 1405%nat else 1%Z) * ((if zz_in_Pn 1024 1406%nat then Z.of_nat 1406%nat else 1%Z) * ((if zz_in_Pn 1024 1407%nat then Z.of_nat 1407%nat else 1%Z) * (if zz_in_Pn 1024 1408%nat then Z.of_nat 1408%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1408.
    rewrite piu_zz_inPn_1024_1407.
    rewrite piu_zz_inPn_1024_1406.
    rewrite piu_zz_inPn_1024_1405.
    rewrite piu_zz_inPn_1024_1404.
    rewrite piu_zz_inPn_1024_1403.
    rewrite piu_zz_inPn_1024_1402.
    rewrite piu_zz_inPn_1024_1401.
    rewrite piu_zz_inPn_1024_1400.
    rewrite piu_zz_inPn_1024_1399.
    rewrite piu_zz_inPn_1024_1398.
    rewrite piu_zz_inPn_1024_1397.
    rewrite piu_zz_inPn_1024_1396.
    rewrite piu_zz_inPn_1024_1395.
    rewrite piu_zz_inPn_1024_1394.
    rewrite piu_zz_inPn_1024_1393.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1880-L1900 (assert Hb41) *)
Lemma piu_zz_hb_1024_41 : piu_zz_zprod_seg 1024%nat (512%nat + 864%nat) 16%nat = ((if zz_in_Pn 1024 1377%nat then Z.of_nat 1377%nat else 1%Z) * ((if zz_in_Pn 1024 1378%nat then Z.of_nat 1378%nat else 1%Z) * ((if zz_in_Pn 1024 1379%nat then Z.of_nat 1379%nat else 1%Z) * ((if zz_in_Pn 1024 1380%nat then Z.of_nat 1380%nat else 1%Z) * ((if zz_in_Pn 1024 1381%nat then Z.of_nat 1381%nat else 1%Z) * ((if zz_in_Pn 1024 1382%nat then Z.of_nat 1382%nat else 1%Z) * ((if zz_in_Pn 1024 1383%nat then Z.of_nat 1383%nat else 1%Z) * ((if zz_in_Pn 1024 1384%nat then Z.of_nat 1384%nat else 1%Z) * ((if zz_in_Pn 1024 1385%nat then Z.of_nat 1385%nat else 1%Z) * ((if zz_in_Pn 1024 1386%nat then Z.of_nat 1386%nat else 1%Z) * ((if zz_in_Pn 1024 1387%nat then Z.of_nat 1387%nat else 1%Z) * ((if zz_in_Pn 1024 1388%nat then Z.of_nat 1388%nat else 1%Z) * ((if zz_in_Pn 1024 1389%nat then Z.of_nat 1389%nat else 1%Z) * ((if zz_in_Pn 1024 1390%nat then Z.of_nat 1390%nat else 1%Z) * ((if zz_in_Pn 1024 1391%nat then Z.of_nat 1391%nat else 1%Z) * (if zz_in_Pn 1024 1392%nat then Z.of_nat 1392%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1392.
    rewrite piu_zz_inPn_1024_1391.
    rewrite piu_zz_inPn_1024_1390.
    rewrite piu_zz_inPn_1024_1389.
    rewrite piu_zz_inPn_1024_1388.
    rewrite piu_zz_inPn_1024_1387.
    rewrite piu_zz_inPn_1024_1386.
    rewrite piu_zz_inPn_1024_1385.
    rewrite piu_zz_inPn_1024_1384.
    rewrite piu_zz_inPn_1024_1383.
    rewrite piu_zz_inPn_1024_1382.
    rewrite piu_zz_inPn_1024_1381.
    rewrite piu_zz_inPn_1024_1380.
    rewrite piu_zz_inPn_1024_1379.
    rewrite piu_zz_inPn_1024_1378.
    rewrite piu_zz_inPn_1024_1377.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1901-L1921 (assert Hb42) *)
Lemma piu_zz_hb_1024_42 : piu_zz_zprod_seg 1024%nat (512%nat + 848%nat) 16%nat = ((if zz_in_Pn 1024 1361%nat then Z.of_nat 1361%nat else 1%Z) * ((if zz_in_Pn 1024 1362%nat then Z.of_nat 1362%nat else 1%Z) * ((if zz_in_Pn 1024 1363%nat then Z.of_nat 1363%nat else 1%Z) * ((if zz_in_Pn 1024 1364%nat then Z.of_nat 1364%nat else 1%Z) * ((if zz_in_Pn 1024 1365%nat then Z.of_nat 1365%nat else 1%Z) * ((if zz_in_Pn 1024 1366%nat then Z.of_nat 1366%nat else 1%Z) * ((if zz_in_Pn 1024 1367%nat then Z.of_nat 1367%nat else 1%Z) * ((if zz_in_Pn 1024 1368%nat then Z.of_nat 1368%nat else 1%Z) * ((if zz_in_Pn 1024 1369%nat then Z.of_nat 1369%nat else 1%Z) * ((if zz_in_Pn 1024 1370%nat then Z.of_nat 1370%nat else 1%Z) * ((if zz_in_Pn 1024 1371%nat then Z.of_nat 1371%nat else 1%Z) * ((if zz_in_Pn 1024 1372%nat then Z.of_nat 1372%nat else 1%Z) * ((if zz_in_Pn 1024 1373%nat then Z.of_nat 1373%nat else 1%Z) * ((if zz_in_Pn 1024 1374%nat then Z.of_nat 1374%nat else 1%Z) * ((if zz_in_Pn 1024 1375%nat then Z.of_nat 1375%nat else 1%Z) * (if zz_in_Pn 1024 1376%nat then Z.of_nat 1376%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1376.
    rewrite piu_zz_inPn_1024_1375.
    rewrite piu_zz_inPn_1024_1374.
    rewrite piu_zz_inPn_1024_1373.
    rewrite piu_zz_inPn_1024_1372.
    rewrite piu_zz_inPn_1024_1371.
    rewrite piu_zz_inPn_1024_1370.
    rewrite piu_zz_inPn_1024_1369.
    rewrite piu_zz_inPn_1024_1368.
    rewrite piu_zz_inPn_1024_1367.
    rewrite piu_zz_inPn_1024_1366.
    rewrite piu_zz_inPn_1024_1365.
    rewrite piu_zz_inPn_1024_1364.
    rewrite piu_zz_inPn_1024_1363.
    rewrite piu_zz_inPn_1024_1362.
    rewrite piu_zz_inPn_1024_1361.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1922-L1942 (assert Hb43) *)
Lemma piu_zz_hb_1024_43 : piu_zz_zprod_seg 1024%nat (512%nat + 832%nat) 16%nat = ((if zz_in_Pn 1024 1345%nat then Z.of_nat 1345%nat else 1%Z) * ((if zz_in_Pn 1024 1346%nat then Z.of_nat 1346%nat else 1%Z) * ((if zz_in_Pn 1024 1347%nat then Z.of_nat 1347%nat else 1%Z) * ((if zz_in_Pn 1024 1348%nat then Z.of_nat 1348%nat else 1%Z) * ((if zz_in_Pn 1024 1349%nat then Z.of_nat 1349%nat else 1%Z) * ((if zz_in_Pn 1024 1350%nat then Z.of_nat 1350%nat else 1%Z) * ((if zz_in_Pn 1024 1351%nat then Z.of_nat 1351%nat else 1%Z) * ((if zz_in_Pn 1024 1352%nat then Z.of_nat 1352%nat else 1%Z) * ((if zz_in_Pn 1024 1353%nat then Z.of_nat 1353%nat else 1%Z) * ((if zz_in_Pn 1024 1354%nat then Z.of_nat 1354%nat else 1%Z) * ((if zz_in_Pn 1024 1355%nat then Z.of_nat 1355%nat else 1%Z) * ((if zz_in_Pn 1024 1356%nat then Z.of_nat 1356%nat else 1%Z) * ((if zz_in_Pn 1024 1357%nat then Z.of_nat 1357%nat else 1%Z) * ((if zz_in_Pn 1024 1358%nat then Z.of_nat 1358%nat else 1%Z) * ((if zz_in_Pn 1024 1359%nat then Z.of_nat 1359%nat else 1%Z) * (if zz_in_Pn 1024 1360%nat then Z.of_nat 1360%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1360.
    rewrite piu_zz_inPn_1024_1359.
    rewrite piu_zz_inPn_1024_1358.
    rewrite piu_zz_inPn_1024_1357.
    rewrite piu_zz_inPn_1024_1356.
    rewrite piu_zz_inPn_1024_1355.
    rewrite piu_zz_inPn_1024_1354.
    rewrite piu_zz_inPn_1024_1353.
    rewrite piu_zz_inPn_1024_1352.
    rewrite piu_zz_inPn_1024_1351.
    rewrite piu_zz_inPn_1024_1350.
    rewrite piu_zz_inPn_1024_1349.
    rewrite piu_zz_inPn_1024_1348.
    rewrite piu_zz_inPn_1024_1347.
    rewrite piu_zz_inPn_1024_1346.
    rewrite piu_zz_inPn_1024_1345.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1943-L1963 (assert Hb44) *)
Lemma piu_zz_hb_1024_44 : piu_zz_zprod_seg 1024%nat (512%nat + 816%nat) 16%nat = ((if zz_in_Pn 1024 1329%nat then Z.of_nat 1329%nat else 1%Z) * ((if zz_in_Pn 1024 1330%nat then Z.of_nat 1330%nat else 1%Z) * ((if zz_in_Pn 1024 1331%nat then Z.of_nat 1331%nat else 1%Z) * ((if zz_in_Pn 1024 1332%nat then Z.of_nat 1332%nat else 1%Z) * ((if zz_in_Pn 1024 1333%nat then Z.of_nat 1333%nat else 1%Z) * ((if zz_in_Pn 1024 1334%nat then Z.of_nat 1334%nat else 1%Z) * ((if zz_in_Pn 1024 1335%nat then Z.of_nat 1335%nat else 1%Z) * ((if zz_in_Pn 1024 1336%nat then Z.of_nat 1336%nat else 1%Z) * ((if zz_in_Pn 1024 1337%nat then Z.of_nat 1337%nat else 1%Z) * ((if zz_in_Pn 1024 1338%nat then Z.of_nat 1338%nat else 1%Z) * ((if zz_in_Pn 1024 1339%nat then Z.of_nat 1339%nat else 1%Z) * ((if zz_in_Pn 1024 1340%nat then Z.of_nat 1340%nat else 1%Z) * ((if zz_in_Pn 1024 1341%nat then Z.of_nat 1341%nat else 1%Z) * ((if zz_in_Pn 1024 1342%nat then Z.of_nat 1342%nat else 1%Z) * ((if zz_in_Pn 1024 1343%nat then Z.of_nat 1343%nat else 1%Z) * (if zz_in_Pn 1024 1344%nat then Z.of_nat 1344%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1344.
    rewrite piu_zz_inPn_1024_1343.
    rewrite piu_zz_inPn_1024_1342.
    rewrite piu_zz_inPn_1024_1341.
    rewrite piu_zz_inPn_1024_1340.
    rewrite piu_zz_inPn_1024_1339.
    rewrite piu_zz_inPn_1024_1338.
    rewrite piu_zz_inPn_1024_1337.
    rewrite piu_zz_inPn_1024_1336.
    rewrite piu_zz_inPn_1024_1335.
    rewrite piu_zz_inPn_1024_1334.
    rewrite piu_zz_inPn_1024_1333.
    rewrite piu_zz_inPn_1024_1332.
    rewrite piu_zz_inPn_1024_1331.
    rewrite piu_zz_inPn_1024_1330.
    rewrite piu_zz_inPn_1024_1329.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1964-L1984 (assert Hb45) *)
Lemma piu_zz_hb_1024_45 : piu_zz_zprod_seg 1024%nat (512%nat + 800%nat) 16%nat = ((if zz_in_Pn 1024 1313%nat then Z.of_nat 1313%nat else 1%Z) * ((if zz_in_Pn 1024 1314%nat then Z.of_nat 1314%nat else 1%Z) * ((if zz_in_Pn 1024 1315%nat then Z.of_nat 1315%nat else 1%Z) * ((if zz_in_Pn 1024 1316%nat then Z.of_nat 1316%nat else 1%Z) * ((if zz_in_Pn 1024 1317%nat then Z.of_nat 1317%nat else 1%Z) * ((if zz_in_Pn 1024 1318%nat then Z.of_nat 1318%nat else 1%Z) * ((if zz_in_Pn 1024 1319%nat then Z.of_nat 1319%nat else 1%Z) * ((if zz_in_Pn 1024 1320%nat then Z.of_nat 1320%nat else 1%Z) * ((if zz_in_Pn 1024 1321%nat then Z.of_nat 1321%nat else 1%Z) * ((if zz_in_Pn 1024 1322%nat then Z.of_nat 1322%nat else 1%Z) * ((if zz_in_Pn 1024 1323%nat then Z.of_nat 1323%nat else 1%Z) * ((if zz_in_Pn 1024 1324%nat then Z.of_nat 1324%nat else 1%Z) * ((if zz_in_Pn 1024 1325%nat then Z.of_nat 1325%nat else 1%Z) * ((if zz_in_Pn 1024 1326%nat then Z.of_nat 1326%nat else 1%Z) * ((if zz_in_Pn 1024 1327%nat then Z.of_nat 1327%nat else 1%Z) * (if zz_in_Pn 1024 1328%nat then Z.of_nat 1328%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1328.
    rewrite piu_zz_inPn_1024_1327.
    rewrite piu_zz_inPn_1024_1326.
    rewrite piu_zz_inPn_1024_1325.
    rewrite piu_zz_inPn_1024_1324.
    rewrite piu_zz_inPn_1024_1323.
    rewrite piu_zz_inPn_1024_1322.
    rewrite piu_zz_inPn_1024_1321.
    rewrite piu_zz_inPn_1024_1320.
    rewrite piu_zz_inPn_1024_1319.
    rewrite piu_zz_inPn_1024_1318.
    rewrite piu_zz_inPn_1024_1317.
    rewrite piu_zz_inPn_1024_1316.
    rewrite piu_zz_inPn_1024_1315.
    rewrite piu_zz_inPn_1024_1314.
    rewrite piu_zz_inPn_1024_1313.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1985-L2005 (assert Hb46) *)
Lemma piu_zz_hb_1024_46 : piu_zz_zprod_seg 1024%nat (512%nat + 784%nat) 16%nat = ((if zz_in_Pn 1024 1297%nat then Z.of_nat 1297%nat else 1%Z) * ((if zz_in_Pn 1024 1298%nat then Z.of_nat 1298%nat else 1%Z) * ((if zz_in_Pn 1024 1299%nat then Z.of_nat 1299%nat else 1%Z) * ((if zz_in_Pn 1024 1300%nat then Z.of_nat 1300%nat else 1%Z) * ((if zz_in_Pn 1024 1301%nat then Z.of_nat 1301%nat else 1%Z) * ((if zz_in_Pn 1024 1302%nat then Z.of_nat 1302%nat else 1%Z) * ((if zz_in_Pn 1024 1303%nat then Z.of_nat 1303%nat else 1%Z) * ((if zz_in_Pn 1024 1304%nat then Z.of_nat 1304%nat else 1%Z) * ((if zz_in_Pn 1024 1305%nat then Z.of_nat 1305%nat else 1%Z) * ((if zz_in_Pn 1024 1306%nat then Z.of_nat 1306%nat else 1%Z) * ((if zz_in_Pn 1024 1307%nat then Z.of_nat 1307%nat else 1%Z) * ((if zz_in_Pn 1024 1308%nat then Z.of_nat 1308%nat else 1%Z) * ((if zz_in_Pn 1024 1309%nat then Z.of_nat 1309%nat else 1%Z) * ((if zz_in_Pn 1024 1310%nat then Z.of_nat 1310%nat else 1%Z) * ((if zz_in_Pn 1024 1311%nat then Z.of_nat 1311%nat else 1%Z) * (if zz_in_Pn 1024 1312%nat then Z.of_nat 1312%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1312.
    rewrite piu_zz_inPn_1024_1311.
    rewrite piu_zz_inPn_1024_1310.
    rewrite piu_zz_inPn_1024_1309.
    rewrite piu_zz_inPn_1024_1308.
    rewrite piu_zz_inPn_1024_1307.
    rewrite piu_zz_inPn_1024_1306.
    rewrite piu_zz_inPn_1024_1305.
    rewrite piu_zz_inPn_1024_1304.
    rewrite piu_zz_inPn_1024_1303.
    rewrite piu_zz_inPn_1024_1302.
    rewrite piu_zz_inPn_1024_1301.
    rewrite piu_zz_inPn_1024_1300.
    rewrite piu_zz_inPn_1024_1299.
    rewrite piu_zz_inPn_1024_1298.
    rewrite piu_zz_inPn_1024_1297.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L2006-L2026 (assert Hb47) *)
Lemma piu_zz_hb_1024_47 : piu_zz_zprod_seg 1024%nat (512%nat + 768%nat) 16%nat = ((if zz_in_Pn 1024 1281%nat then Z.of_nat 1281%nat else 1%Z) * ((if zz_in_Pn 1024 1282%nat then Z.of_nat 1282%nat else 1%Z) * ((if zz_in_Pn 1024 1283%nat then Z.of_nat 1283%nat else 1%Z) * ((if zz_in_Pn 1024 1284%nat then Z.of_nat 1284%nat else 1%Z) * ((if zz_in_Pn 1024 1285%nat then Z.of_nat 1285%nat else 1%Z) * ((if zz_in_Pn 1024 1286%nat then Z.of_nat 1286%nat else 1%Z) * ((if zz_in_Pn 1024 1287%nat then Z.of_nat 1287%nat else 1%Z) * ((if zz_in_Pn 1024 1288%nat then Z.of_nat 1288%nat else 1%Z) * ((if zz_in_Pn 1024 1289%nat then Z.of_nat 1289%nat else 1%Z) * ((if zz_in_Pn 1024 1290%nat then Z.of_nat 1290%nat else 1%Z) * ((if zz_in_Pn 1024 1291%nat then Z.of_nat 1291%nat else 1%Z) * ((if zz_in_Pn 1024 1292%nat then Z.of_nat 1292%nat else 1%Z) * ((if zz_in_Pn 1024 1293%nat then Z.of_nat 1293%nat else 1%Z) * ((if zz_in_Pn 1024 1294%nat then Z.of_nat 1294%nat else 1%Z) * ((if zz_in_Pn 1024 1295%nat then Z.of_nat 1295%nat else 1%Z) * (if zz_in_Pn 1024 1296%nat then Z.of_nat 1296%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1296.
    rewrite piu_zz_inPn_1024_1295.
    rewrite piu_zz_inPn_1024_1294.
    rewrite piu_zz_inPn_1024_1293.
    rewrite piu_zz_inPn_1024_1292.
    rewrite piu_zz_inPn_1024_1291.
    rewrite piu_zz_inPn_1024_1290.
    rewrite piu_zz_inPn_1024_1289.
    rewrite piu_zz_inPn_1024_1288.
    rewrite piu_zz_inPn_1024_1287.
    rewrite piu_zz_inPn_1024_1286.
    rewrite piu_zz_inPn_1024_1285.
    rewrite piu_zz_inPn_1024_1284.
    rewrite piu_zz_inPn_1024_1283.
    rewrite piu_zz_inPn_1024_1282.
    rewrite piu_zz_inPn_1024_1281.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
