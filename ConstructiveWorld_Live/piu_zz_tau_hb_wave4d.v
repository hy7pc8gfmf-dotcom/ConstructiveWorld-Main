(* piu_zz_tau_hb_wave4d.v — KB11 Hb 升格候选子片 4/8（1024 段 Hb16-Hb31·机械升格件·零漂移回读断言已过）。
   [KB20 checkpoint split] 本件=wave4（1024_16..31 重条区）四等分 d/4；引理自 wave4 逐字搬移，语句/体零改写。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave4.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* src piu_zz_tau_enclosure.v L1607-L1627 (assert Hb28) *)
Lemma piu_zz_hb_1024_28 : piu_zz_zprod_seg 1024%nat (512%nat + 1072%nat) 16%nat = ((if zz_in_Pn 1024 1585%nat then Z.of_nat 1585%nat else 1%Z) * ((if zz_in_Pn 1024 1586%nat then Z.of_nat 1586%nat else 1%Z) * ((if zz_in_Pn 1024 1587%nat then Z.of_nat 1587%nat else 1%Z) * ((if zz_in_Pn 1024 1588%nat then Z.of_nat 1588%nat else 1%Z) * ((if zz_in_Pn 1024 1589%nat then Z.of_nat 1589%nat else 1%Z) * ((if zz_in_Pn 1024 1590%nat then Z.of_nat 1590%nat else 1%Z) * ((if zz_in_Pn 1024 1591%nat then Z.of_nat 1591%nat else 1%Z) * ((if zz_in_Pn 1024 1592%nat then Z.of_nat 1592%nat else 1%Z) * ((if zz_in_Pn 1024 1593%nat then Z.of_nat 1593%nat else 1%Z) * ((if zz_in_Pn 1024 1594%nat then Z.of_nat 1594%nat else 1%Z) * ((if zz_in_Pn 1024 1595%nat then Z.of_nat 1595%nat else 1%Z) * ((if zz_in_Pn 1024 1596%nat then Z.of_nat 1596%nat else 1%Z) * ((if zz_in_Pn 1024 1597%nat then Z.of_nat 1597%nat else 1%Z) * ((if zz_in_Pn 1024 1598%nat then Z.of_nat 1598%nat else 1%Z) * ((if zz_in_Pn 1024 1599%nat then Z.of_nat 1599%nat else 1%Z) * (if zz_in_Pn 1024 1600%nat then Z.of_nat 1600%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1600.
    rewrite piu_zz_inPn_1024_1599.
    rewrite piu_zz_inPn_1024_1598.
    rewrite piu_zz_inPn_1024_1597.
    rewrite piu_zz_inPn_1024_1596.
    rewrite piu_zz_inPn_1024_1595.
    rewrite piu_zz_inPn_1024_1594.
    rewrite piu_zz_inPn_1024_1593.
    rewrite piu_zz_inPn_1024_1592.
    rewrite piu_zz_inPn_1024_1591.
    rewrite piu_zz_inPn_1024_1590.
    rewrite piu_zz_inPn_1024_1589.
    rewrite piu_zz_inPn_1024_1588.
    rewrite piu_zz_inPn_1024_1587.
    rewrite piu_zz_inPn_1024_1586.
    rewrite piu_zz_inPn_1024_1585.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1628-L1648 (assert Hb29) *)
Lemma piu_zz_hb_1024_29 : piu_zz_zprod_seg 1024%nat (512%nat + 1056%nat) 16%nat = ((if zz_in_Pn 1024 1569%nat then Z.of_nat 1569%nat else 1%Z) * ((if zz_in_Pn 1024 1570%nat then Z.of_nat 1570%nat else 1%Z) * ((if zz_in_Pn 1024 1571%nat then Z.of_nat 1571%nat else 1%Z) * ((if zz_in_Pn 1024 1572%nat then Z.of_nat 1572%nat else 1%Z) * ((if zz_in_Pn 1024 1573%nat then Z.of_nat 1573%nat else 1%Z) * ((if zz_in_Pn 1024 1574%nat then Z.of_nat 1574%nat else 1%Z) * ((if zz_in_Pn 1024 1575%nat then Z.of_nat 1575%nat else 1%Z) * ((if zz_in_Pn 1024 1576%nat then Z.of_nat 1576%nat else 1%Z) * ((if zz_in_Pn 1024 1577%nat then Z.of_nat 1577%nat else 1%Z) * ((if zz_in_Pn 1024 1578%nat then Z.of_nat 1578%nat else 1%Z) * ((if zz_in_Pn 1024 1579%nat then Z.of_nat 1579%nat else 1%Z) * ((if zz_in_Pn 1024 1580%nat then Z.of_nat 1580%nat else 1%Z) * ((if zz_in_Pn 1024 1581%nat then Z.of_nat 1581%nat else 1%Z) * ((if zz_in_Pn 1024 1582%nat then Z.of_nat 1582%nat else 1%Z) * ((if zz_in_Pn 1024 1583%nat then Z.of_nat 1583%nat else 1%Z) * (if zz_in_Pn 1024 1584%nat then Z.of_nat 1584%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1584.
    rewrite piu_zz_inPn_1024_1583.
    rewrite piu_zz_inPn_1024_1582.
    rewrite piu_zz_inPn_1024_1581.
    rewrite piu_zz_inPn_1024_1580.
    rewrite piu_zz_inPn_1024_1579.
    rewrite piu_zz_inPn_1024_1578.
    rewrite piu_zz_inPn_1024_1577.
    rewrite piu_zz_inPn_1024_1576.
    rewrite piu_zz_inPn_1024_1575.
    rewrite piu_zz_inPn_1024_1574.
    rewrite piu_zz_inPn_1024_1573.
    rewrite piu_zz_inPn_1024_1572.
    rewrite piu_zz_inPn_1024_1571.
    rewrite piu_zz_inPn_1024_1570.
    rewrite piu_zz_inPn_1024_1569.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1649-L1669 (assert Hb30) *)
Lemma piu_zz_hb_1024_30 : piu_zz_zprod_seg 1024%nat (512%nat + 1040%nat) 16%nat = ((if zz_in_Pn 1024 1553%nat then Z.of_nat 1553%nat else 1%Z) * ((if zz_in_Pn 1024 1554%nat then Z.of_nat 1554%nat else 1%Z) * ((if zz_in_Pn 1024 1555%nat then Z.of_nat 1555%nat else 1%Z) * ((if zz_in_Pn 1024 1556%nat then Z.of_nat 1556%nat else 1%Z) * ((if zz_in_Pn 1024 1557%nat then Z.of_nat 1557%nat else 1%Z) * ((if zz_in_Pn 1024 1558%nat then Z.of_nat 1558%nat else 1%Z) * ((if zz_in_Pn 1024 1559%nat then Z.of_nat 1559%nat else 1%Z) * ((if zz_in_Pn 1024 1560%nat then Z.of_nat 1560%nat else 1%Z) * ((if zz_in_Pn 1024 1561%nat then Z.of_nat 1561%nat else 1%Z) * ((if zz_in_Pn 1024 1562%nat then Z.of_nat 1562%nat else 1%Z) * ((if zz_in_Pn 1024 1563%nat then Z.of_nat 1563%nat else 1%Z) * ((if zz_in_Pn 1024 1564%nat then Z.of_nat 1564%nat else 1%Z) * ((if zz_in_Pn 1024 1565%nat then Z.of_nat 1565%nat else 1%Z) * ((if zz_in_Pn 1024 1566%nat then Z.of_nat 1566%nat else 1%Z) * ((if zz_in_Pn 1024 1567%nat then Z.of_nat 1567%nat else 1%Z) * (if zz_in_Pn 1024 1568%nat then Z.of_nat 1568%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1568.
    rewrite piu_zz_inPn_1024_1567.
    rewrite piu_zz_inPn_1024_1566.
    rewrite piu_zz_inPn_1024_1565.
    rewrite piu_zz_inPn_1024_1564.
    rewrite piu_zz_inPn_1024_1563.
    rewrite piu_zz_inPn_1024_1562.
    rewrite piu_zz_inPn_1024_1561.
    rewrite piu_zz_inPn_1024_1560.
    rewrite piu_zz_inPn_1024_1559.
    rewrite piu_zz_inPn_1024_1558.
    rewrite piu_zz_inPn_1024_1557.
    rewrite piu_zz_inPn_1024_1556.
    rewrite piu_zz_inPn_1024_1555.
    rewrite piu_zz_inPn_1024_1554.
    rewrite piu_zz_inPn_1024_1553.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1670-L1690 (assert Hb31) *)
Lemma piu_zz_hb_1024_31 : piu_zz_zprod_seg 1024%nat (512%nat + 1024%nat) 16%nat = ((if zz_in_Pn 1024 1537%nat then Z.of_nat 1537%nat else 1%Z) * ((if zz_in_Pn 1024 1538%nat then Z.of_nat 1538%nat else 1%Z) * ((if zz_in_Pn 1024 1539%nat then Z.of_nat 1539%nat else 1%Z) * ((if zz_in_Pn 1024 1540%nat then Z.of_nat 1540%nat else 1%Z) * ((if zz_in_Pn 1024 1541%nat then Z.of_nat 1541%nat else 1%Z) * ((if zz_in_Pn 1024 1542%nat then Z.of_nat 1542%nat else 1%Z) * ((if zz_in_Pn 1024 1543%nat then Z.of_nat 1543%nat else 1%Z) * ((if zz_in_Pn 1024 1544%nat then Z.of_nat 1544%nat else 1%Z) * ((if zz_in_Pn 1024 1545%nat then Z.of_nat 1545%nat else 1%Z) * ((if zz_in_Pn 1024 1546%nat then Z.of_nat 1546%nat else 1%Z) * ((if zz_in_Pn 1024 1547%nat then Z.of_nat 1547%nat else 1%Z) * ((if zz_in_Pn 1024 1548%nat then Z.of_nat 1548%nat else 1%Z) * ((if zz_in_Pn 1024 1549%nat then Z.of_nat 1549%nat else 1%Z) * ((if zz_in_Pn 1024 1550%nat then Z.of_nat 1550%nat else 1%Z) * ((if zz_in_Pn 1024 1551%nat then Z.of_nat 1551%nat else 1%Z) * (if zz_in_Pn 1024 1552%nat then Z.of_nat 1552%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1552.
    rewrite piu_zz_inPn_1024_1551.
    rewrite piu_zz_inPn_1024_1550.
    rewrite piu_zz_inPn_1024_1549.
    rewrite piu_zz_inPn_1024_1548.
    rewrite piu_zz_inPn_1024_1547.
    rewrite piu_zz_inPn_1024_1546.
    rewrite piu_zz_inPn_1024_1545.
    rewrite piu_zz_inPn_1024_1544.
    rewrite piu_zz_inPn_1024_1543.
    rewrite piu_zz_inPn_1024_1542.
    rewrite piu_zz_inPn_1024_1541.
    rewrite piu_zz_inPn_1024_1540.
    rewrite piu_zz_inPn_1024_1539.
    rewrite piu_zz_inPn_1024_1538.
    rewrite piu_zz_inPn_1024_1537.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
