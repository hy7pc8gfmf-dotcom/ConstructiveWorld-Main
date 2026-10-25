(* piu_zz_tau_hb_wave4c.v — KB11 Hb 升格候选子片 4/8（1024 段 Hb16-Hb31·机械升格件·零漂移回读断言已过）。
   [KB20 checkpoint split] 本件=wave4（1024_16..31 重条区）四等分 c/4；引理自 wave4 逐字搬移，语句/体零改写。
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
(* src piu_zz_tau_enclosure.v L1523-L1543 (assert Hb24) *)
Lemma piu_zz_hb_1024_24 : piu_zz_zprod_seg 1024%nat (512%nat + 1136%nat) 16%nat = ((if zz_in_Pn 1024 1649%nat then Z.of_nat 1649%nat else 1%Z) * ((if zz_in_Pn 1024 1650%nat then Z.of_nat 1650%nat else 1%Z) * ((if zz_in_Pn 1024 1651%nat then Z.of_nat 1651%nat else 1%Z) * ((if zz_in_Pn 1024 1652%nat then Z.of_nat 1652%nat else 1%Z) * ((if zz_in_Pn 1024 1653%nat then Z.of_nat 1653%nat else 1%Z) * ((if zz_in_Pn 1024 1654%nat then Z.of_nat 1654%nat else 1%Z) * ((if zz_in_Pn 1024 1655%nat then Z.of_nat 1655%nat else 1%Z) * ((if zz_in_Pn 1024 1656%nat then Z.of_nat 1656%nat else 1%Z) * ((if zz_in_Pn 1024 1657%nat then Z.of_nat 1657%nat else 1%Z) * ((if zz_in_Pn 1024 1658%nat then Z.of_nat 1658%nat else 1%Z) * ((if zz_in_Pn 1024 1659%nat then Z.of_nat 1659%nat else 1%Z) * ((if zz_in_Pn 1024 1660%nat then Z.of_nat 1660%nat else 1%Z) * ((if zz_in_Pn 1024 1661%nat then Z.of_nat 1661%nat else 1%Z) * ((if zz_in_Pn 1024 1662%nat then Z.of_nat 1662%nat else 1%Z) * ((if zz_in_Pn 1024 1663%nat then Z.of_nat 1663%nat else 1%Z) * (if zz_in_Pn 1024 1664%nat then Z.of_nat 1664%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1664.
    rewrite piu_zz_inPn_1024_1663.
    rewrite piu_zz_inPn_1024_1662.
    rewrite piu_zz_inPn_1024_1661.
    rewrite piu_zz_inPn_1024_1660.
    rewrite piu_zz_inPn_1024_1659.
    rewrite piu_zz_inPn_1024_1658.
    rewrite piu_zz_inPn_1024_1657.
    rewrite piu_zz_inPn_1024_1656.
    rewrite piu_zz_inPn_1024_1655.
    rewrite piu_zz_inPn_1024_1654.
    rewrite piu_zz_inPn_1024_1653.
    rewrite piu_zz_inPn_1024_1652.
    rewrite piu_zz_inPn_1024_1651.
    rewrite piu_zz_inPn_1024_1650.
    rewrite piu_zz_inPn_1024_1649.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1544-L1564 (assert Hb25) *)
Lemma piu_zz_hb_1024_25 : piu_zz_zprod_seg 1024%nat (512%nat + 1120%nat) 16%nat = ((if zz_in_Pn 1024 1633%nat then Z.of_nat 1633%nat else 1%Z) * ((if zz_in_Pn 1024 1634%nat then Z.of_nat 1634%nat else 1%Z) * ((if zz_in_Pn 1024 1635%nat then Z.of_nat 1635%nat else 1%Z) * ((if zz_in_Pn 1024 1636%nat then Z.of_nat 1636%nat else 1%Z) * ((if zz_in_Pn 1024 1637%nat then Z.of_nat 1637%nat else 1%Z) * ((if zz_in_Pn 1024 1638%nat then Z.of_nat 1638%nat else 1%Z) * ((if zz_in_Pn 1024 1639%nat then Z.of_nat 1639%nat else 1%Z) * ((if zz_in_Pn 1024 1640%nat then Z.of_nat 1640%nat else 1%Z) * ((if zz_in_Pn 1024 1641%nat then Z.of_nat 1641%nat else 1%Z) * ((if zz_in_Pn 1024 1642%nat then Z.of_nat 1642%nat else 1%Z) * ((if zz_in_Pn 1024 1643%nat then Z.of_nat 1643%nat else 1%Z) * ((if zz_in_Pn 1024 1644%nat then Z.of_nat 1644%nat else 1%Z) * ((if zz_in_Pn 1024 1645%nat then Z.of_nat 1645%nat else 1%Z) * ((if zz_in_Pn 1024 1646%nat then Z.of_nat 1646%nat else 1%Z) * ((if zz_in_Pn 1024 1647%nat then Z.of_nat 1647%nat else 1%Z) * (if zz_in_Pn 1024 1648%nat then Z.of_nat 1648%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1648.
    rewrite piu_zz_inPn_1024_1647.
    rewrite piu_zz_inPn_1024_1646.
    rewrite piu_zz_inPn_1024_1645.
    rewrite piu_zz_inPn_1024_1644.
    rewrite piu_zz_inPn_1024_1643.
    rewrite piu_zz_inPn_1024_1642.
    rewrite piu_zz_inPn_1024_1641.
    rewrite piu_zz_inPn_1024_1640.
    rewrite piu_zz_inPn_1024_1639.
    rewrite piu_zz_inPn_1024_1638.
    rewrite piu_zz_inPn_1024_1637.
    rewrite piu_zz_inPn_1024_1636.
    rewrite piu_zz_inPn_1024_1635.
    rewrite piu_zz_inPn_1024_1634.
    rewrite piu_zz_inPn_1024_1633.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1565-L1585 (assert Hb26) *)
Lemma piu_zz_hb_1024_26 : piu_zz_zprod_seg 1024%nat (512%nat + 1104%nat) 16%nat = ((if zz_in_Pn 1024 1617%nat then Z.of_nat 1617%nat else 1%Z) * ((if zz_in_Pn 1024 1618%nat then Z.of_nat 1618%nat else 1%Z) * ((if zz_in_Pn 1024 1619%nat then Z.of_nat 1619%nat else 1%Z) * ((if zz_in_Pn 1024 1620%nat then Z.of_nat 1620%nat else 1%Z) * ((if zz_in_Pn 1024 1621%nat then Z.of_nat 1621%nat else 1%Z) * ((if zz_in_Pn 1024 1622%nat then Z.of_nat 1622%nat else 1%Z) * ((if zz_in_Pn 1024 1623%nat then Z.of_nat 1623%nat else 1%Z) * ((if zz_in_Pn 1024 1624%nat then Z.of_nat 1624%nat else 1%Z) * ((if zz_in_Pn 1024 1625%nat then Z.of_nat 1625%nat else 1%Z) * ((if zz_in_Pn 1024 1626%nat then Z.of_nat 1626%nat else 1%Z) * ((if zz_in_Pn 1024 1627%nat then Z.of_nat 1627%nat else 1%Z) * ((if zz_in_Pn 1024 1628%nat then Z.of_nat 1628%nat else 1%Z) * ((if zz_in_Pn 1024 1629%nat then Z.of_nat 1629%nat else 1%Z) * ((if zz_in_Pn 1024 1630%nat then Z.of_nat 1630%nat else 1%Z) * ((if zz_in_Pn 1024 1631%nat then Z.of_nat 1631%nat else 1%Z) * (if zz_in_Pn 1024 1632%nat then Z.of_nat 1632%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1632.
    rewrite piu_zz_inPn_1024_1631.
    rewrite piu_zz_inPn_1024_1630.
    rewrite piu_zz_inPn_1024_1629.
    rewrite piu_zz_inPn_1024_1628.
    rewrite piu_zz_inPn_1024_1627.
    rewrite piu_zz_inPn_1024_1626.
    rewrite piu_zz_inPn_1024_1625.
    rewrite piu_zz_inPn_1024_1624.
    rewrite piu_zz_inPn_1024_1623.
    rewrite piu_zz_inPn_1024_1622.
    rewrite piu_zz_inPn_1024_1621.
    rewrite piu_zz_inPn_1024_1620.
    rewrite piu_zz_inPn_1024_1619.
    rewrite piu_zz_inPn_1024_1618.
    rewrite piu_zz_inPn_1024_1617.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1586-L1606 (assert Hb27) *)
Lemma piu_zz_hb_1024_27 : piu_zz_zprod_seg 1024%nat (512%nat + 1088%nat) 16%nat = ((if zz_in_Pn 1024 1601%nat then Z.of_nat 1601%nat else 1%Z) * ((if zz_in_Pn 1024 1602%nat then Z.of_nat 1602%nat else 1%Z) * ((if zz_in_Pn 1024 1603%nat then Z.of_nat 1603%nat else 1%Z) * ((if zz_in_Pn 1024 1604%nat then Z.of_nat 1604%nat else 1%Z) * ((if zz_in_Pn 1024 1605%nat then Z.of_nat 1605%nat else 1%Z) * ((if zz_in_Pn 1024 1606%nat then Z.of_nat 1606%nat else 1%Z) * ((if zz_in_Pn 1024 1607%nat then Z.of_nat 1607%nat else 1%Z) * ((if zz_in_Pn 1024 1608%nat then Z.of_nat 1608%nat else 1%Z) * ((if zz_in_Pn 1024 1609%nat then Z.of_nat 1609%nat else 1%Z) * ((if zz_in_Pn 1024 1610%nat then Z.of_nat 1610%nat else 1%Z) * ((if zz_in_Pn 1024 1611%nat then Z.of_nat 1611%nat else 1%Z) * ((if zz_in_Pn 1024 1612%nat then Z.of_nat 1612%nat else 1%Z) * ((if zz_in_Pn 1024 1613%nat then Z.of_nat 1613%nat else 1%Z) * ((if zz_in_Pn 1024 1614%nat then Z.of_nat 1614%nat else 1%Z) * ((if zz_in_Pn 1024 1615%nat then Z.of_nat 1615%nat else 1%Z) * (if zz_in_Pn 1024 1616%nat then Z.of_nat 1616%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1616.
    rewrite piu_zz_inPn_1024_1615.
    rewrite piu_zz_inPn_1024_1614.
    rewrite piu_zz_inPn_1024_1613.
    rewrite piu_zz_inPn_1024_1612.
    rewrite piu_zz_inPn_1024_1611.
    rewrite piu_zz_inPn_1024_1610.
    rewrite piu_zz_inPn_1024_1609.
    rewrite piu_zz_inPn_1024_1608.
    rewrite piu_zz_inPn_1024_1607.
    rewrite piu_zz_inPn_1024_1606.
    rewrite piu_zz_inPn_1024_1605.
    rewrite piu_zz_inPn_1024_1604.
    rewrite piu_zz_inPn_1024_1603.
    rewrite piu_zz_inPn_1024_1602.
    rewrite piu_zz_inPn_1024_1601.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
