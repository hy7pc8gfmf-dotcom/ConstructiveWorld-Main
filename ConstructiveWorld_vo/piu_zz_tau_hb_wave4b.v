(* piu_zz_tau_hb_wave4b.v — KB11 Hb 升格候选子片 4/8（1024 段 Hb16-Hb31·机械升格件·零漂移回读断言已过）。
   [KB20 checkpoint split] 本件=wave4（1024_16..31 重条区）四等分 b/4；引理自 wave4 逐字搬移，语句/体零改写。
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
(* src piu_zz_tau_enclosure.v L1439-L1459 (assert Hb20) *)
Lemma piu_zz_hb_1024_20 : piu_zz_zprod_seg 1024%nat (512%nat + 1200%nat) 16%nat = ((if zz_in_Pn 1024 1713%nat then Z.of_nat 1713%nat else 1%Z) * ((if zz_in_Pn 1024 1714%nat then Z.of_nat 1714%nat else 1%Z) * ((if zz_in_Pn 1024 1715%nat then Z.of_nat 1715%nat else 1%Z) * ((if zz_in_Pn 1024 1716%nat then Z.of_nat 1716%nat else 1%Z) * ((if zz_in_Pn 1024 1717%nat then Z.of_nat 1717%nat else 1%Z) * ((if zz_in_Pn 1024 1718%nat then Z.of_nat 1718%nat else 1%Z) * ((if zz_in_Pn 1024 1719%nat then Z.of_nat 1719%nat else 1%Z) * ((if zz_in_Pn 1024 1720%nat then Z.of_nat 1720%nat else 1%Z) * ((if zz_in_Pn 1024 1721%nat then Z.of_nat 1721%nat else 1%Z) * ((if zz_in_Pn 1024 1722%nat then Z.of_nat 1722%nat else 1%Z) * ((if zz_in_Pn 1024 1723%nat then Z.of_nat 1723%nat else 1%Z) * ((if zz_in_Pn 1024 1724%nat then Z.of_nat 1724%nat else 1%Z) * ((if zz_in_Pn 1024 1725%nat then Z.of_nat 1725%nat else 1%Z) * ((if zz_in_Pn 1024 1726%nat then Z.of_nat 1726%nat else 1%Z) * ((if zz_in_Pn 1024 1727%nat then Z.of_nat 1727%nat else 1%Z) * (if zz_in_Pn 1024 1728%nat then Z.of_nat 1728%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1728.
    rewrite piu_zz_inPn_1024_1727.
    rewrite piu_zz_inPn_1024_1726.
    rewrite piu_zz_inPn_1024_1725.
    rewrite piu_zz_inPn_1024_1724.
    rewrite piu_zz_inPn_1024_1723.
    rewrite piu_zz_inPn_1024_1722.
    rewrite piu_zz_inPn_1024_1721.
    rewrite piu_zz_inPn_1024_1720.
    rewrite piu_zz_inPn_1024_1719.
    rewrite piu_zz_inPn_1024_1718.
    rewrite piu_zz_inPn_1024_1717.
    rewrite piu_zz_inPn_1024_1716.
    rewrite piu_zz_inPn_1024_1715.
    rewrite piu_zz_inPn_1024_1714.
    rewrite piu_zz_inPn_1024_1713.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1460-L1480 (assert Hb21) *)
Lemma piu_zz_hb_1024_21 : piu_zz_zprod_seg 1024%nat (512%nat + 1184%nat) 16%nat = ((if zz_in_Pn 1024 1697%nat then Z.of_nat 1697%nat else 1%Z) * ((if zz_in_Pn 1024 1698%nat then Z.of_nat 1698%nat else 1%Z) * ((if zz_in_Pn 1024 1699%nat then Z.of_nat 1699%nat else 1%Z) * ((if zz_in_Pn 1024 1700%nat then Z.of_nat 1700%nat else 1%Z) * ((if zz_in_Pn 1024 1701%nat then Z.of_nat 1701%nat else 1%Z) * ((if zz_in_Pn 1024 1702%nat then Z.of_nat 1702%nat else 1%Z) * ((if zz_in_Pn 1024 1703%nat then Z.of_nat 1703%nat else 1%Z) * ((if zz_in_Pn 1024 1704%nat then Z.of_nat 1704%nat else 1%Z) * ((if zz_in_Pn 1024 1705%nat then Z.of_nat 1705%nat else 1%Z) * ((if zz_in_Pn 1024 1706%nat then Z.of_nat 1706%nat else 1%Z) * ((if zz_in_Pn 1024 1707%nat then Z.of_nat 1707%nat else 1%Z) * ((if zz_in_Pn 1024 1708%nat then Z.of_nat 1708%nat else 1%Z) * ((if zz_in_Pn 1024 1709%nat then Z.of_nat 1709%nat else 1%Z) * ((if zz_in_Pn 1024 1710%nat then Z.of_nat 1710%nat else 1%Z) * ((if zz_in_Pn 1024 1711%nat then Z.of_nat 1711%nat else 1%Z) * (if zz_in_Pn 1024 1712%nat then Z.of_nat 1712%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1712.
    rewrite piu_zz_inPn_1024_1711.
    rewrite piu_zz_inPn_1024_1710.
    rewrite piu_zz_inPn_1024_1709.
    rewrite piu_zz_inPn_1024_1708.
    rewrite piu_zz_inPn_1024_1707.
    rewrite piu_zz_inPn_1024_1706.
    rewrite piu_zz_inPn_1024_1705.
    rewrite piu_zz_inPn_1024_1704.
    rewrite piu_zz_inPn_1024_1703.
    rewrite piu_zz_inPn_1024_1702.
    rewrite piu_zz_inPn_1024_1701.
    rewrite piu_zz_inPn_1024_1700.
    rewrite piu_zz_inPn_1024_1699.
    rewrite piu_zz_inPn_1024_1698.
    rewrite piu_zz_inPn_1024_1697.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1481-L1501 (assert Hb22) *)
Lemma piu_zz_hb_1024_22 : piu_zz_zprod_seg 1024%nat (512%nat + 1168%nat) 16%nat = ((if zz_in_Pn 1024 1681%nat then Z.of_nat 1681%nat else 1%Z) * ((if zz_in_Pn 1024 1682%nat then Z.of_nat 1682%nat else 1%Z) * ((if zz_in_Pn 1024 1683%nat then Z.of_nat 1683%nat else 1%Z) * ((if zz_in_Pn 1024 1684%nat then Z.of_nat 1684%nat else 1%Z) * ((if zz_in_Pn 1024 1685%nat then Z.of_nat 1685%nat else 1%Z) * ((if zz_in_Pn 1024 1686%nat then Z.of_nat 1686%nat else 1%Z) * ((if zz_in_Pn 1024 1687%nat then Z.of_nat 1687%nat else 1%Z) * ((if zz_in_Pn 1024 1688%nat then Z.of_nat 1688%nat else 1%Z) * ((if zz_in_Pn 1024 1689%nat then Z.of_nat 1689%nat else 1%Z) * ((if zz_in_Pn 1024 1690%nat then Z.of_nat 1690%nat else 1%Z) * ((if zz_in_Pn 1024 1691%nat then Z.of_nat 1691%nat else 1%Z) * ((if zz_in_Pn 1024 1692%nat then Z.of_nat 1692%nat else 1%Z) * ((if zz_in_Pn 1024 1693%nat then Z.of_nat 1693%nat else 1%Z) * ((if zz_in_Pn 1024 1694%nat then Z.of_nat 1694%nat else 1%Z) * ((if zz_in_Pn 1024 1695%nat then Z.of_nat 1695%nat else 1%Z) * (if zz_in_Pn 1024 1696%nat then Z.of_nat 1696%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1696.
    rewrite piu_zz_inPn_1024_1695.
    rewrite piu_zz_inPn_1024_1694.
    rewrite piu_zz_inPn_1024_1693.
    rewrite piu_zz_inPn_1024_1692.
    rewrite piu_zz_inPn_1024_1691.
    rewrite piu_zz_inPn_1024_1690.
    rewrite piu_zz_inPn_1024_1689.
    rewrite piu_zz_inPn_1024_1688.
    rewrite piu_zz_inPn_1024_1687.
    rewrite piu_zz_inPn_1024_1686.
    rewrite piu_zz_inPn_1024_1685.
    rewrite piu_zz_inPn_1024_1684.
    rewrite piu_zz_inPn_1024_1683.
    rewrite piu_zz_inPn_1024_1682.
    rewrite piu_zz_inPn_1024_1681.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1502-L1522 (assert Hb23) *)
Lemma piu_zz_hb_1024_23 : piu_zz_zprod_seg 1024%nat (512%nat + 1152%nat) 16%nat = ((if zz_in_Pn 1024 1665%nat then Z.of_nat 1665%nat else 1%Z) * ((if zz_in_Pn 1024 1666%nat then Z.of_nat 1666%nat else 1%Z) * ((if zz_in_Pn 1024 1667%nat then Z.of_nat 1667%nat else 1%Z) * ((if zz_in_Pn 1024 1668%nat then Z.of_nat 1668%nat else 1%Z) * ((if zz_in_Pn 1024 1669%nat then Z.of_nat 1669%nat else 1%Z) * ((if zz_in_Pn 1024 1670%nat then Z.of_nat 1670%nat else 1%Z) * ((if zz_in_Pn 1024 1671%nat then Z.of_nat 1671%nat else 1%Z) * ((if zz_in_Pn 1024 1672%nat then Z.of_nat 1672%nat else 1%Z) * ((if zz_in_Pn 1024 1673%nat then Z.of_nat 1673%nat else 1%Z) * ((if zz_in_Pn 1024 1674%nat then Z.of_nat 1674%nat else 1%Z) * ((if zz_in_Pn 1024 1675%nat then Z.of_nat 1675%nat else 1%Z) * ((if zz_in_Pn 1024 1676%nat then Z.of_nat 1676%nat else 1%Z) * ((if zz_in_Pn 1024 1677%nat then Z.of_nat 1677%nat else 1%Z) * ((if zz_in_Pn 1024 1678%nat then Z.of_nat 1678%nat else 1%Z) * ((if zz_in_Pn 1024 1679%nat then Z.of_nat 1679%nat else 1%Z) * (if zz_in_Pn 1024 1680%nat then Z.of_nat 1680%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1680.
    rewrite piu_zz_inPn_1024_1679.
    rewrite piu_zz_inPn_1024_1678.
    rewrite piu_zz_inPn_1024_1677.
    rewrite piu_zz_inPn_1024_1676.
    rewrite piu_zz_inPn_1024_1675.
    rewrite piu_zz_inPn_1024_1674.
    rewrite piu_zz_inPn_1024_1673.
    rewrite piu_zz_inPn_1024_1672.
    rewrite piu_zz_inPn_1024_1671.
    rewrite piu_zz_inPn_1024_1670.
    rewrite piu_zz_inPn_1024_1669.
    rewrite piu_zz_inPn_1024_1668.
    rewrite piu_zz_inPn_1024_1667.
    rewrite piu_zz_inPn_1024_1666.
    rewrite piu_zz_inPn_1024_1665.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
