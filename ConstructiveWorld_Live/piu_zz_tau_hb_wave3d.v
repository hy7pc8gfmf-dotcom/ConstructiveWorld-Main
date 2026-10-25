(* piu_zz_tau_hb_wave3d.v — KB11 Hb 升格候选子片 3/8（1024 段 Hb0-Hb15·机械升格件·零漂移回读断言已过）。
   [KB12 adaptive resplit] 本件=wave3（1024_0..15 重条区）四等分 d/4；引理自 wave3 逐字搬移，语句/体零改写。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave3.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.
(* src piu_zz_tau_enclosure.v L1271-L1291 (assert Hb12) *)
Lemma piu_zz_hb_1024_12 : piu_zz_zprod_seg 1024%nat (512%nat + 1328%nat) 16%nat = ((if zz_in_Pn 1024 1841%nat then Z.of_nat 1841%nat else 1%Z) * ((if zz_in_Pn 1024 1842%nat then Z.of_nat 1842%nat else 1%Z) * ((if zz_in_Pn 1024 1843%nat then Z.of_nat 1843%nat else 1%Z) * ((if zz_in_Pn 1024 1844%nat then Z.of_nat 1844%nat else 1%Z) * ((if zz_in_Pn 1024 1845%nat then Z.of_nat 1845%nat else 1%Z) * ((if zz_in_Pn 1024 1846%nat then Z.of_nat 1846%nat else 1%Z) * ((if zz_in_Pn 1024 1847%nat then Z.of_nat 1847%nat else 1%Z) * ((if zz_in_Pn 1024 1848%nat then Z.of_nat 1848%nat else 1%Z) * ((if zz_in_Pn 1024 1849%nat then Z.of_nat 1849%nat else 1%Z) * ((if zz_in_Pn 1024 1850%nat then Z.of_nat 1850%nat else 1%Z) * ((if zz_in_Pn 1024 1851%nat then Z.of_nat 1851%nat else 1%Z) * ((if zz_in_Pn 1024 1852%nat then Z.of_nat 1852%nat else 1%Z) * ((if zz_in_Pn 1024 1853%nat then Z.of_nat 1853%nat else 1%Z) * ((if zz_in_Pn 1024 1854%nat then Z.of_nat 1854%nat else 1%Z) * ((if zz_in_Pn 1024 1855%nat then Z.of_nat 1855%nat else 1%Z) * (if zz_in_Pn 1024 1856%nat then Z.of_nat 1856%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1856.
    rewrite piu_zz_inPn_1024_1855.
    rewrite piu_zz_inPn_1024_1854.
    rewrite piu_zz_inPn_1024_1853.
    rewrite piu_zz_inPn_1024_1852.
    rewrite piu_zz_inPn_1024_1851.
    rewrite piu_zz_inPn_1024_1850.
    rewrite piu_zz_inPn_1024_1849.
    rewrite piu_zz_inPn_1024_1848.
    rewrite piu_zz_inPn_1024_1847.
    rewrite piu_zz_inPn_1024_1846.
    rewrite piu_zz_inPn_1024_1845.
    rewrite piu_zz_inPn_1024_1844.
    rewrite piu_zz_inPn_1024_1843.
    rewrite piu_zz_inPn_1024_1842.
    rewrite piu_zz_inPn_1024_1841.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1292-L1312 (assert Hb13) *)
Lemma piu_zz_hb_1024_13 : piu_zz_zprod_seg 1024%nat (512%nat + 1312%nat) 16%nat = ((if zz_in_Pn 1024 1825%nat then Z.of_nat 1825%nat else 1%Z) * ((if zz_in_Pn 1024 1826%nat then Z.of_nat 1826%nat else 1%Z) * ((if zz_in_Pn 1024 1827%nat then Z.of_nat 1827%nat else 1%Z) * ((if zz_in_Pn 1024 1828%nat then Z.of_nat 1828%nat else 1%Z) * ((if zz_in_Pn 1024 1829%nat then Z.of_nat 1829%nat else 1%Z) * ((if zz_in_Pn 1024 1830%nat then Z.of_nat 1830%nat else 1%Z) * ((if zz_in_Pn 1024 1831%nat then Z.of_nat 1831%nat else 1%Z) * ((if zz_in_Pn 1024 1832%nat then Z.of_nat 1832%nat else 1%Z) * ((if zz_in_Pn 1024 1833%nat then Z.of_nat 1833%nat else 1%Z) * ((if zz_in_Pn 1024 1834%nat then Z.of_nat 1834%nat else 1%Z) * ((if zz_in_Pn 1024 1835%nat then Z.of_nat 1835%nat else 1%Z) * ((if zz_in_Pn 1024 1836%nat then Z.of_nat 1836%nat else 1%Z) * ((if zz_in_Pn 1024 1837%nat then Z.of_nat 1837%nat else 1%Z) * ((if zz_in_Pn 1024 1838%nat then Z.of_nat 1838%nat else 1%Z) * ((if zz_in_Pn 1024 1839%nat then Z.of_nat 1839%nat else 1%Z) * (if zz_in_Pn 1024 1840%nat then Z.of_nat 1840%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1840.
    rewrite piu_zz_inPn_1024_1839.
    rewrite piu_zz_inPn_1024_1838.
    rewrite piu_zz_inPn_1024_1837.
    rewrite piu_zz_inPn_1024_1836.
    rewrite piu_zz_inPn_1024_1835.
    rewrite piu_zz_inPn_1024_1834.
    rewrite piu_zz_inPn_1024_1833.
    rewrite piu_zz_inPn_1024_1832.
    rewrite piu_zz_inPn_1024_1831.
    rewrite piu_zz_inPn_1024_1830.
    rewrite piu_zz_inPn_1024_1829.
    rewrite piu_zz_inPn_1024_1828.
    rewrite piu_zz_inPn_1024_1827.
    rewrite piu_zz_inPn_1024_1826.
    rewrite piu_zz_inPn_1024_1825.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1313-L1333 (assert Hb14) *)
Lemma piu_zz_hb_1024_14 : piu_zz_zprod_seg 1024%nat (512%nat + 1296%nat) 16%nat = ((if zz_in_Pn 1024 1809%nat then Z.of_nat 1809%nat else 1%Z) * ((if zz_in_Pn 1024 1810%nat then Z.of_nat 1810%nat else 1%Z) * ((if zz_in_Pn 1024 1811%nat then Z.of_nat 1811%nat else 1%Z) * ((if zz_in_Pn 1024 1812%nat then Z.of_nat 1812%nat else 1%Z) * ((if zz_in_Pn 1024 1813%nat then Z.of_nat 1813%nat else 1%Z) * ((if zz_in_Pn 1024 1814%nat then Z.of_nat 1814%nat else 1%Z) * ((if zz_in_Pn 1024 1815%nat then Z.of_nat 1815%nat else 1%Z) * ((if zz_in_Pn 1024 1816%nat then Z.of_nat 1816%nat else 1%Z) * ((if zz_in_Pn 1024 1817%nat then Z.of_nat 1817%nat else 1%Z) * ((if zz_in_Pn 1024 1818%nat then Z.of_nat 1818%nat else 1%Z) * ((if zz_in_Pn 1024 1819%nat then Z.of_nat 1819%nat else 1%Z) * ((if zz_in_Pn 1024 1820%nat then Z.of_nat 1820%nat else 1%Z) * ((if zz_in_Pn 1024 1821%nat then Z.of_nat 1821%nat else 1%Z) * ((if zz_in_Pn 1024 1822%nat then Z.of_nat 1822%nat else 1%Z) * ((if zz_in_Pn 1024 1823%nat then Z.of_nat 1823%nat else 1%Z) * (if zz_in_Pn 1024 1824%nat then Z.of_nat 1824%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1824.
    rewrite piu_zz_inPn_1024_1823.
    rewrite piu_zz_inPn_1024_1822.
    rewrite piu_zz_inPn_1024_1821.
    rewrite piu_zz_inPn_1024_1820.
    rewrite piu_zz_inPn_1024_1819.
    rewrite piu_zz_inPn_1024_1818.
    rewrite piu_zz_inPn_1024_1817.
    rewrite piu_zz_inPn_1024_1816.
    rewrite piu_zz_inPn_1024_1815.
    rewrite piu_zz_inPn_1024_1814.
    rewrite piu_zz_inPn_1024_1813.
    rewrite piu_zz_inPn_1024_1812.
    rewrite piu_zz_inPn_1024_1811.
    rewrite piu_zz_inPn_1024_1810.
    rewrite piu_zz_inPn_1024_1809.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L1334-L1354 (assert Hb15) *)
Lemma piu_zz_hb_1024_15 : piu_zz_zprod_seg 1024%nat (512%nat + 1280%nat) 16%nat = ((if zz_in_Pn 1024 1793%nat then Z.of_nat 1793%nat else 1%Z) * ((if zz_in_Pn 1024 1794%nat then Z.of_nat 1794%nat else 1%Z) * ((if zz_in_Pn 1024 1795%nat then Z.of_nat 1795%nat else 1%Z) * ((if zz_in_Pn 1024 1796%nat then Z.of_nat 1796%nat else 1%Z) * ((if zz_in_Pn 1024 1797%nat then Z.of_nat 1797%nat else 1%Z) * ((if zz_in_Pn 1024 1798%nat then Z.of_nat 1798%nat else 1%Z) * ((if zz_in_Pn 1024 1799%nat then Z.of_nat 1799%nat else 1%Z) * ((if zz_in_Pn 1024 1800%nat then Z.of_nat 1800%nat else 1%Z) * ((if zz_in_Pn 1024 1801%nat then Z.of_nat 1801%nat else 1%Z) * ((if zz_in_Pn 1024 1802%nat then Z.of_nat 1802%nat else 1%Z) * ((if zz_in_Pn 1024 1803%nat then Z.of_nat 1803%nat else 1%Z) * ((if zz_in_Pn 1024 1804%nat then Z.of_nat 1804%nat else 1%Z) * ((if zz_in_Pn 1024 1805%nat then Z.of_nat 1805%nat else 1%Z) * ((if zz_in_Pn 1024 1806%nat then Z.of_nat 1806%nat else 1%Z) * ((if zz_in_Pn 1024 1807%nat then Z.of_nat 1807%nat else 1%Z) * (if zz_in_Pn 1024 1808%nat then Z.of_nat 1808%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_1024_1808.
    rewrite piu_zz_inPn_1024_1807.
    rewrite piu_zz_inPn_1024_1806.
    rewrite piu_zz_inPn_1024_1805.
    rewrite piu_zz_inPn_1024_1804.
    rewrite piu_zz_inPn_1024_1803.
    rewrite piu_zz_inPn_1024_1802.
    rewrite piu_zz_inPn_1024_1801.
    rewrite piu_zz_inPn_1024_1800.
    rewrite piu_zz_inPn_1024_1799.
    rewrite piu_zz_inPn_1024_1798.
    rewrite piu_zz_inPn_1024_1797.
    rewrite piu_zz_inPn_1024_1796.
    rewrite piu_zz_inPn_1024_1795.
    rewrite piu_zz_inPn_1024_1794.
    rewrite piu_zz_inPn_1024_1793.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
